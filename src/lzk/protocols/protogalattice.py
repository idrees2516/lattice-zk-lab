"""ProtogaLattice: lattice-based algebraic folding (lab item 7.4, P0-1..P0-5).

Paper: "ProtogaLattice" (Balbás, Nitulescu, Plançon).  This module
implements the algebraic folding core:

* **The relaxed accumulator relation** (lab model of Ξ^acc): instance
  (t, x, beta, e) with witness w, commitment t = A w, and the constraint
      sum_i beta_i * f_i(w) = e  (mod q)
  where f = (f_1..f_n) is a degree-d polynomial map R_q^m -> R_q^n and
  beta = (beta_1..beta_n) is the public power-vector.  ||w||_2 <= gamma.

* **PGL-Fold (Figure 2)**: folds one accumulator with k fresh instances:
      delta <- challenge,  delta-vec = (delta, delta^2, ..., delta^n)
      F(X)  = sum_i (beta_i + X delta^i) f_i(w_0)          [affine in X]
      alpha <- challenge,  beta*_i = beta_i + alpha delta^i
      H(Y)  = sum_i beta*_i f_i( sum_j L_j(Y) w_j )        [degree d in Y]
      H(Y) - F(alpha) = sum_{r<=s} K_{rs}(Y) Z_{rs}(Y)     [Groebner division]
      y <- C^k,  w* = sum_j L_j(y) w_j,  t*/x* likewise,
      e* = sum K_{rs}(y) Z_{rs}(y) + F(alpha)
  Theorem 1 guarantees H(Y) - F(alpha) lies in the ideal I, so the K_{rs}
  exist with deg <= d-2 (Proposition 1's reduced Groebner basis).

* **PGL-Boot (Figure 3)**: the norm-bootstrapping reduction — decompose the
  accumulator witness in base b (w = sum_j b^j w_j with small digits),
  per-digit errors e_j = sum_i beta_i f_i(w_j), the SAME Groebder reduction
  H(Y) = sum_j L_j(Y) e_j + sum Z K, the verifier's checks
  sum b^j t_j = t and sum b^j e_j = e + sum Z(D) K(D) with L_j(D) = b^j,
  then the fold at fresh challenges re-anchors the norm to gamma.

The e*-check-style error bookkeeping (the relaxed-witness linearisation) is
exactly the paper's: the error accumulator absorbs both the F(alpha) drift
and the ideal-reduction residue evaluated at the challenges.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, List, Sequence, Tuple

from ..core.ring import Ring, RingElt
from ..core.transcript import Transcript
from ..core.commitment import AjtaiParams
from ..core.groebner import (
    MPoly,
    divide,
    verify_division,
    quotient_degree_bound_ok,
    l_basis,
    l_eval,
    z_eval,
)

# --------------------------------------------------------------------------- #
#  The polynomial map f (degree d) — lab instances use quadratic maps
# --------------------------------------------------------------------------- #


@dataclass
class PolyMap:
    """f: R_q^m -> R_q^n, f_i(w) = <M_i, w> + <w, N_i w> (degree <= 2)."""

    M: List[List[RingElt]]           # n x m linear part
    N: List[List[List[RingElt]]]     # n x m x m quadratic part
    ring: Ring

    @classmethod
    def random_quadratic(
        cls, ring: Ring, m: int, n: int, rng, small: bool = True, scalar: bool = False
    ) -> "PolyMap":
        """Random degree-<=2 map.  scalar=True draws Z_q-scalar entries
        (constant-coefficient ring elements) so the ring evaluation and the
        MPoly (Groebner) evaluation agree exactly — the lab's default for
        PGL (full ring-element entries need a module-valued MPoly, see the
        gap ledger)."""
        cr = 2 if small else None
        if scalar:
            M = [[ring.from_int(rng.randrange(1, 4)) for _ in range(m)] for _ in range(n)]
            N = [
                [[ring.from_int(rng.randrange(0, 3)) for _ in range(m)] for _ in range(m)]
                for _ in range(n)
            ]
            return cls(M=M, N=N, ring=ring)
        M = [[ring.random(rng, coeffs_range=cr) for _ in range(m)] for _ in range(n)]
        N = [
            [[ring.random(rng, coeffs_range=cr) for _ in range(m)] for _ in range(m)]
            for _ in range(n)
        ]
        return cls(M=M, N=N, ring=ring)

    def eval(self, w: Sequence[RingElt]) -> List[RingElt]:
        ring = self.ring
        out = []
        for i in range(len(self.M)):
            acc = ring.zero()
            for a, x in zip(self.M[i], w):
                acc = acc + a * x
            for r in range(len(w)):
                for c in range(len(w)):
                    if not self.N[i][r][c].is_zero():
                        acc = acc + self.N[i][r][c] * (w[r] * w[c])
            out.append(acc)
        return out

    def eval_mpoly(self, w_mpoly: Sequence[MPoly]) -> List[MPoly]:
        """f evaluated with MPoly-valued witness (for H(Y) construction)."""
        q = self.ring.q
        nvars = w_mpoly[0].nvars
        out = []
        for i in range(len(self.M)):
            acc = MPoly.const(0, q, nvars)
            for a, x in zip(self.M[i], w_mpoly):
                acc = acc + x * _ring_elt_to_int(a, self.ring)
            for r in range(len(w_mpoly)):
                for c in range(len(w_mpoly)):
                    nr = _ring_elt_to_int(self.N[i][r][c], self.ring)
                    if nr:
                        acc = acc + (w_mpoly[r] * w_mpoly[c]) * nr
            out.append(acc)
        return out


def _ring_elt_to_int(a: RingElt, ring: Ring) -> int:
    """Lift a ring element to the MPoly coefficient field by its constant
    coefficient (the lab's f-components use scalar coefficients: the M/N
    entries are drawn from the base field Z_q embedded as constants)."""
    return a.coeffs[0] % ring.q


# --------------------------------------------------------------------------- #
#  The accumulator relation instances
# --------------------------------------------------------------------------- #


@dataclass
class Accumulator:
    t: List[RingElt]          # commitment A . w
    x: List[RingElt]          # public instance vector (lab: informational)
    beta: List[int]           # the power-vector (beta_1..beta_n)
    e: RingElt                # error accumulator
    w: List[RingElt] | None = None   # witness (prover side)
    gamma: int = 0            # norm bound


@dataclass
class FoldInstance:
    t: List[RingElt]
    x: List[RingElt]
    w: List[RingElt] | None = None


class PGL:
    """ProtogaLattice driver: holds (ring, f, commitment key, k, base b)."""

    def __init__(
        self,
        ring: Ring,
        f: PolyMap,
        k: int = 2,
        seed: bytes = b"pgl-seed",
    ):
        self.ring = ring
        self.f = f
        self.k = k
        self.m = len(f.M[0]) if f.M else 0
        self.n = len(f.M)
        self.com_key = AjtaiParams(ring, 2, self.m, seed=seed)

    # ------------------------------------------------------------ helpers #
    def commit(self, w: Sequence[RingElt]) -> List[RingElt]:
        return self.com_key.commit(list(w))

    def power_constraint(self, w: Sequence[RingElt], beta: Sequence[int]) -> RingElt:
        """sum_i beta_i f_i(w)."""
        fvals = self.f.eval(w)
        acc = self.ring.zero()
        for b_i, fv in zip(beta, fvals):
            acc = acc + fv * b_i
        return acc

    def fresh_accumulator(self, w: Sequence[RingElt], beta: Sequence[int], rng) -> Accumulator:
        """An accumulator with e = sum beta_i f_i(w) (the honest initial
        relaxation: fresh witnesses satisfy the unrelaxed relation e = 0
        when f(w) = 0; the lab seeds e from the actual value)."""
        t = self.commit(w)
        e = self.power_constraint(w, beta)
        x = [self.ring.random(rng) for _ in range(2)]
        gamma = int(sum(x.l2_sq_int() for x in w) ** 0.5) + 1
        return Accumulator(t=t, x=x, beta=list(beta), e=e, w=list(w), gamma=gamma)

    # -------------------------------------------------------- PGL-Fold #
    def fold_prove(
        self,
        acc: Accumulator,
        instances: Sequence[FoldInstance],
        transcript: Transcript,
    ) -> Tuple[Accumulator, "FoldProof"]:
        """PGL-Fold (Figure 2).  Returns (new accumulator, proof)."""
        ring = self.ring
        q = ring.q
        k = self.k
        nvars = k  # variables Y_0..Y_{k-1}; Y_k := 1
        n = self.n
        ws = [acc.w] + [inst.w for inst in instances]
        # ---- delta and the delta-vector
        transcript.absorb_bytes(b"pgl:fold:start")
        for c in acc.t:
            transcript.absorb_ring(c)
        for inst in instances:
            for c in inst.t:
                transcript.absorb_ring(c)
        delta = ring.challenge_small(transcript, label="pgl:delta")
        delta_vec = [pow(delta.coeffs[0], i, q) for i in range(1, n + 1)]
        # ---- F(X) = sum_i (beta_i + X delta^i) f_i(w_0): affine in X
        f0 = self.f.eval(ws[0])
        F_const = sum((b * fv for b, fv in zip(acc.beta, f0)), start=ring.zero())
        F_lin = sum((d * fv for d, fv in zip(delta_vec, f0)), start=ring.zero())
        # prover sends the two coefficients (F_1, F_2 in the paper's t-slot
        # counting; the lab sends (F_const, F_lin))
        transcript.absorb_ring(F_const)
        transcript.absorb_ring(F_lin)
        alpha = ring.challenge_small(transcript, label="pgl:alpha")
        # ---- beta*_i = beta_i + alpha delta^i
        beta_star = [(b + alpha.coeffs[0] * d) % q for b, d in zip(acc.beta, delta_vec)]
        # ---- H(Y) = sum_i beta*_i f_i(sum_j L_j(Y) w_j)
        Ls = [l_basis(j, k, q) for j in range(k + 1)]
        w_comb = [
            sum((Ls[j] * _scalar(ring, wj[coord], nvars) for j, wj in enumerate(ws)),
                start=MPoly.const(0, q, nvars))
            for coord in range(self.m)
        ]
        H_terms = self.f.eval_mpoly(w_comb)
        H = MPoly.const(0, q, nvars)
        for b_i, hterm in zip(beta_star, H_terms):
            H = H + hterm * (b_i % q)
        # ---- F(alpha) = F_const + alpha F_lin
        F_alpha = F_const + F_lin * alpha
        F_alpha_int = F_alpha.coeffs[0] % q
        # ---- Groebner division: H(Y) - F(alpha) = sum K Z
        target = H - MPoly.const(F_alpha_int, q, nvars)
        K, R = divide(target)
        # completeness audit: R must vanish when the inputs are consistent
        # (Theorem 1: the deviation lies in I; R is the unique normal form)
        if not R.is_zero():
            # the remainder absorbs into the error bookkeeping — the paper's
            # relation guarantees R = 0 for honest inputs; carry it as an
            # assertion for the lab
            raise AssertionError("Groebner remainder nonzero (honest-input bug)")
        # ---- send K; verifier checks degrees; fold at fresh challenges
        transcript.absorb_bytes(b"pgl:fold:K")
        for (i, j), Kij in sorted(K.items()):
            for m, c in sorted(Kij.terms.items()):
                transcript.absorb_int(c, label=f"pgl:K{i}{j}")
        y = [ring.challenge_small(transcript, label=f"pgl:y{i}") for i in range(k)]
        # y_0 := 1 per the protocol (Y_k = 1 telescoping; the challenge set
        # uses y_1..y_{k-1} free, y_0 fixed — lab: resample slot 0 as 1)
        y[0] = ring.challenge_small(transcript, label="pgl:y0fix")
        # ---- updates
        cs = [l_eval(j, k, [c.coeffs[0] for c in y], q) for j in range(k + 1)]
        w_star = [
            sum((ws[j][coord] * c for j, c in enumerate(cs)), start=ring.zero())
            for coord in range(self.m)
        ]
        t_star = [
            sum((([acc.t] + [inst.t for inst in instances])[j][idx] * c
                  for j, c in enumerate(cs)), start=ring.zero())
            for idx in range(len(acc.t))
        ]
        x_star = [
            sum(([acc.x] + [inst.x for inst in instances])[j][idx] * c
                for j, c in enumerate(cs)) for idx in range(len(acc.x))
        ]
        # e* = sum K(y) Z(y) + F(alpha)
        kz = ring.zero()
        for (i, j), Kij in K.items():
            pts = [c.coeffs[0] for c in y]
            kz = kz + ring.from_int(Kij.eval(pts)) * ring.from_int(z_eval(i, j, pts, q))
        e_star = kz + ring.from_int(F_alpha_int)
        gamma_star = int(sum(x.l2_sq_int() for x in w_star) ** 0.5) + 1
        new_acc = Accumulator(t=t_star, x=x_star, beta=beta_star, e=e_star,
                              w=w_star, gamma=gamma_star)
        proof = FoldProof(F_const=F_const, F_lin=F_lin, alpha=alpha, K=K,
                          y=y, delta=delta)
        return new_acc, proof

    def fold_verify(
        self,
        acc: Accumulator,
        instances: Sequence[FoldInstance],
        proof: FoldProof,
        transcript: Transcript,
        degree: int = 2,
    ) -> Tuple[bool, Accumulator]:
        """PGL-Fold verifier (Figure 2 right column)."""
        ring = self.ring
        q = ring.q
        k = self.k
        transcript.absorb_bytes(b"pgl:fold:start")
        for c in acc.t:
            transcript.absorb_ring(c)
        for inst in instances:
            for c in inst.t:
                transcript.absorb_ring(c)
        delta = ring.challenge_small(transcript, label="pgl:delta")
        transcript.absorb_ring(proof.F_const)
        transcript.absorb_ring(proof.F_lin)
        alpha = ring.challenge_small(transcript, label="pgl:alpha")
        if alpha != proof.alpha or delta != proof.delta:
            return False, None
        # degree check on K
        if not quotient_degree_bound_ok(proof.K, degree - 2):
            return False, None
        transcript.absorb_bytes(b"pgl:fold:K")
        for (i, j), Kij in sorted(proof.K.items()):
            for m, c in sorted(Kij.terms.items()):
                transcript.absorb_int(c, label=f"pgl:K{i}{j}")
        y = [ring.challenge_small(transcript, label=f"pgl:y{i}") for i in range(k)]
        y[0] = ring.challenge_small(transcript, label="pgl:y0fix")
        if y != proof.y:
            return False, None
        # recompute the folded statement (both parties)
        cs = [l_eval(j, k, [c.coeffs[0] for c in y], q) for j in range(k + 1)]
        t_star = [
            sum((([acc.t] + [inst.t for inst in instances])[j][idx] * c
                  for j, c in enumerate(cs)), start=ring.zero())
            for idx in range(len(acc.t))
        ]
        x_star = [
            sum(([acc.x] + [inst.x for inst in instances])[j][idx] * c
                for j, c in enumerate(cs)) for idx in range(len(acc.x))
        ]
        delta_vec = [pow(delta.coeffs[0], i, q) for i in range(1, self.n + 1)]
        beta_star = [(b + alpha.coeffs[0] * d) % q for b, d in zip(acc.beta, delta_vec)]
        F_alpha_int = (proof.F_const + proof.F_lin * alpha).coeffs[0] % q
        kz = ring.zero()
        pts = [c.coeffs[0] for c in y]
        for (i, j), Kij in proof.K.items():
            kz = kz + ring.from_int(Kij.eval(pts)) * ring.from_int(z_eval(i, j, pts, q))
        e_star = kz + ring.from_int(F_alpha_int)
        new_acc = Accumulator(t=t_star, x=x_star, beta=beta_star, e=e_star, w=None,
                              gamma=0)
        return True, new_acc

    # -------------------------------------------------------- PGL-Boot #
    def boot_prove(
        self,
        acc: Accumulator,
        base: int,
        k_prime: int,
        transcript: Transcript,
    ) -> Tuple[Accumulator, "BootProof"]:
        """PGL-Boot (Figure 3): decompose w in base b; per-digit errors; the
        Groebner reduction H = sum L_j e_j + sum Z K; verifier checks
        sum b^j t_j = t and sum b^j e_j = e + sum Z(D) K(D)."""
        ring = self.ring
        q = ring.q
        k1 = k_prime
        nvars = k1
        w = acc.w
        # base-b digit witnesses (coefficient-wise over the centred reps)
        digits: List[List[RingElt]] = [[] for _ in range(k1)]
        for elt in w:
            v = ring.center(elt.coeffs[0], q)
            # decompose the CONSTANT coefficient only if the witness is
            # scalar-embedded; the lab uses full ring elements — decompose
            # each coefficient into k1 digits
            remaining = list(elt.coeffs)
            for j in range(k1):
                layer = ring.zero()
                for idx, c in enumerate(remaining):
                    d = ring.center(c, q)
                    layer.coeffs[idx] = (d // (base**j)) % base
                digits[j].append(layer)
            # note: residual beyond base^k1 must vanish — enforced by the
            # recomposition check below
        # recomposition check
        w_rec = [
            sum((digits[j][i] * (base**j) for j in range(k1)), start=ring.zero())
            for i in range(len(w))
        ]
        if w_rec != list(w):
            raise ValueError("base-b decomposition does not recompose (increase k')")
        # commitments + per-digit errors
        t_js = [self.commit(dj) for dj in digits]
        e_js = [self.power_constraint(dj, acc.beta) for dj in digits]
        # H(Y) = sum_i beta_i f_i(sum_j L_j(Y) w_j)
        Ls = [l_basis(j, k1, q) for j in range(k1)]
        w_comb = [
            sum((Ls[j] * _scalar(ring, digits[j][coord], nvars) for j in range(k1)),
                start=MPoly.const(0, q, nvars))
            for coord in range(self.m)
        ]
        H_terms = self.f.eval_mpoly(w_comb)
        H = MPoly.const(0, q, nvars)
        for b_i, hterm in zip(acc.beta, H_terms):
            H = H + hterm * (b_i % q)
        # H - sum_j L_j e_j = sum K Z  (Groebner)
        target = H
        for j in range(k1):
            target = target - l_basis(j, k1, q) * (e_js[j].coeffs[0] % q)
        K, R = divide(target)
        if not R.is_zero():
            raise AssertionError("PGL-Boot Groebner remainder nonzero (bug)")
        # send (t_j, e_j, K)
        transcript.absorb_bytes(b"pgl:boot:start")
        for c in acc.t:
            transcript.absorb_ring(c)
        for tj in t_js:
            for c in tj:
                transcript.absorb_ring(c)
        for ej in e_js:
            transcript.absorb_ring(ej)
        y = [ring.challenge_small(transcript, label=f"pgl:by{i}") for i in range(k1)]
        y[0] = ring.challenge_small(transcript, label="pgl:by0fix")
        # updates
        cs = [l_eval(j, k1, [c.coeffs[0] for c in y], q) for j in range(k1)]
        w_star = [
            sum((digits[j][coord] * c for j, c in enumerate(cs)), start=ring.zero())
            for coord in range(self.m)
        ]
        t_star = [
            sum((t_js[j][idx] * c for j, c in enumerate(cs)), start=ring.zero())
            for idx in range(len(acc.t))
        ]
        x_star = [
            sum((acc.x[idx] * (1 if j == 0 else 0) for j in range(k1)), start=ring.zero())
            for idx in range(len(acc.x))
        ]
        pts = [c.coeffs[0] for c in y]
        kz = ring.zero()
        for (i, j), Kij in K.items():
            kz = kz + ring.from_int(Kij.eval(pts)) * ring.from_int(z_eval(i, j, pts, q))
        e_star = kz + sum((e_js[j] * c for j, c in enumerate(cs)), start=ring.zero())
        gamma = int(sum(x.l2_sq_int() for x in digits[0]) ** 0.5) + 1
        new_acc = Accumulator(t=t_star, x=x_star, beta=list(acc.beta), e=e_star,
                              w=w_star, gamma=gamma)
        proof = BootProof(t_js=t_js, e_js=e_js, K=K, y=y, base=base, k_prime=k_prime)
        return new_acc, proof

    def boot_verify(
        self,
        acc: Accumulator,
        proof: BootProof,
        transcript: Transcript,
        degree: int = 2,
    ) -> Tuple[bool, Accumulator]:
        ring = self.ring
        q = ring.q
        k1 = proof.k_prime
        if not quotient_degree_bound_ok(proof.K, degree - 2):
            return False, None
        transcript.absorb_bytes(b"pgl:boot:start")
        for c in acc.t:
            transcript.absorb_ring(c)
        for tj in proof.t_js:
            for c in tj:
                transcript.absorb_ring(c)
        for ej in proof.e_js:
            transcript.absorb_ring(ej)
        y = [ring.challenge_small(transcript, label=f"pgl:by{i}") for i in range(k1)]
        y[0] = ring.challenge_small(transcript, label="pgl:by0fix")
        if y != proof.y:
            return False, None
        # ---- the D-evaluation checks (Figure 3):
        # sum b^j t_j == t ; sum b^j e_j == e + sum Z(D) K(D) with L_j(D) = b^j
        t_sum = [
            sum((proof.t_js[j][idx] * (proof.base**j) for j in range(k1)),
                start=ring.zero())
            for idx in range(len(acc.t))
        ]
        if t_sum != list(acc.t):
            return False, None
        # D_j = sum_{l<=j} b^l  (so that L_j(D) = b^j)
        D = [sum(proof.base**l for l in range(j + 1)) % q for j in range(k1)]
        kz_D = ring.zero()
        for (i, j), Kij in proof.K.items():
            kz_D = kz_D + ring.from_int(Kij.eval(D)) * ring.from_int(z_eval(i, j, D, q))
        e_sum = sum((proof.e_js[j] * (proof.base**j) for j in range(k1)),
                    start=ring.zero())
        if e_sum != acc.e + kz_D:
            return False, None
        # ---- folded statement update
        cs = [l_eval(j, k1, [c.coeffs[0] for c in y], q) for j in range(k1)]
        t_star = [
            sum((proof.t_js[j][idx] * c for j, c in enumerate(cs)), start=ring.zero())
            for idx in range(len(acc.t))
        ]
        x_star = [ring.zero() for _ in acc.x]
        pts = [c.coeffs[0] for c in y]
        kz = ring.zero()
        for (i, j), Kij in proof.K.items():
            kz = kz + ring.from_int(Kij.eval(pts)) * ring.from_int(z_eval(i, j, pts, q))
        e_star = kz + sum((proof.e_js[j] * c for j, c in enumerate(cs)), start=ring.zero())
        new_acc = Accumulator(t=t_star, x=x_star, beta=list(acc.beta), e=e_star,
                              w=None, gamma=0)
        return True, new_acc


def _scalar(ring: Ring, elt: RingElt, nvars: int) -> MPoly:
    """Embed a ring element as an MPoly constant (constant-coefficient
    embedding — the lab's f-maps use Z_q-scalar entries lifted into R_q;
    full ring-element coefficients would need a module-valued MPoly,
    documented in the gap ledger)."""
    return MPoly.const(elt.coeffs[0] % ring.q, ring.q, nvars)


@dataclass
class FoldProof:
    F_const: RingElt
    F_lin: RingElt
    alpha: RingElt
    K: dict
    y: List[RingElt]
    delta: RingElt


@dataclass
class BootProof:
    t_js: List[List[RingElt]]
    e_js: List[RingElt]
    K: dict
    y: List[RingElt]
    base: int
    k_prime: int
