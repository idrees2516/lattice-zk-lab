# Polynomial-Time Key-Recovery Attack on PROV — Deep Analysis & Implementation Spec

## 1. Metadata
"Polynomial-Time Key-Recovery Attack on the NIST Specification of PROV"
(River Moreira Ferreira, Ludovic Perret; Sorbonne Université, LIP6).
Attack paper — context for the lab's Gröbner module.

## 2. Notation Table
PROV/UOV: n oil variables, m = n equations; F: F_q^{n+m} -> F_q^m the public
quadratic map; public key P = F restricted by the oil space O; sk = the oil
subspace. The attack: solve the public-key polynomial system directly.

## 3. Algebraic Setting
The homogeneous quadratic system defining PROV's key; the structure yields
to Gröbner-basis elimination (the "directsolve"-style weakness of the v1.0
parameter sets: the system's quotient algebra degenerates).

## 4. Relations
Key recovery ⟺ finding the oil space ⟺ solving the quadratic system
{P_i(x) = 0} with the bilinear structure of UOV.

## 5. Protocols (attack pipeline)
1. Set up the public-key equations over the (small) finite field.
2. Run a graded-basis / F4-F5 elimination; PROV v1.0's structure gives a
   polynomial-time degree collapse (the paper's core result: the first
   fall degree is constant, leading to full key recovery in polynomial time).
3. Recover the oil space; forge signatures.

## 6. Soundness & Security
The attack breaks PROV v1.0's EUF-CMA proof premise (hardness of the
public-key system). NIST's subsequent round fixed the parameters.

## 7. Parameters & Concrete Efficiency
Recovered in seconds/minutes at the NIST v1.0 security levels.

## 8. Implementation Notes
Cautionary backdrop for `lzk.core.groebner`: the lab implements Gröbner
**division** (normal forms + quotient extraction) for ProtogaLattice's
verifier-side check compression — a sound use; the attack uses Gröbner
**elimination** to break systems. Arithmetization-oriented primitives must
be analyzed against directsolve-style attacks before use.

## 9. Implementation Status (Gap Ledger)
Analysis only (attack paper): documented as the security-lesson companion
to the Gröbner module. No attack code implemented by policy.
