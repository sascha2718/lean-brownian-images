# Correspondence with the paper

All 32 numbered statements of [arXiv:2610.16339v1](https://arxiv.org/abs/2610.16339v1)
are formalised with the paper's hypotheses and conclusions. The
[README](../README.md) lists the nine headline endpoints;
[paper-correspondence.yaml](../paper-correspondence.yaml) gives the full statement mapping.

The supporting renewal theory is proved for the self-similar laws used in the paper.
The full generality of the quoted renewal theorem, its lattice renewal-series identity
and its uniform-continuity conclusion are not separately formalised. The required
uniform lattice convergence is proved directly. Background discussions and conjectures
are outside the formalisation.

The main differences in formulation are:

- Lean uses closed-ball Frostman bounds and a closed time-correlation inequality.
  Proved conversions and atomlessness connect these with the paper's conventions.
- The library's `fixedMoment` is the normalised cross-term integral; the paper's
  unnormalised integral is `2p(1-p)` times this quantity. The formal mean is proved
  equal to the Brownian Cesàro mean.
- Lemma 9.2 is stronger in Lean: the open convex domain need not be bounded.

The lattice limit in Proposition 3.3 and Lemma 3.4 is the paper's explicit periodisation,
with convergence of its defining series proved. Some proofs take different routes:

| Result | Paper | Lean |
| --- | --- | --- |
| Lattice non-constancy | Comparison of two phases | Contradiction from convergence |
| Four-point estimate | Integral estimates | Dyadic summation |
| Neighbourhood concentration | First/fourth-moment interpolation | Third-moment interpolation |
| Base-five example | Cylinder counting | First-digit recursions |

The small-parameter argument uses the sufficient bound `0.754 < 0.88` in place of
`0.62 < 0.88`. The three numbered derivative bounds retain the constants `6`, `3000`
and `10¹¹`, with the same parameter ranges and conclusions.
