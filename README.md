# Distinguishing sets and measures from their planar Brownian images

Lean 4 formalisation of the paper *Distinguishing sets and measures from their planar Brownian images*
by Sascha Troscheit (2026), [arXiv:2610.16339v2](https://arxiv.org/abs/2610.16339v2),
with a [Palomar registry entry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-15-000007).

## Scope
Expected correlation profiles distinguish planar Brownian images of time measures with
matching dimension. For natural self-similar measures under the open set condition, the
library proves lattice and non-lattice profile asymptotics and separation of their image
laws. Normalised neighbourhood measures recover the occupation measure from the compact
image, giving the corresponding separation of compact-set laws. In a two-contraction
family, each parameter has finitely many possible exceptions; for sufficiently small
dimension, every pair of distinct parameters is separated.

[Challenge.lean](Challenge.lean) contains the nine results of Section 1, each with an
intentional `sorry`, and their statement vocabulary over Mathlib:

| Result | Endpoint |
| --- | --- |
| 1.1 Profile separation | `audit_main` |
| 1.2 Profile asymptotics | `audit_profile_asymptotics` |
| 1.3 Lattice/non-lattice measure separation | `audit_lattice_nonlattice_measures` |
| 1.4 Finite exceptions | `audit_finite_exceptions` |
| 1.5 Small-dimension monotonicity | `audit_small_dimension` |
| 1.6 Finite critical set | `audit_finite_critical_set` |
| 1.7 Minkowski reconstruction | `audit_reconstruction` |
| 1.8 Lattice/non-lattice set separation | `audit_lattice_nonlattice_sets` |
| 1.9 Two-contraction set separation | `audit_two_contraction_sets` |

[Solution.lean](Solution.lean) proves these statements from [BrownianImages](BrownianImages.lean),
with supporting results and examples. The library and Solution are `sorry'-free and rely only on Mathlib.
The Comparator configuration permits only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

**Coverage:** all 32 numbered statements are formalised, including the nine headline
results and the explicit lattice periodisation. Supporting renewal results are proved
for the self-similar laws used in the paper; only the minimal version necessary for proving this has
been proved. In particularly, we do not prove the full Renewal theorem that we cite in the article.
None of the background discussions have been formalised.

[paper-correspondence.yaml](paper-correspondence.yaml) identifies the current manuscript revision
and maps its numbered statements.
[docs/correspondence.md](docs/correspondence.md) records scope and proof differences;
[formalization.yaml](formalization.yaml) records authorship, sources, AI assistance and review.

## Build and verification

Lean and Mathlib are pinned to `v4.35.0-rc2`. On a fresh independent checkout, obtain the
dependencies with `lake exe cache get`, then run:

```bash
lake build BrownianImages Challenge Solution
python3 scripts/check_module_headers.py
python3 scripts/check_paper_correspondence.py
```

The nine Challenge warnings are intentional. The correspondence check needs
`../BrownianImagesComplete.tex`; it checks source drift and declaration consistency,
not mathematical equivalence. This workstation shares `.lake/packages` with another
project, so do not run `lake update` or replace those dependencies there.

On Linux, `./comparator-audit.sh` uses the toolchain's sandboxed Comparator, Lean kernel,
NanoDa and con-ron. On macOS, `./comparator-audit.sh --local-unsandboxed` provides a
local development check with the same kernels, without Linux sandbox isolation.
The [Comparator workflow](.github/workflows/comparator.yml) runs the Linux audit.

Submit a public repository at an immutable commit, selecting `comparator-config.json`.
The [Palomar preflight](.github/workflows/palomar-preflight.yml) runs the registry verifier
on demand. Local checks do not establish Palomar acceptance.

## Attribution and licence

The formalisation is developed by the paper's author with AI assistance.
The sources use the [Apache License 2.0](LICENSE). Six renewal modules are adapted from
Benny Avelin's [AbsorptionCutoff](https://github.com/BennyAvelin/AbsorptionCutoff);
[NOTICE](NOTICE) and [docs/renewal-library.md](docs/renewal-library.md) record their
source and modifications. Citation details are in [CITATION.cff](CITATION.cff).
