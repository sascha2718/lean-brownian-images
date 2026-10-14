# Distinguishing sets and measures from their planar Brownian images

Lean 4 formalisation of the manuscript of the same title by Sascha Troscheit (2026).

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
with supporting results and examples. The library and Solution have no proof holes or
literature axioms. The Comparator configuration permits only `propext`, `Classical.choice`
and `Quot.sound`.

**Qualifications:** the explicit lattice periodisation formula in the renewal proof is
not separately formalised. The introduction's correlation-dimension and local-density
discussion, and its comparisons with dynamical reconstruction and hitting-time statistics,
are background outside the formalisation. Some proof routes and numerical bounds differ.
[paper-correspondence.yaml](paper-correspondence.yaml) maps all 32 numbered statements and
records these exclusions; [docs/correspondence.md](docs/correspondence.md) explains the
representations and proof differences. Authorship, sources, AI assistance and review are
recorded in [formalization.yaml](formalization.yaml).

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
