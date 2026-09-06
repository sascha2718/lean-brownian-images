# Pair-distance profiles and Minkowski reconstruction of planar Brownian images: the Lean formalisation

[![Comparator audit](https://github.com/sascha2718/lean-brownian-images/actions/workflows/comparator.yml/badge.svg)](https://github.com/sascha2718/lean-brownian-images/actions/workflows/comparator.yml)

A Lean 4 formalisation, over Mathlib, of the paper

> Sascha Troscheit, *Pair-distance profiles and Minkowski reconstruction of planar
> Brownian images*, 2026. arXiv:XXXX.XXXXX (identifier to be filled in).

Every numbered result of the paper is stated formally and proved, together with the
displayed claims that a later result cites or that carry a hypothesis of their own.
The library is `sorry`-free, declares no axiom, and every proof uses only the three
standard axioms `propext`, `Classical.choice` and `Quot.sound`; `native_decide` is not
used.

## What is proved

The two headline theorems of the paper, and the two claims of the final sentence of the
second, are the audited endpoints:

| Paper | Endpoint |
| --- | --- |
| `thm:main`: distinct pair-distance profiles give mutually singular occupation-measure laws | `audit_main` |
| `thm:cantor-application`: the homogeneous and the paired natural measure separate | `audit_cantor_application`, `audit_cantor_application_pair` |
| `thm:cantor-application`, final sentence: the exceptional parameter set is countable | `audit_exceptional_parameters_countable` |

Beside them, `Solution.lean` states 84 endpoints in all, named `audit_<slug>` in document
order, from the Gaussian reduction of the correlation integral through the renewal
analysis, the smoothing operator and its Fourier multipliers, the four-point estimate and
the concentration argument, to the Minkowski reconstruction of the occupation measure
from the compact Brownian image, the transfer of singularity to compact-set laws, and the
homometric counterexample. The table of every result against its endpoint is in
[`docs/correspondence.md`](docs/correspondence.md).

## Layout

- `BrownianImages/`: the library, 94 modules organised along the sections of the paper.
  The root module `BrownianImages.lean` is the index: it lists every module with the part
  of the paper it certifies. `BrownianImages/Minkowski/` carries the reconstruction
  section, and `BrownianImages/Renewal/` is vendored third-party code, see below.
- `Solution.lean`: the formal statement of the paper, every endpoint proved by a library
  declaration.
- `Challenge.lean`: the four headline endpoints restated with `sorry`, on Mathlib-only
  copies of the definitions their statements need. It imports only Mathlib, so the audit
  trusts this file and Mathlib alone. Its statement text is character-for-character
  identical to `Solution.lean`.
- `comparator-config.json`, `comparator-audit.sh`: the audit configuration and a local
  runner for it.
- `docs/`: the [correspondence with the paper](docs/correspondence.md), including the
  fidelity boundary; [what Mathlib does not have](docs/mathlib-gaps.md); and the account
  of the [vendored renewal library](docs/renewal-library.md).

Every module opens with a comment naming the section of the paper it mirrors and the
declarations that matter, and every declaration carries a doc comment naming the label of
the paper it certifies.

## Building

The project pins Lean `v4.32.2` and Mathlib `v4.32.2` (`lean-toolchain`,
`lake-manifest.json`). With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get          # the prebuilt Mathlib
lake build                  # the library
lake build Solution Challenge
```

## The audit

[Comparator](https://github.com/leanprover/comparator) compares the statements of
`Challenge.lean` with the identically named declarations of `Solution.lean`, audits the
axioms of the solution proofs on the raw `lean4export` output, and replays the proofs
through the Lean kernel, trusting neither the elaborator nor `#print axioms`. Because
`Challenge.lean` imports only Mathlib, the guarantee covers the audited statements as
written there, with the library never trusted. The other endpoints of `Solution.lean` are
checked by `lake build Solution`: the library declares no axiom, so they rest on the same
three axioms.

The GitHub workflow `.github/workflows/comparator.yml` runs the audit on every push, fully
sandboxed: comparator, `lean4export` and `landrun` are built at pinned commits, the
sandbox is probed, and comparator runs inside a `systemd-run` unit with network access
denied.

To run it locally, build [comparator](https://github.com/leanprover/comparator) and
[lean4export](https://github.com/leanprover/lean4export) at Lean `v4.32.2`, then

```
COMPARATOR_TOOLS=/path/to/tools ./comparator-audit.sh
```

where the tools directory contains the two checkouts; `COMPARATOR_LANDRUN` and
`COMPARATOR_LEAN4EXPORT` override the individual binaries. On macOS, where `landrun`
is unavailable, the script uses comparator's unsandboxed shim.

## Correspondence with the paper

Comparator never compares against the paper, so the correspondence between the formal
statements and the document is a human obligation. [`docs/correspondence.md`](docs/correspondence.md)
argues it: the statement layer, the endpoint table, and the fidelity boundary, that is
the places where a formal statement can look right and be false or vacuous, chiefly the
support condition on a measure and the clipping of negative times by `Real.toNNReal`.

## Licence

The code in this repository is licensed under the Apache License 2.0, see `LICENSE`.
`BrownianImages/Renewal/` is vendored from Benny Avelin's
[AbsorptionCutoff](https://github.com/BennyAvelin/AbsorptionCutoff), also under the
Apache License 2.0, with the modifications recorded in `NOTICE` and in each file's
header.

## Citation

See `CITATION.cff`.
