module

/-
The renewal layer, vendored.

`thm:non-lattice-limit` and `thm:neighbourhood-renewal` are applications of the
non-arithmetic key renewal theorem for directly Riemann integrable functions on the
line (Feller, vol. II, §XI).  Mathlib has no renewal theory at all, but that theorem is
formalised, sorry-free and Mathlib-only, in Benny Avelin's `AbsorptionCutoff`.  The six
modules below are its renewal leaf, copied in under the Apache License 2.0;
`Renewal/LICENSE` is the licence, and each file carries its provenance and the
statement of how it was modified. Imports use this project's module paths, the key
renewal theorem uses `FellerNonlattice` in place of the stronger upstream
`Nonlattice`, and the subset retains the declarations needed by the proofs and
documented renewal interfaces. `docs/renewal-library.md` describes these changes.

Upstream: https://github.com/BennyAvelin/AbsorptionCutoff
Commit:   41c45c6d72e979419e46224bb7b4be5cee31f2b5
Files:    AbsorptionCutoff/Supercritical/{Renewal, RenewalAbel, RenewalKernel,
          RenewalSinc, RenewalApprox, RenewalEquation}.lean

The declarations keep their upstream namespace `AbsorptionCutoff.Renewal`, so nothing
here is confusable with a declaration of this project.

The headline `tendsto_tsum_integral_comp_sub_of_driNorm`, as stated upstream, does not
apply to the renewal measure `ϑ = ∑ p_i δ_{α_i}` of a two-map self-similar system:
`System.not_nonlattice_renewalLaw` proves that a two-atom law always charges an
affine lattice.  Under `FellerNonlattice`, which `ϑ` satisfies exactly under
`eq:non-lattice` (`System.nonArithmetic_iff_charFun_ne_one`), the theorem applies, and
`KeyRenewalFourier` and `Minkowski.TubeRenewalLimit` consume it in that form.
-/
public import BrownianImages.Renewal.Basic
public import BrownianImages.Renewal.Abel
public import BrownianImages.Renewal.Kernel
public import BrownianImages.Renewal.Sinc
public import BrownianImages.Renewal.Approx
public import BrownianImages.Renewal.Equation

@[expose] public section
