/-
The renewal layer, vendored.

`thm:non-lattice-limit` and `thm:neighbourhood-renewal` are applications of the
non-arithmetic key renewal theorem for directly Riemann integrable functions on the
line (Feller, vol. II, §XI).  Mathlib has no renewal theory at all, but that theorem is
formalised, sorry-free and Mathlib-only, in Benny Avelin's `AbsorptionCutoff`.  The six
modules below are its renewal leaf, copied in under the Apache License 2.0;
`Renewal/LICENSE` is the licence, and each file carries its provenance and the
statement of how it was modified.  Two changes were made: the `import` lines were
rewritten to the module paths of this project, and the `Nonlattice` hypothesis of the
key renewal theorem was weakened to `FellerNonlattice`, which is what its proof
consumes.  `docs/renewal-library.md` gives the account.

Upstream: https://github.com/BennyAvelin/AbsorptionCutoff
Commit:   41c45c6d72e979419e46224bb7b4be5cee31f2b5
Files:    AbsorptionCutoff/Supercritical/{Renewal, RenewalAbel, RenewalKernel,
          RenewalSinc, RenewalApprox, RenewalEquation}.lean

The declarations keep their upstream namespace `AbsorptionCutoff.Renewal`, so nothing
here is confusable with a declaration of this project.

The headline `tendsto_tsum_integral_comp_sub_of_driNorm`, as stated upstream, does not
apply to the renewal measure `ϑ = ∑ p_i δ_{a_i}` of a self-similar system:
`RenewalBridge.not_nonlattice_renewalLaw` proves that a two-atom law always charges an
affine lattice.  Under `FellerNonlattice`, which `ϑ` satisfies exactly under
`eq:non-lattice` (`System.nonArithmetic_iff_charFun_ne_one`), the theorem applies, and
`KeyRenewalFourier` and `Minkowski.TubeRenewalLimit` consume it in that form.
-/
import BrownianImages.Renewal.Basic
import BrownianImages.Renewal.Abel
import BrownianImages.Renewal.Kernel
import BrownianImages.Renewal.Sinc
import BrownianImages.Renewal.Approx
import BrownianImages.Renewal.Equation
