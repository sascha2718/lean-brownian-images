/-
The renewal layer, vendored.

`thm:non-lattice-limit` is an application of the non-arithmetic key renewal theorem for
directly Riemann integrable functions on the line (Feller, vol. II, §XI). Mathlib has no
renewal theory at all, but that theorem is formalised, sorry-free and Mathlib-only, in
Benny Avelin's `AbsorptionCutoff`. The six modules below are its renewal leaf, copied in
under the Apache License 2.0; `Renewal/LICENSE` is the licence and each file carries its
provenance and whether it was modified. Only the `import` lines were changed.

Upstream: https://github.com/BennyAvelin/AbsorptionCutoff
Commit:   41c45c6d72e979419e46224bb7b4be5cee31f2b5
Files:    AbsorptionCutoff/Supercritical/{Renewal, RenewalAbel, RenewalKernel,
          RenewalSinc, RenewalApprox, RenewalEquation}.lean

The declarations keep their upstream namespace `AbsorptionCutoff.Renewal`, so nothing
here is confusable with a declaration of this project.

What this project consumes is **not** the headline
`tendsto_tsum_integral_comp_sub_of_driNorm`: its non-lattice hypothesis is the strongly
non-lattice one, and `RenewalBridge.not_nonlattice_renewalLaw` proves that the renewal
measure of a self-similar system never satisfies it. What it consumes is everything not
gated on that hypothesis, chiefly `eq_tsum_integral_comp_sub_of_renewalEquation`, the
renewal equation iterated, which is the first half of the proof of
`thm:non-lattice-limit`. `PLAN.md` records the split and the refutation.
-/
import BrownianImages.Renewal.Basic
import BrownianImages.Renewal.Abel
import BrownianImages.Renewal.Kernel
import BrownianImages.Renewal.Sinc
import BrownianImages.Renewal.Approx
import BrownianImages.Renewal.Equation
