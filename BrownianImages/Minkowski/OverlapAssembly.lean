/-
System-level assembly of the tube-overlap theorem from its distinct-pair
estimate.

The Gaussian argument naturally proves one uniform estimate for every pair of
different first-level cylinders.  `Minkowski.DefectExpectation` then supplies
all remaining measurability, integrability, and finite-pair bookkeeping.  The
result below isolates that exact boundary in the notation of
`thm:neighbourhood-overlap`.
-/
import BrownianImages.Minkowski.DefectExpectation

namespace BrownianImages

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace System

variable {Omega iota : Type*} [MeasurableSpace Omega]
variable [Fintype iota] [Nonempty iota]

/-- Once the uniform distinct-pair estimate is known, the complete pair and
multiple-defect conclusion of `thm:neighbourhood-overlap` follows. -/
theorem IsNatural.tubeOverlap_of_pairwise
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set ℝ} {s : ℝ}
    (_hs0 : 0 < s) (_hs1 : s < 1)
    (_hsep : S.IntervalSeparated) (_hdim : S.IsDimension s)
    {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (hpair : ∃ C0 : ℝ, 0 < C0 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea r
            (brownianImage W (hmu.compactPiece S i) omega)
            (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
          C0 * r ^ (2 * tubeExponent s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea r
            (brownianImage W (hmu.compactPiece S i) omega)
            (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
          C * r ^ (2 * tubeExponent s)) ∧
      Integrable (fun omega => tubeDefect r
        (fun i => brownianImage W (hmu.compactPiece S i) omega)) P ∧
      (∫ omega, tubeDefect r
          (fun i => brownianImage W (hmu.compactPiece S i) omega) ∂P) ≤
        C * r ^ (2 * tubeExponent s) := by
  exact exists_pairwise_overlap_and_defect_bound
    (F := fun i omega => brownianImage W (hmu.compactPiece S i) omega)
    (fun i => hW.aemeasurable_brownianImage (hmu.compactPiece S i))
    (fun r hr _ => Real.rpow_nonneg hr.le _)
    hpair

end System

end

end BrownianImages
