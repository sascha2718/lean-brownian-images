/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: the deterministic data of the
first-level pieces used by Minkowski reconstruction.

* `System.IsAttractor.toNonemptyCompacts`, `System.IsNatural.compactAttractor`,
  `System.IsNatural.compactPiece`: the attractor and its first-level pieces as points
  of the Hausdorff hyperspace.
* `System.halfLogRatio`, `System.tubeWeight`, `tubeExponent`: the parameters
  `β_i`, `p_i` and `α` of `sec:reconstruction`.
-/
import BrownianImages.SelfSimilar
import Mathlib.Topology.MetricSpace.Closeds

namespace BrownianImages

open MeasureTheory TopologicalSpace

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- Bundle a nonempty compact attractor as a point of the Hausdorff hyperspace. -/
def IsAttractor.toNonemptyCompacts {K : Set ℝ} (hK : S.IsAttractor K) :
    NonemptyCompacts ℝ :=
  ⟨⟨K, hK.1⟩, hK.2.1⟩

/-- The attractor bundled as a nonempty compact set has itself as underlying set. -/
@[simp]
theorem IsAttractor.coe_toNonemptyCompacts {K : Set ℝ} (hK : S.IsAttractor K) :
    (hK.toNonemptyCompacts : Set ℝ) = K := rfl

/-- The bundled compact attractor carried by a natural measure. -/
def IsNatural.compactAttractor {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) : NonemptyCompacts ℝ :=
  hmu.attractor.toNonemptyCompacts

/-- The compact attractor carried by a natural measure has the attractor as underlying
set. -/
@[simp]
theorem IsNatural.coe_compactAttractor {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) :
    (hmu.compactAttractor : Set ℝ) = K := rfl

/-- Each similarity of a system is continuous. -/
theorem continuous_map (i : ι) : Continuous (S.map i) := by
  unfold map
  fun_prop

/-- The `i`th first-level piece of a compact attractor, bundled in the Hausdorff
hyperspace. -/
noncomputable def IsAttractor.compactPiece {K : Set ℝ} (hK : S.IsAttractor K)
    (i : ι) : NonemptyCompacts ℝ :=
  hK.toNonemptyCompacts.map (S.map i) (S.continuous_map i)

/-- The `i`-th compact piece of the attractor is its image under `S_i`. -/
@[simp]
theorem IsAttractor.coe_compactPiece {K : Set ℝ} (hK : S.IsAttractor K) (i : ι) :
    (hK.compactPiece S i : Set ℝ) = S.map i '' K := by
  rw [IsAttractor.compactPiece, NonemptyCompacts.coe_map,
    IsAttractor.coe_toNonemptyCompacts]

/-- The first-level compact time piece carried by a natural measure. -/
noncomputable def IsNatural.compactPiece {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (i : ι) : NonemptyCompacts ℝ :=
  hmu.attractor.compactPiece S i

/-- The `i`-th compact piece, read through the natural measure, is the image of the
attractor under `S_i`. -/
@[simp]
theorem IsNatural.coe_compactPiece {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (i : ι) :
    (hmu.compactPiece S i : Set ℝ) = S.map i '' K := by
  exact hmu.attractor.coe_compactPiece S i

/-- The half-logarithmic step `β_i = (1/2) log(1/r_i)` of
`sec:reconstruction`. -/
noncomputable def halfLogRatio (i : ι) : ℝ := (1 / 2 : ℝ) * S.logRatio i

/-- Every half-logarithmic step is positive. -/
theorem halfLogRatio_pos (i : ι) : 0 < S.halfLogRatio i := by
  exact mul_pos (by norm_num) (S.logRatio_pos i)

/-- The natural cylinder weight `p_i = r_i^s` of `sec:reconstruction`. -/
noncomputable def tubeWeight (s : ℝ) (i : ι) : ℝ := S.ratio i ^ s

/-- At the similarity dimension, the natural cylinder weights sum to one. -/
theorem sum_tubeWeight {s : ℝ} (hdim : S.IsDimension s) :
    ∑ i, S.tubeWeight s i = 1 := by
  change ∑ i, S.ratio i ^ s = 1
  exact hdim

/-- Every natural cylinder weight is strictly positive. -/
theorem tubeWeight_pos (s : ℝ) (i : ι) : 0 < S.tubeWeight s i :=
  Real.rpow_pos_of_pos (S.ratio_pos i) s

/-- In positive dimension every natural cylinder weight is strictly below one. -/
theorem tubeWeight_lt_one {s : ℝ} (hs : 0 < s) (i : ι) : S.tubeWeight s i < 1 := by
  exact Real.rpow_lt_one (S.ratio_pos i).le (S.ratio_lt_one i) hs

end System

/-- The normalising exponent `α = 2 - 2s` of `sec:reconstruction`. -/
def tubeExponent (s : ℝ) : ℝ := 2 - 2 * s


end BrownianImages
