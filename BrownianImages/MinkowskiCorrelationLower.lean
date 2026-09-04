/-
`eq:neighbourhood-correlation-lower-bound`: deterministic ball-mass and correlation
estimates behind the lower bound for the area of a compact set's tube.

The proof is kept first in `ENNReal`.  This makes Tonelli's theorem available
without provisional integrability assumptions.  Finiteness is introduced only at
the final conversion to the real-valued `tubeArea` used by the paper.
-/
import BrownianImages.MinkowskiProfile
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace BrownianImages

open MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

/-- The mass assigned by `nu` to the open ball of radius `r` about `x`. -/
def ballMass (nu : Measure Plane) (r : ℝ) (x : Plane) : ℝ≥0∞ :=
  nu (Metric.ball x r)

/-- The ball-mass function is measurable for every s-finite measure. -/
theorem measurable_ballMass (nu : Measure Plane) [SFinite nu] (r : ℝ) :
    Measurable (ballMass nu r) := by
  let A : Set (Plane × Plane) := {p | dist p.1 p.2 < r}
  have hA : MeasurableSet A := measurableSet_corrSet r
  have hsection : ∀ x : Plane, Prod.mk x ⁻¹' A = Metric.ball x r := by
    intro x
    ext y
    simp only [A, Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_ball, dist_comm]
  have hm : Measurable (fun x : Plane => nu (Prod.mk x ⁻¹' A)) :=
    measurable_measure_prodMk_left hA
  change Measurable (fun x : Plane => nu (Metric.ball x r))
  simpa only [hsection] using hm

/-- Correlation is the integral, with respect to the measure itself, of its local
open-ball masses. -/
theorem corr_eq_lintegral_ballMass (nu : Measure Plane) [SFinite nu] (r : ℝ) :
    corr nu r = ∫⁻ x, ballMass nu r x ∂nu := by
  let A : Set (Plane × Plane) := {p | dist p.1 p.2 < r}
  have hsection : ∀ x : Plane, Prod.mk x ⁻¹' A = Metric.ball x r := by
    intro x
    ext y
    simp only [A, Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_ball, dist_comm]
  rw [corr, Measure.prod_apply (measurableSet_corrSet r)]
  simp_rw [show {p : Plane × Plane | dist p.1 p.2 < r} = A from rfl,
    hsection]
  rfl

/-- The first spatial moment of the ball-mass function.  It is the area of one
radius-`r` disc times the total mass of `nu`. -/
theorem lintegral_ballMass_volume (nu : Measure Plane) [SFinite nu] (r : ℝ) :
    ∫⁻ x, ballMass nu r x ∂volume =
      (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) * nu Set.univ := by
  let A : Set (Plane × Plane) := {p | dist p.1 p.2 < r}
  have hA : MeasurableSet A := measurableSet_corrSet r
  have hleft : ∀ x : Plane, Prod.mk x ⁻¹' A = Metric.ball x r := by
    intro x
    ext y
    simp only [A, Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_ball, dist_comm]
  have hright : ∀ y : Plane, (fun x => (x, y)) ⁻¹' A = Metric.ball y r := by
    intro y
    ext x
    simp only [A, Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_ball]
  calc
    ∫⁻ x, ballMass nu r x ∂volume = (volume.prod nu) A := by
      rw [Measure.prod_apply hA]
      simp_rw [hleft]
      rfl
    _ = ∫⁻ y, volume (Metric.ball y r) ∂nu := by
      rw [Measure.prod_apply_symm hA]
      simp_rw [hright]
    _ = (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) * nu Set.univ := by
      simp

/-- The triples `(z,x,y)` for which `z` lies in both radius-`r` balls centred at
`x` and `y`. -/
def commonBallTripleSet (r : ℝ) : Set (Plane × (Plane × Plane)) :=
  {q | dist q.1 q.2.1 < r ∧ dist q.1 q.2.2 < r}

theorem measurableSet_commonBallTripleSet (r : ℝ) :
    MeasurableSet (commonBallTripleSet r) := by
  exact
    (measurableSet_lt
      (measurable_fst.dist (measurable_fst.comp measurable_snd))
      measurable_const).inter
    (measurableSet_lt
      (measurable_fst.dist (measurable_snd.comp measurable_snd))
      measurable_const)

/-- The spatial `L²` ball-mass estimate.  If a point belongs to two radius-`r`
balls, their centres are less than `2r` apart; the common part has area at most
the area of one disc. -/
theorem lintegral_ballMass_sq_le_corr (nu : Measure Plane) [SFinite nu]
    (r : ℝ) :
    ∫⁻ z, ballMass nu r z ^ 2 ∂volume ≤
      (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) * corr nu (2 * r) := by
  let T : Set (Plane × (Plane × Plane)) := commonBallTripleSet r
  let C : Set (Plane × Plane) := {p | dist p.1 p.2 < 2 * r}
  let area : ℝ≥0∞ := ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi
  have hT : MeasurableSet T := measurableSet_commonBallTripleSet r
  have hC : MeasurableSet C := measurableSet_corrSet (2 * r)
  have hleft : ∀ z : Plane,
      Prod.mk z ⁻¹' T = Metric.ball z r ×ˢ Metric.ball z r := by
    intro z
    ext p
    simp only [T, commonBallTripleSet, Set.mem_preimage, Set.mem_setOf_eq,
      Set.mem_prod, Metric.mem_ball, dist_comm]
  have hright_le : ∀ p : Plane × Plane,
      volume ((fun z : Plane => (z, p)) ⁻¹' T) ≤ C.indicator (fun _ => area) p := by
    intro p
    by_cases hp : p ∈ C
    · rw [Set.indicator_of_mem hp]
      change volume ((fun z : Plane => (z, p)) ⁻¹' T) ≤
        ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi
      rw [← EuclideanSpace.volume_ball_fin_two p.1 r]
      apply measure_mono
      intro z hz
      change dist z p.1 < r
      exact hz.1
    · rw [Set.indicator_of_notMem hp]
      suffices (fun z : Plane => (z, p)) ⁻¹' T = ∅ by simp [this]
      refine Set.Subset.antisymm ?_ (Set.empty_subset _)
      intro z hz
      exact (hp (show p ∈ C by
        change dist p.1 p.2 < 2 * r
        have hz1 : dist z p.1 < r := hz.1
        have hz2 : dist z p.2 < r := hz.2
        calc
          dist p.1 p.2 ≤ dist p.1 z + dist z p.2 := dist_triangle _ _ _
          _ < 2 * r := by rw [dist_comm p.1 z]; linarith)).elim
  calc
    ∫⁻ z, ballMass nu r z ^ 2 ∂volume =
        (volume.prod (nu.prod nu)) T := by
      rw [Measure.prod_apply hT]
      apply lintegral_congr
      intro z
      rw [hleft, Measure.prod_prod]
      simp only [ballMass, pow_two]
    _ = ∫⁻ p, volume ((fun z : Plane => (z, p)) ⁻¹' T) ∂(nu.prod nu) := by
      rw [Measure.prod_apply_symm hT]
    _ ≤ ∫⁻ p, C.indicator (fun _ => area) p ∂(nu.prod nu) :=
      lintegral_mono hright_le
    _ = area * corr nu (2 * r) := by
      rw [lintegral_indicator hC, setLIntegral_const]
      rfl
    _ = (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) * corr nu (2 * r) := rfl

/-- A measure carried by `F` assigns zero mass to every radius-`r` ball whose
centre lies outside the open `r`-thickening of `F`. -/
theorem ballMass_eq_zero_of_notMem_thickening (nu : Measure Plane)
    (F : CompactPlane) {r : ℝ} (hsupport : nu (F : Set Plane)ᶜ = 0)
    {x : Plane} (hx : x ∉ Metric.thickening r (F : Set Plane)) :
    ballMass nu r x = 0 := by
  apply measure_mono_null _ hsupport
  intro y hy hyF
  have hxinf : r ≤ Metric.infDist x (F : Set Plane) := by
    rw [Metric.mem_thickening_iff_infDist_lt F.nonempty] at hx
    exact le_of_not_gt hx
  have hxy : Metric.infDist x (F : Set Plane) ≤ dist x y :=
    Metric.infDist_le_dist_of_mem hyF
  have hyx : dist y x < r := by simpa only [Metric.mem_ball] using hy
  rw [dist_comm] at hyx
  linarith

/-- Cauchy--Schwarz in the exact `ENNReal` form used for a nonnegative function
supported on a measurable set. -/
theorem sq_lintegral_le_measure_mul_lintegral_sq
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (E : Set X)
    {f : X → ℝ≥0∞} (hE : MeasurableSet E) (hf : Measurable f)
    (hsupport : ∀ x, x ∉ E → f x = 0) :
    (∫⁻ x, f x ∂mu) ^ 2 ≤ mu E * ∫⁻ x, f x ^ 2 ∂mu := by
  let oneE : X → ℝ≥0∞ := E.indicator (fun _ => 1)
  have honeE : Measurable oneE := measurable_const.indicator hE
  have hmul : (fun x => oneE x * f x) = f := by
    funext x
    by_cases hx : x ∈ E
    · simp [oneE, hx]
    · simp [oneE, hx, hsupport x hx]
  have hone_sq : ∫⁻ x, oneE x ^ (2 : ℝ) ∂mu = mu E := by
    rw [← lintegral_indicator_one hE]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ E <;> simp [oneE, hx]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    Real.HolderConjugate.two_two honeE.aemeasurable hf.aemeasurable
  simp only [Pi.mul_apply] at hholder
  rw [hmul, hone_sq] at hholder
  simp only [one_div, ENNReal.rpow_two] at hholder
  calc
    (∫⁻ x, f x ∂mu) ^ 2 ≤
        ((mu E) ^ (2 : ℝ)⁻¹ *
          (∫⁻ x, f x ^ 2 ∂mu) ^ (2 : ℝ)⁻¹) ^ 2 :=
      pow_le_pow_left' hholder 2
    _ = mu E * ∫⁻ x, f x ^ 2 ∂mu := by
      rw [mul_pow]
      congr 1 <;>
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] <;>
        norm_num

/-- For a probability measure carried by `F`, Cauchy--Schwarz and the spatial
`L²` estimate give the uncancelled correlation lower bound. -/
theorem discArea_sq_le_tubeVolume_mul_discArea_mul_corr
    (nu : Measure Plane) [IsProbabilityMeasure nu] (F : CompactPlane)
    (r : ℝ) (hsupport : nu (F : Set Plane)ᶜ = 0) :
    (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) ^ 2 ≤
      volume (Metric.thickening r (F : Set Plane)) *
        ((ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) * corr nu (2 * r)) := by
  let E : Set Plane := Metric.thickening r (F : Set Plane)
  have hcauchy := sq_lintegral_le_measure_mul_lintegral_sq
    volume E Metric.isOpen_thickening.measurableSet
    (measurable_ballMass nu r)
    (fun x hx => ballMass_eq_zero_of_notMem_thickening nu F hsupport hx)
  rw [lintegral_ballMass_volume] at hcauchy
  simp only [measure_univ, mul_one] at hcauchy
  exact hcauchy.trans <| mul_le_mul_right
    (lintegral_ballMass_sq_le_corr nu r)
    (volume E)

/-- After cancelling the positive finite disc area, the disc area is bounded by
tube area times correlation. -/
theorem discArea_le_tubeVolume_mul_corr
    (nu : Measure Plane) [IsProbabilityMeasure nu] (F : CompactPlane)
    {r : ℝ} (hr : 0 < r) (hsupport : nu (F : Set Plane)ᶜ = 0) :
    ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi ≤
      volume (Metric.thickening r (F : Set Plane)) * corr nu (2 * r) := by
  let area : ℝ≥0∞ := ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi
  have harea_pos : 0 < area := by
    dsimp [area]
    positivity
  have harea_top : area ≠ ∞ := by
    dsimp [area]
    finiteness
  apply (ENNReal.mul_le_mul_iff_right harea_pos.ne' harea_top).1
  have h := discArea_sq_le_tubeVolume_mul_discArea_mul_corr
    nu F r hsupport
  simpa only [area, pow_two, mul_assoc, mul_left_comm, mul_comm] using h

/-- Positive-radius correlation is automatically positive for a probability measure
carried by a compact set. -/
theorem corr_two_mul_pos_of_support
    (nu : Measure Plane) [IsProbabilityMeasure nu] (F : CompactPlane)
    {r : ℝ} (hr : 0 < r) (hsupport : nu (F : Set Plane)ᶜ = 0) :
    0 < corr nu (2 * r) := by
  apply pos_iff_ne_zero.2
  intro hzero
  have h := discArea_le_tubeVolume_mul_corr nu F hr hsupport
  rw [hzero, mul_zero] at h
  have harea : 0 < ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
    positivity
  exact (not_le_of_gt harea) h

/-- The exact `ENNReal` tube-correlation lower bound, with correlation nonvanishing
shown explicitly at the division boundary. -/
theorem discArea_div_corr_le_tubeVolume_of_ne_zero
    (nu : Measure Plane) [IsProbabilityMeasure nu] (F : CompactPlane)
    {r : ℝ} (hr : 0 < r) (hsupport : nu (F : Set Plane)ᶜ = 0)
    (hcorr : corr nu (2 * r) ≠ 0) :
    (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) / corr nu (2 * r) ≤
      volume (Metric.thickening r (F : Set Plane)) := by
  have hcorr_le : corr nu (2 * r) ≤ 1 := by
    unfold corr
    calc
      (nu.prod nu) {p : Plane × Plane | dist p.1 p.2 < 2 * r} ≤
          (nu.prod nu) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hcorr_top : corr nu (2 * r) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hcorr_le
  exact (ENNReal.div_le_iff hcorr hcorr_top).2
    (discArea_le_tubeVolume_mul_corr nu F hr hsupport)

/-- The exact `ENNReal` tube-correlation lower bound. -/
theorem discArea_div_corr_le_tubeVolume
    (nu : Measure Plane) [IsProbabilityMeasure nu] (F : CompactPlane)
    {r : ℝ} (hr : 0 < r) (hsupport : nu (F : Set Plane)ᶜ = 0) :
    (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) / corr nu (2 * r) ≤
      volume (Metric.thickening r (F : Set Plane)) :=
  discArea_div_corr_le_tubeVolume_of_ne_zero nu F hr hsupport
    (corr_two_mul_pos_of_support nu F hr hsupport).ne'

/-- `eq:neighbourhood-correlation-lower-bound` in the real-valued notation of the paper.
The explicit nonzero-correlation hypothesis is the honest condition needed for
division; finiteness follows automatically from probability mass one. -/
theorem tubeArea_ge_discArea_div_corr_of_ne_zero
    (nu : Measure Plane) [IsProbabilityMeasure nu] (F : CompactPlane)
    {r : ℝ} (hr : 0 < r) (hsupport : nu (F : Set Plane)ᶜ = 0)
    (hcorr : corr nu (2 * r) ≠ 0) :
    Real.pi * r ^ 2 / (corr nu (2 * r)).toReal ≤ tubeArea r F := by
  have h := discArea_div_corr_le_tubeVolume_of_ne_zero nu F hr hsupport hcorr
  have hvol_top : volume (Metric.thickening r (F : Set Plane)) ≠ ∞ :=
    (F.isCompact.isBounded.thickening.measure_lt_top).ne
  have hreal := ENNReal.toReal_mono hvol_top h
  simpa only [tubeArea, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_ofReal Real.pi_nonneg, mul_comm] using hreal

/-- `eq:neighbourhood-correlation-lower-bound`, with correlation positivity derived from the
probability and support assumptions. -/
theorem tubeArea_ge_discArea_div_corr
    (nu : Measure Plane) [IsProbabilityMeasure nu] (F : CompactPlane)
    {r : ℝ} (hr : 0 < r) (hsupport : nu (F : Set Plane)ᶜ = 0) :
    Real.pi * r ^ 2 / (corr nu (2 * r)).toReal ≤ tubeArea r F :=
  tubeArea_ge_discArea_div_corr_of_ne_zero nu F hr hsupport
    (corr_two_mul_pos_of_support nu F hr hsupport).ne'

end

end BrownianImages
