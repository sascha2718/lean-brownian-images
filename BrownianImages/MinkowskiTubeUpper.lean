/-
The deterministic and finite-moment assembly behind the upper half of
`thm:tube-moments`.

The paper covers the Brownian image by finitely many random discs.  This file
separates the two parts of that argument which do not use a Brownian maximal
inequality:

* a compact set covered by discs has both its smoothed and raw sausage bounded
  by the sum of the areas of the enlarged discs;
* the real `q`-moment of a finite nonnegative sum is bounded by the usual
  cardinality factor, with integrability and the expectation inequality kept
  explicit;
* the stopping-antichain count follows abstractly from the mass identity and a
  lower bound on every stopping ratio.

Thus a later Brownian input only has to supply the individual oscillation
moments and the stopping cover; no geometric or integration step remains
hidden in that input.
-/
import BrownianImages.MinkowskiOverlapTranslation
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace BrownianImages

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Smoothed mass is bounded by raw sausage area -/

/-- The triangular tube cut-off is pointwise bounded by the indicator of the
open tube. -/
theorem tubeCutoff_le_tubeIndicator {r : ℝ} (hr : 0 < r)
    (F : CompactPlane) (x : Plane) :
    tubeCutoff r F x ≤ tubeIndicator r F x := by
  by_cases hx : x ∈ Metric.thickening r (F : Set Plane)
  · rw [tubeIndicator, Set.indicator_of_mem hx]
    exact tubeCutoff_le_one hr F x
  · have hdist : r ≤ Metric.infDist x (F : Set Plane) := by
      rw [Metric.mem_thickening_iff_infDist_lt F.nonempty] at hx
      exact le_of_not_gt hx
    rw [tubeIndicator, Set.indicator_of_notMem hx,
      (tubeCutoff_eq_zero_iff hr F x).2 hdist]

/-- The smoothed tube mass is no larger than the area of the raw open
sausage at the same radius. -/
theorem tubeMass_le_tubeArea {r : ℝ} (hr : 0 < r) (F : CompactPlane) :
    tubeMass r F ≤ tubeArea r F := by
  rw [tubeMass, ← integral_tubeIndicator]
  exact integral_mono (integrable_tubeCutoff hr F)
    (integrable_tubeIndicator r F) (tubeCutoff_le_tubeIndicator hr F)

/-! ### A finite disc cover -/

/-- Enlarging a finite cover of a compact set by closed discs gives a cover of
its open sausage by correspondingly enlarged open discs. -/
theorem thickening_subset_iUnion_ball_of_subset_iUnion_closedBall
    {J : Type*} [Fintype J] {F : CompactPlane}
    (center : J → Plane) (radius : J → ℝ) {r : ℝ}
    (hcover : (F : Set Plane) ⊆ ⋃ j, Metric.closedBall (center j) (radius j)) :
    Metric.thickening r (F : Set Plane) ⊆
      ⋃ j, Metric.ball (center j) (r + radius j) := by
  intro x hx
  obtain ⟨y, hyF, hxy⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp (hcover hyF)
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  rw [Metric.mem_closedBall] at hyj
  rw [Metric.mem_ball]
  calc
    dist x (center j) ≤ dist x y + dist y (center j) := dist_triangle _ _ _
    _ < r + radius j := by linarith

/-- The raw sausage area of a compact set covered by finitely many closed
discs is bounded by the sum of the areas of the enlarged discs. -/
theorem tubeArea_le_pi_mul_sum_sq_of_subset_iUnion_closedBall
    {J : Type*} [Fintype J] (F : CompactPlane)
    (center : J → Plane) (radius : J → ℝ) {r : ℝ} (hr : 0 < r)
    (hradius : ∀ j, 0 ≤ radius j)
    (hcover : (F : Set Plane) ⊆ ⋃ j, Metric.closedBall (center j) (radius j)) :
    tubeArea r F ≤ Real.pi * ∑ j, (r + radius j) ^ 2 := by
  have hsub := thickening_subset_iUnion_ball_of_subset_iUnion_closedBall
    center radius (r := r) hcover
  have hmeasure :
      volume (Metric.thickening r (F : Set Plane)) ≤
        ∑ j, volume (Metric.ball (center j) (r + radius j)) :=
    (measure_mono hsub).trans (measure_iUnion_fintype_le volume _)
  have hsum_ne_top :
      (∑ j, volume (Metric.ball (center j) (r + radius j))) ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro j hj
    rw [EuclideanSpace.volume_ball_fin_two]
    finiteness
  have hreal := ENNReal.toReal_mono hsum_ne_top hmeasure
  change tubeArea r F ≤
    (∑ j, volume (Metric.ball (center j) (r + radius j))).toReal at hreal
  simp_rw [EuclideanSpace.volume_ball_fin_two] at hreal
  rw [ENNReal.toReal_sum (s := Finset.univ)
    (f := fun j => ENNReal.ofReal (r + radius j) ^ 2 * ENNReal.ofReal Real.pi)
    (fun j _ => by finiteness)] at hreal
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (add_nonneg hr.le (hradius _)),
    ENNReal.toReal_ofReal Real.pi_nonneg] at hreal
  calc
    tubeArea r F ≤ ∑ j, (r + radius j) ^ 2 * Real.pi := hreal
    _ = Real.pi * ∑ j, (r + radius j) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The complete deterministic cover estimate used in
`eq:tube-cover-bound`: the smoothed mass and the raw area are simultaneously
bounded by the same sum of enlarged disc areas. -/
theorem tubeMass_and_tubeArea_le_pi_mul_sum_sq_of_disc_cover
    {J : Type*} [Fintype J] (F : CompactPlane)
    (center : J → Plane) (radius : J → ℝ) {r : ℝ} (hr : 0 < r)
    (hradius : ∀ j, 0 ≤ radius j)
    (hcover : (F : Set Plane) ⊆ ⋃ j, Metric.closedBall (center j) (radius j)) :
    tubeMass r F ≤ Real.pi * ∑ j, (r + radius j) ^ 2 ∧
      tubeArea r F ≤ Real.pi * ∑ j, (r + radius j) ^ 2 := by
  have harea := tubeArea_le_pi_mul_sum_sq_of_subset_iUnion_closedBall
    F center radius hr hradius hcover
  exact ⟨(tubeMass_le_tubeArea hr F).trans harea, harea⟩

/-! ### Brownian-image specialization of the disc cover -/

variable {Omega : Type*} [MeasurableSpace Omega]

omit [MeasurableSpace Omega] in
/-- On a continuous path, any finite family of anchors and oscillation radii
covering the values at the prescribed time set gives the paper's sausage
cover bound.  The hypotheses deliberately mention only the local oscillation
statement which the Brownian maximal inequality supplies. -/
theorem brownianTube_cover_bound_of_continuous
    {W : ℝ≥0 → Omega → Plane} (K : NonemptyCompacts ℝ) {omega : Omega}
    (homega : Continuous (fun t : ℝ≥0 => W t omega))
    {J : Type*} [Fintype J] (anchor : J → ℝ) (oscillation : J → ℝ)
    {r : ℝ} (hr : 0 < r) (hosc : ∀ j, 0 ≤ oscillation j)
    (hcover : ∀ t ∈ (K : Set ℝ), ∃ j,
      dist (W t.toNNReal omega) (W (anchor j).toNNReal omega) ≤ oscillation j) :
    tubeMass r (brownianImage W K omega) ≤
        Real.pi * ∑ j, (r + oscillation j) ^ 2 ∧
      tubeArea r (brownianImage W K omega) ≤
        Real.pi * ∑ j, (r + oscillation j) ^ 2 := by
  apply tubeMass_and_tubeArea_le_pi_mul_sum_sq_of_disc_cover
    (brownianImage W K omega)
    (fun j => W (anchor j).toNNReal omega) oscillation hr hosc
  rw [coe_brownianImage_of_continuous K homega]
  rintro x ⟨t, ht, rfl⟩
  obtain ⟨j, hj⟩ := hcover t ht
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

/-! ### Finite-family real-moment assembly -/

/-- The convexity inequality in the exact real-exponent form used by
`thm:tube-moments`. -/
theorem rpow_sum_le_card_factor
    {J : Type*} [Fintype J] (a : J → ℝ) {q : ℝ} (hq : 1 ≤ q)
    (ha : ∀ j, 0 ≤ a j) :
    (∑ j, a j) ^ q ≤
      (Fintype.card J : ℝ) ^ (q - 1) * ∑ j, (a j) ^ q := by
  simpa only [Finset.card_univ] using
    (Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := Finset.univ) (f := a) hq (fun j _ => ha j))

/-- Integrability and expectation form of the finite-sum moment inequality.
No independence is required. -/
theorem integrable_rpow_sum_and_integral_le
    {J : Type*} [Fintype J] {P : Measure Omega}
    (a : J → Omega → ℝ) {q : ℝ} (hq : 1 ≤ q)
    (haemeas : ∀ j, AEMeasurable (a j) P)
    (ha : ∀ j omega, 0 ≤ a j omega)
    (hint : ∀ j, Integrable (fun omega => (a j omega) ^ q) P) :
    Integrable (fun omega => (∑ j, a j omega) ^ q) P ∧
      (∫ omega, (∑ j, a j omega) ^ q ∂P) ≤
        (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ j, ∫ omega, (a j omega) ^ q ∂P := by
  let B : Omega → ℝ := fun omega =>
    (Fintype.card J : ℝ) ^ (q - 1) * ∑ j, (a j omega) ^ q
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hsum_meas : AEMeasurable (fun omega => ∑ j, a j omega) P := by
    rw [show (fun omega => ∑ j, a j omega) = ∑ j : J, a j by
      funext omega
      simp]
    exact Finset.aemeasurable_sum Finset.univ (fun j _ => haemeas j)
  have hpow_meas : AEStronglyMeasurable
      (fun omega => (∑ j, a j omega) ^ q) P :=
    (Real.continuous_rpow_const hq0).measurable.comp_aemeasurable
      hsum_meas |>.aestronglyMeasurable
  have hBint : Integrable B P := by
    dsimp [B]
    exact (integrable_finsetSum Finset.univ fun j _ => hint j).const_mul _
  have hnonneg : ∀ omega, 0 ≤ (∑ j, a j omega) ^ q := fun omega =>
    Real.rpow_nonneg (Finset.sum_nonneg fun j _ => ha j omega) q
  have hle : ∀ omega, (∑ j, a j omega) ^ q ≤ B omega := fun omega =>
    rpow_sum_le_card_factor (fun j => a j omega) hq (fun j => ha j omega)
  have hfin : Integrable (fun omega => (∑ j, a j omega) ^ q) P :=
    hBint.mono_nonneg hpow_meas
      (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hle)
  refine ⟨hfin, ?_⟩
  calc
    (∫ omega, (∑ j, a j omega) ^ q ∂P) ≤ ∫ omega, B omega ∂P :=
      integral_mono hfin hBint hle
    _ = (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ j, ∫ omega, (a j omega) ^ q ∂P := by
      simp only [B, integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hint j)]

/-- Expectation-level assembly of the finite disc cover.  Once each squared
enlarged radius has an integrable `q`-moment, both the raw and smoothed random
sausages have integrable `q`-moments with the same explicit bound.  This is the
whole upper-moment proof after the stopping cover and the Brownian oscillation
estimate have been supplied. -/
theorem random_tube_moments_of_finite_disc_cover
    {J : Type*} [Fintype J] {P : Measure Omega}
    (F : Omega → CompactPlane) (hF : AEMeasurable F P)
    (center : J → Omega → Plane) (radius : J → Omega → ℝ)
    {r q : ℝ} (hr : 0 < r) (hq : 1 ≤ q)
    (hradius : ∀ j omega, 0 ≤ radius j omega)
    (hradiusMeas : ∀ j, AEMeasurable (radius j) P)
    (hcover : ∀ᵐ omega ∂P,
      (F omega : Set Plane) ⊆
        ⋃ j, Metric.closedBall (center j omega) (radius j omega))
    (hlocal : ∀ j,
      Integrable (fun omega => ((r + radius j omega) ^ 2) ^ q) P) :
    Integrable (fun omega => (tubeArea r (F omega)) ^ q) P ∧
      Integrable (fun omega => (tubeMass r (F omega)) ^ q) P ∧
      (∫ omega, (tubeArea r (F omega)) ^ q ∂P) ≤
        Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ j, ∫ omega, ((r + radius j omega) ^ 2) ^ q ∂P ∧
      (∫ omega, (tubeMass r (F omega)) ^ q ∂P) ≤
        Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ j, ∫ omega, ((r + radius j omega) ^ 2) ^ q ∂P := by
  let a : J → Omega → ℝ := fun j omega => (r + radius j omega) ^ 2
  let Y : Omega → ℝ := fun omega => (∑ j, a j omega) ^ q
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have haemeas : ∀ j, AEMeasurable (a j) P := by
    intro j
    exact (aemeasurable_const.add (hradiusMeas j)).pow_const 2
  have ha : ∀ j omega, 0 ≤ a j omega := fun j omega => sq_nonneg _
  obtain ⟨hYint, hYbound⟩ :=
    integrable_rpow_sum_and_integral_le a hq haemeas ha hlocal
  have hpiq : 0 ≤ Real.pi ^ q := Real.rpow_nonneg Real.pi_nonneg q
  have hscaledYint : Integrable (fun omega => Real.pi ^ q * Y omega) P := by
    exact hYint.const_mul _
  have harea_meas : AEStronglyMeasurable
      (fun omega => (tubeArea r (F omega)) ^ q) P :=
    (Real.continuous_rpow_const hq0).measurable.comp_aemeasurable
      ((measurable_tubeArea r).comp_aemeasurable hF) |>.aestronglyMeasurable
  have hmass_meas : AEStronglyMeasurable
      (fun omega => (tubeMass r (F omega)) ^ q) P :=
    (Real.continuous_rpow_const hq0).measurable.comp_aemeasurable
      ((measurable_tubeMass hr).comp_aemeasurable hF) |>.aestronglyMeasurable
  have harea_le : ∀ᵐ omega ∂P,
      (tubeArea r (F omega)) ^ q ≤ Real.pi ^ q * Y omega := by
    filter_upwards [hcover] with omega homega
    have hraw := tubeArea_le_pi_mul_sum_sq_of_subset_iUnion_closedBall
      (F omega) (fun j => center j omega) (fun j => radius j omega)
      hr (fun j => hradius j omega) homega
    calc
      (tubeArea r (F omega)) ^ q ≤
          (Real.pi * ∑ j, a j omega) ^ q :=
        Real.rpow_le_rpow (tubeArea_nonneg r (F omega)) hraw hq0
      _ = Real.pi ^ q * (∑ j, a j omega) ^ q :=
        Real.mul_rpow Real.pi_nonneg (Finset.sum_nonneg fun j _ => ha j omega)
      _ = Real.pi ^ q * Y omega := rfl
  have hmass_le : ∀ᵐ omega ∂P,
      (tubeMass r (F omega)) ^ q ≤ Real.pi ^ q * Y omega := by
    filter_upwards [harea_le] with omega homega
    exact (Real.rpow_le_rpow (tubeMass_nonneg r (F omega))
      (tubeMass_le_tubeArea hr (F omega)) hq0).trans homega
  have harea_nonneg : ∀ᵐ omega ∂P, 0 ≤ (tubeArea r (F omega)) ^ q :=
    Filter.Eventually.of_forall fun omega =>
      Real.rpow_nonneg (tubeArea_nonneg r (F omega)) q
  have hmass_nonneg : ∀ᵐ omega ∂P, 0 ≤ (tubeMass r (F omega)) ^ q :=
    Filter.Eventually.of_forall fun omega =>
      Real.rpow_nonneg (tubeMass_nonneg r (F omega)) q
  have harea_int : Integrable (fun omega => (tubeArea r (F omega)) ^ q) P :=
    hscaledYint.mono_nonneg harea_meas harea_nonneg harea_le
  have hmass_int : Integrable (fun omega => (tubeMass r (F omega)) ^ q) P :=
    hscaledYint.mono_nonneg hmass_meas hmass_nonneg hmass_le
  have harea_expect :
      (∫ omega, (tubeArea r (F omega)) ^ q ∂P) ≤
        Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ j, ∫ omega, ((r + radius j omega) ^ 2) ^ q ∂P := by
    calc
      (∫ omega, (tubeArea r (F omega)) ^ q ∂P) ≤
          ∫ omega, Real.pi ^ q * Y omega ∂P :=
        integral_mono_ae harea_int hscaledYint harea_le
      _ = Real.pi ^ q * ∫ omega, Y omega ∂P := by
        rw [integral_const_mul]
      _ ≤ Real.pi ^ q *
          ((Fintype.card J : ℝ) ^ (q - 1) *
            ∑ j, ∫ omega, ((r + radius j omega) ^ 2) ^ q ∂P) := by
        exact mul_le_mul_of_nonneg_left hYbound hpiq
      _ = Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ j, ∫ omega, ((r + radius j omega) ^ 2) ^ q ∂P := by ring
  have hmass_expect :
      (∫ omega, (tubeMass r (F omega)) ^ q ∂P) ≤
        Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ j, ∫ omega, ((r + radius j omega) ^ 2) ^ q ∂P := by
    calc
      (∫ omega, (tubeMass r (F omega)) ^ q ∂P) ≤
          ∫ omega, Real.pi ^ q * Y omega ∂P :=
        integral_mono_ae hmass_int hscaledYint hmass_le
      _ = Real.pi ^ q * ∫ omega, Y omega ∂P := by
        rw [integral_const_mul]
      _ ≤ Real.pi ^ q *
          ((Fintype.card J : ℝ) ^ (q - 1) *
            ∑ j, ∫ omega, ((r + radius j omega) ^ 2) ^ q ∂P) := by
        exact mul_le_mul_of_nonneg_left hYbound hpiq
      _ = Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ j, ∫ omega, ((r + radius j omega) ^ 2) ^ q ∂P := by ring
  exact ⟨harea_int, hmass_int, harea_expect, hmass_expect⟩

/-! ### The abstract stopping-antichain count -/

/-- The numerical core of `eq:tube-stopping-count`.  If the `s`-weights of a
finite stopping family sum to one and every contraction ratio is bounded below
by `rmin * delta`, its cardinality is at most `(rmin * delta)⁻ˢ`.

This statement is independent of a particular word representation, so both a
recursive stopping tree and an externally supplied antichain can use it. -/
theorem card_le_rpow_neg_of_sum_rpow_eq_one
    {J : Type*} [Fintype J] [Nonempty J]
    (ratio : J → ℝ) {rmin delta s : ℝ}
    (hrmin : 0 < rmin) (hdelta : 0 < delta) (hs : 0 < s)
    (hratio : ∀ j, rmin * delta ≤ ratio j)
    (hmass : ∑ j, (ratio j) ^ s = 1) :
    (Fintype.card J : ℝ) ≤ (rmin * delta) ^ (-s) := by
  have hbase : 0 < rmin * delta := mul_pos hrmin hdelta
  have hterm : ∀ j, (rmin * delta) ^ s ≤ (ratio j) ^ s := by
    intro j
    exact Real.rpow_le_rpow hbase.le (hratio j) hs.le
  have hweighted :
      (Fintype.card J : ℝ) * (rmin * delta) ^ s ≤ 1 := by
    calc
      (Fintype.card J : ℝ) * (rmin * delta) ^ s =
          ∑ _j : J, (rmin * delta) ^ s := by
            simp [nsmul_eq_mul]
      _ ≤ ∑ j : J, (ratio j) ^ s :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = 1 := hmass
  have hpowpos : 0 < (rmin * delta) ^ s := Real.rpow_pos_of_pos hbase s
  rw [Real.rpow_neg hbase.le, inv_eq_one_div]
  exact (le_div_iff₀ hpowpos).2 hweighted

end

end BrownianImages
