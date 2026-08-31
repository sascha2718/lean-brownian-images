/-
Maximal moments of the Brownian image on the unit interval.

The first part of this file builds the discrete martingale obtained by sampling
a real Brownian motion on a uniform grid.  Evaluations of `IsBrownianReal` are
only almost everywhere measurable, so we use their canonical measurable
versions.  The weak Markov property then identifies the conditional mean of
each next increment with zero.
-/
import BrownianImages.MinkowskiBrownianMaximalReduction
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ### Uniformly sampled real Brownian motion -/

/-- A measurable version of one evaluation of a real Brownian motion. -/
noncomputable def brownianEvalMk {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (t : NNReal) : Omega → Real :=
  (hB.aemeasurable t).mk (B t)

theorem stronglyMeasurable_brownianEvalMk
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (t : NNReal) :
    StronglyMeasurable (brownianEvalMk hB t) :=
  (hB.aemeasurable t).measurable_mk.stronglyMeasurable

theorem brownianEvalMk_ae_eq
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (t : NNReal) :
    brownianEvalMk hB t =ᵐ[P] B t :=
  (hB.aemeasurable t).ae_eq_mk.symm

/-- Time `n / N` in the uniform grid with denominator `N`. -/
def brownianGridTime (N n : Nat) : NNReal :=
  (n : NNReal) / (N : NNReal)

theorem brownianGridTime_mono (N : Nat) : Monotone (brownianGridTime N) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (mod_cast hij) (show 0 ≤ (N : NNReal) from bot_le)

/-- The measurable sampled process `B (n / N)`. -/
noncomputable def brownianGridSample {P : Measure Omega}
    {B : NNReal → Omega → Real} (hB : IsBrownianReal B P) (N n : Nat) :
    Omega → Real :=
  brownianEvalMk hB (brownianGridTime N n)

theorem stronglyMeasurable_brownianGridSample
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N n : Nat) :
    StronglyMeasurable (brownianGridSample hB N n) :=
  stronglyMeasurable_brownianEvalMk hB _

theorem brownianGridSample_ae_eq
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N n : Nat) :
    brownianGridSample hB N n =ᵐ[P] B (brownianGridTime N n) :=
  brownianEvalMk_ae_eq hB _

/-- The natural filtration of the uniformly sampled measurable process. -/
noncomputable def brownianGridFiltration {P : Measure Omega}
    {B : NNReal → Omega → Real} (hB : IsBrownianReal B P) (N : Nat) :
    Filtration Nat ‹MeasurableSpace Omega› :=
  Filtration.natural (brownianGridSample hB N)
    (stronglyMeasurable_brownianGridSample hB N)

private theorem brownianGridTime_add_sub (N : Nat) {i j : Nat} (hij : i ≤ j) :
    brownianGridTime N i + (brownianGridTime N j - brownianGridTime N i) =
      brownianGridTime N j := by
  rw [add_comm, tsub_add_cancel_of_le (brownianGridTime_mono N hij)]

/-- The next sampled Brownian increment is independent of all sampled values
up to the current time. -/
theorem IsBrownianReal.indepFun_brownianGridIncrement_past
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N i : Nat) :
    IndepFun
      (brownianGridSample hB N (i + 1) - brownianGridSample hB N i)
      (fun omega (k : Set.Iic i) => brownianGridSample hB N k omega) P := by
  let ti := brownianGridTime N i
  let tj := brownianGridTime N (i + 1)
  let d := tj - ti
  have htij : ti ≤ tj := brownianGridTime_mono N (Nat.le_add_right i 1)
  have hraw := hB.indepFun_shift ti
  have hcomp := hraw.comp
    (show Measurable (fun z : NNReal → Real => z d) by fun_prop)
    (show Measurable (fun z : Set.Iic ti → Real =>
      fun k : Set.Iic i => z ⟨brownianGridTime N k, brownianGridTime_mono N k.2⟩) by
      apply measurable_pi_lambda
      intro k
      exact measurable_pi_apply _)
  change IndepFun
    (fun omega => B (ti + d) omega - B ti omega)
    (fun omega (k : Set.Iic i) => B (brownianGridTime N k) omega) P at hcomp
  have hinc :
      (fun omega => B (ti + d) omega - B ti omega) =ᵐ[P]
        (brownianGridSample hB N (i + 1) - brownianGridSample hB N i) := by
    filter_upwards [brownianGridSample_ae_eq hB N (i + 1),
      brownianGridSample_ae_eq hB N i] with omega hnext hnow
    rw [show ti + d = tj from brownianGridTime_add_sub N (i := i) (j := i + 1)
      (Nat.le_add_right i 1)]
    exact congrArg₂ (· - ·) hnext.symm hnow.symm
  have hpast :
      (fun omega (k : Set.Iic i) => B (brownianGridTime N k) omega) =ᵐ[P]
        (fun omega (k : Set.Iic i) => brownianGridSample hB N k omega) := by
    exact (Filter.eventually_all.mpr fun k : Set.Iic i =>
      (brownianGridSample_ae_eq hB N k).symm).mono fun omega homega => funext homega
  exact hcomp.congr hinc hpast

/-- Uniform samples of a real Brownian motion form a discrete martingale. -/
theorem IsBrownianReal.martingale_brownianGridSample
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N : Nat) :
    Martingale (brownianGridSample hB N) (brownianGridFiltration hB N) P := by
  letI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let X := brownianGridSample hB N
  let hX : ∀ n, StronglyMeasurable (X n) :=
    stronglyMeasurable_brownianGridSample hB N
  have hadapt : StronglyAdapted (brownianGridFiltration hB N) X := by
    exact Filtration.stronglyAdapted_natural hX
  have hint : ∀ n, Integrable (X n) P := by
    intro n
    exact (hB.integrable_eval (brownianGridTime N n)).congr
      (brownianGridSample_ae_eq hB N n).symm
  apply martingale_of_condExp_sub_eq_zero_nat hadapt hint
  intro i
  let Y : Omega → Real := X (i + 1) - X i
  have hYstrong : StronglyMeasurable Y := (hX (i + 1)).sub (hX i)
  have hind := indepFun_brownianGridIncrement_past hB N i
  have hnat : brownianGridFiltration hB N i =
      MeasurableSpace.comap
        (fun omega (k : Set.Iic i) => X k omega) inferInstance := by
    exact Filtration.natural_eq_comap X hX i
  have hcond : P[Y | brownianGridFiltration hB N i] =ᵐ[P] fun _ => P[Y] := by
    rw [hnat]
    exact condExp_indep_eq hYstrong.measurable.comap_le
      (show Measurable (fun omega (k : Set.Iic i) => X k omega) by
        apply measurable_pi_lambda
        intro k
        exact (hX k).measurable).comap_le
      (comap_measurable Y).stronglyMeasurable hind
  have hmean : P[Y] = 0 := by
    have hnext := hB.integral_eval (brownianGridTime N (i + 1))
    have hnow := hB.integral_eval (brownianGridTime N i)
    dsimp only [Y]
    change (∫ omega, X (i + 1) omega - X i omega ∂P) = 0
    rw [integral_sub (hint (i + 1)) (hint i)]
    rw [integral_congr_ae (brownianGridSample_ae_eq hB N (i + 1)), hnext,
      integral_congr_ae (brownianGridSample_ae_eq hB N i), hnow, sub_self]
  exact hcond.trans (Filter.Eventually.of_forall fun _ => hmean)

/-! ### Polynomial submartingales and the finite-grid maximum -/

/-- A measurable grid evaluation has a Gaussian law. -/
theorem IsBrownianReal.hasGaussianLaw_brownianGridSample
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N n : Nat) :
    HasGaussianLaw (brownianGridSample hB N n) P :=
  (hB.hasLaw_eval (brownianGridTime N n)).hasGaussianLaw.congr
    (brownianGridSample_ae_eq hB N n).symm

/-- Every real power at least one of the absolute sampled process is a
nonnegative submartingale. -/
theorem IsBrownianReal.submartingale_abs_rpow_brownianGridSample
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N : Nat) {q : Real} (hq : 1 ≤ q) :
    Submartingale
      (fun n omega => |brownianGridSample hB N n omega| ^ q)
      (brownianGridFiltration hB N) P := by
  letI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let X := brownianGridSample hB N
  have hM := martingale_brownianGridSample hB N
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hint : ∀ n, Integrable (fun omega => |X n omega| ^ q) P := by
    intro n
    have hmem : MemLp (X n) (ENNReal.ofReal q) P :=
      (hasGaussianLaw_brownianGridSample hB N n).memLp (by simp)
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq0] using
      hmem.integrable_norm_rpow'
  have hadapt : StronglyAdapted (brownianGridFiltration hB N)
      (fun n omega => |X n omega| ^ q) := by
    intro n
    exact ((Real.continuous_rpow_const hq0).comp continuous_abs).measurable.comp
      (hM.stronglyMeasurable n).measurable |>.stronglyMeasurable
  refine ⟨hadapt, ?_, hint⟩
  intro i j hij
  have hJ := Integrable.norm_condExp_rpow_le
    (m := brownianGridFiltration hB N i) (f := X j) hq (by
    simpa only [Real.norm_eq_abs] using hint j)
  filter_upwards [hJ, hM.condExp_ae_eq hij] with omega hJomega heq
  rw [heq] at hJomega
  simpa only [Real.norm_eq_abs] using hJomega

/-- The largest absolute value among the first `N + 1` grid samples. -/
noncomputable def brownianGridMaxAbs {P : Measure Omega}
    {B : NNReal → Omega → Real} (hB : IsBrownianReal B P) (N : Nat)
    (omega : Omega) : Real :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |brownianGridSample hB N k omega|)

theorem brownianGridMaxAbs_nonneg
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N : Nat) (omega : Omega) :
    0 ≤ brownianGridMaxAbs hB N omega := by
  exact (abs_nonneg (brownianGridSample hB N 0 omega)).trans
    (Finset.le_sup' (fun k => |brownianGridSample hB N k omega|)
      (by simp : 0 ∈ Finset.range (N + 1)))

theorem measurable_brownianGridMaxAbs
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N : Nat) :
    Measurable (brownianGridMaxAbs hB N) := by
  unfold brownianGridMaxAbs
  exact Finset.measurable_range_sup'' fun k _ =>
    (stronglyMeasurable_brownianGridSample hB N k).measurable.abs

/-- Doubling a grid denominator preserves all the old grid times. -/
theorem brownianGridTime_double (N k : Nat) :
    brownianGridTime (2 * N) (2 * k) = brownianGridTime N k := by
  unfold brownianGridTime
  rw [Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_left (k : NNReal) (N : NNReal) (by norm_num)

/-- The maximum over a uniform grid increases when the grid is bisected. -/
theorem brownianGridMaxAbs_le_double
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (N : Nat) (omega : Omega) :
    brownianGridMaxAbs hB N omega ≤ brownianGridMaxAbs hB (2 * N) omega := by
  unfold brownianGridMaxAbs
  apply Finset.sup'_le Finset.nonempty_range_add_one
  intro k hk
  have hkN : k < N + 1 := Finset.mem_range.mp hk
  have h2k : 2 * k ∈ Finset.range (2 * N + 1) := by
    rw [Finset.mem_range]
    omega
  have hsamp : brownianGridSample hB (2 * N) (2 * k) =
      brownianGridSample hB N k := by
    unfold brownianGridSample
    rw [brownianGridTime_double]
  rw [← hsamp]
  exact Finset.le_sup' (fun j => |brownianGridSample hB (2 * N) j omega|) h2k

/-- Dyadic grid maxima form an increasing sequence. -/
theorem monotone_brownianDyadicGridMaxAbs
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) (omega : Omega) :
    Monotone (fun n : Nat => brownianGridMaxAbs hB (2 ^ n) omega) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [pow_succ'] using brownianGridMaxAbs_le_double hB (2 ^ n) omega

/-- Weak maximal estimate for a finite Brownian grid.  The right-hand side is
the `q`-moment of the terminal sample. -/
theorem IsBrownianReal.gridMaxAbs_weak_moment
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) {N : Nat} (hN : N ≠ 0)
    {q a : Real} (hq : 1 ≤ q) (ha : 0 < a) :
    ENNReal.ofReal (a ^ q) * P {omega | a ≤ brownianGridMaxAbs hB N omega} ≤
      ENNReal.ofReal (∫ omega, |B 1 omega| ^ q ∂P) := by
  letI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let f : Nat → Omega → Real := fun n omega => |brownianGridSample hB N n omega| ^ q
  have hsub : Submartingale f (brownianGridFiltration hB N) P :=
    submartingale_abs_rpow_brownianGridSample hB N hq
  have hfnonneg : 0 ≤ f := fun n omega => Real.rpow_nonneg (abs_nonneg _) q
  let eps : NNReal := ⟨a ^ q, Real.rpow_nonneg ha.le q⟩
  have hmax := maximal_ineq hsub hfnonneg (ε := eps) N
  have hevent : {omega | a ≤ brownianGridMaxAbs hB N omega} ⊆
      {omega | (eps : Real) ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k => f k omega)} := by
    intro omega homega
    change a ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => |brownianGridSample hB N k omega|) at homega
    change (eps : Real) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => f k omega)
    rw [Finset.le_sup'_iff] at homega ⊢
    obtain ⟨k, hk, hak⟩ := homega
    exact ⟨k, hk, Real.rpow_le_rpow ha.le hak (zero_le_one.trans hq)⟩
  have hmul : (eps : ENNReal) * P {omega | a ≤ brownianGridMaxAbs hB N omega} ≤
      ENNReal.ofReal (∫ omega in {omega | (eps : Real) ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k => f k omega)}, f N omega ∂P) := by
    exact (mul_le_mul_right (measure_mono hevent) (eps : ENNReal)).trans hmax
  have hint : Integrable (f N) P := hsub.integrable N
  have hset : (∫ omega in {omega | (eps : Real) ≤
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => f k omega)}, f N omega ∂P) ≤ ∫ omega, f N omega ∂P :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun omega => hfnonneg N omega)
  have hterminal : (fun omega => f N omega) =ᵐ[P] fun omega => |B 1 omega| ^ q := by
    have ht : brownianGridTime N N = 1 := by
      simp [brownianGridTime, hN]
    filter_upwards [brownianGridSample_ae_eq hB N N] with omega homega
    rw [ht] at homega
    simp only [f, homega]
  calc
    ENNReal.ofReal (a ^ q) * P {omega | a ≤ brownianGridMaxAbs hB N omega} =
        (eps : ENNReal) * P {omega | a ≤ brownianGridMaxAbs hB N omega} := by
      have heps : (eps : ENNReal) = ENNReal.ofReal (a ^ q) := by
        rw [ENNReal.coe_nnreal_eq]
        rfl
      rw [heps]
    _ ≤ ENNReal.ofReal (∫ omega in {omega | (eps : Real) ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k => f k omega)}, f N omega ∂P) := hmul
    _ ≤ ENNReal.ofReal (∫ omega, f N omega ∂P) := ENNReal.ofReal_le_ofReal hset
    _ = ENNReal.ofReal (∫ omega, |B 1 omega| ^ q ∂P) := by
      rw [integral_congr_ae hterminal]

/-- The same weak maximal estimate holds for the union of all dyadic grid
events.  Nestedness of the dyadic grids is what prevents a union-bound loss. -/
theorem IsBrownianReal.dyadicGridMax_iUnion_weak_moment
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) {q a : Real} (hq : 1 ≤ q) (ha : 0 < a) :
    ENNReal.ofReal (a ^ q) *
        P (⋃ n : Nat, {omega | a ≤ brownianGridMaxAbs hB (2 ^ n) omega}) ≤
      ENNReal.ofReal (∫ omega, |B 1 omega| ^ q ∂P) := by
  let E : Nat → Set Omega := fun n =>
    {omega | a ≤ brownianGridMaxAbs hB (2 ^ n) omega}
  have hEmono : Monotone E := by
    intro n m hnm omega homega
    exact homega.trans (monotone_brownianDyadicGridMaxAbs hB omega hnm)
  change ENNReal.ofReal (a ^ q) * P (⋃ n, E n) ≤ _
  rw [hEmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  exact BrownianImages.IsBrownianReal.gridMaxAbs_weak_moment hB
    (by positivity : (2 : Nat) ^ n ≠ 0) hq ha

/-- The continuous scalar path on `[0,1]` satisfies the finite-dimensional
weak maximal estimate.  Continuity identifies a strict path excursion with
an excursion on one of the nested dyadic grids. -/
theorem IsBrownianReal.pathMax_weak_moment
    {P : Measure Omega} {B : NNReal → Omega → Real}
    (hB : IsBrownianReal B P) {q a : Real} (hq : 1 ≤ q) (ha : 0 < a) :
    ENNReal.ofReal (a ^ q) *
        P {omega | ∃ t : NNReal, t ≤ 1 ∧ a < |B t omega|} ≤
      ENNReal.ofReal (∫ omega, |B 1 omega| ^ q ∂P) := by
  let E : Set Omega :=
    ⋃ n : Nat, {omega | a ≤ brownianGridMaxAbs hB (2 ^ n) omega}
  have hagree : ∀ᵐ omega ∂P, ∀ n k : Nat,
      brownianGridSample hB (2 ^ n) k omega =
        B (brownianGridTime (2 ^ n) k) omega := by
    exact ae_all_iff.mpr fun n => ae_all_iff.mpr fun k =>
      brownianGridSample_ae_eq hB (2 ^ n) k
  have hsubset : {omega | ∃ t : NNReal, t ≤ 1 ∧ a < |B t omega|} ≤ᵐ[P] E := by
    filter_upwards [hB.cont, hagree] with omega hcont homega
    rintro ⟨t, ht, hBt⟩
    let k : Nat → Nat := fun n => ⌈(2 : Real) ^ n * (t : Real)⌉₊
    have htime : Tendsto
        (fun n : Nat => ((k n : NNReal) / 2 ^ n : NNReal)) atTop (nhds t) := by
      exact JointMeasurability.tendsto_approx t
    have hval : Tendsto (fun n : Nat => |B ((k n : NNReal) / 2 ^ n) omega|)
        atTop (nhds |B t omega|) := ((hcont.tendsto t).comp htime).abs
    have hevent : ∀ᶠ n : Nat in atTop,
        a < |B ((k n : NNReal) / 2 ^ n) omega| :=
      hval.eventually (isOpen_Ioi.mem_nhds hBt)
    obtain ⟨n, hn⟩ := hevent.exists
    have hkn : k n ≤ 2 ^ n := by
      apply Nat.ceil_le.mpr
      calc
        (2 : Real) ^ n * (t : Real) ≤ (2 : Real) ^ n * 1 := by
          gcongr
          exact_mod_cast ht
        _ = ((2 ^ n : Nat) : Real) := by norm_num
    have hkmem : k n ∈ Finset.range (2 ^ n + 1) := by
      rw [Finset.mem_range]
      omega
    have hsample : a < |brownianGridSample hB (2 ^ n) (k n) omega| := by
      rw [homega n (k n)]
      simpa only [brownianGridTime, Nat.cast_pow, Nat.cast_ofNat] using hn
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    exact hsample.le.trans
      (Finset.le_sup' (fun j => |brownianGridSample hB (2 ^ n) j omega|) hkmem)
  exact (mul_le_mul_right (measure_mono_ae hsubset) _).trans
    (BrownianImages.IsBrownianReal.dyadicGridMax_iUnion_weak_moment hB hq ha)

/-! ### From the two scalar coordinates to the compact planar radius -/

/-- The Euclidean norm in the plane is bounded by the sum of the absolute
values of the two coordinates. -/
theorem plane_norm_le_abs_add (x : Plane) :
    ‖x‖ ≤ |x 0| + |x 1| := by
  have hs := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_two] at hs
  have hs0 : (x 0) ^ 2 = |x 0| ^ 2 := by rw [sq_abs]
  have hs1 : (x 1) ^ 2 = |x 1| ^ 2 := by rw [sq_abs]
  have hn : 0 ≤ ‖x‖ := norm_nonneg x
  have h0 : 0 ≤ |x 0| := abs_nonneg _
  have h1 : 0 ≤ |x 1| := abs_nonneg _
  nlinarith [mul_nonneg h0 h1]

/-- A uniform bound on a continuous path over `[0,1]` bounds the Hausdorff
radius of its compact image. -/
theorem standardBrownianRadius_le_of_continuous
    {W : NNReal → Omega → Plane} {omega : Omega} {R : Real}
    (hcont : Continuous (fun t => W t omega)) (hR : 0 ≤ R)
    (hbound : ∀ t : NNReal, t ≤ 1 → ‖W t omega‖ ≤ R) :
    standardBrownianRadius W omega ≤ R := by
  rw [standardBrownianRadius, compactRadius]
  change Metric.hausdorffDist (standardBrownianPiece W omega : Set Plane)
    ({0} : Set Plane) ≤ R
  apply Metric.hausdorffDist_le_of_mem_dist hR
  · intro x hx
    rw [standardBrownianPiece,
      coe_brownianImage_of_continuous unitIntervalCompact hcont] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨0, by simp, ?_⟩
    rw [dist_zero_right]
    exact hbound t.toNNReal (Real.toNNReal_le_one.mpr ht.2)
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨W 0 omega, ?_, ?_⟩
    · rw [standardBrownianPiece,
        coe_brownianImage_of_continuous unitIntervalCompact hcont]
      exact ⟨0, by simp, by simp⟩
    · simpa only [dist_zero_left] using hbound 0 (by norm_num)

/-- A strict excursion of the compact planar radius forces a strict
excursion, at half the height, of at least one scalar coordinate. -/
theorem IsPlanarBrownian.radius_excursion_ae_subset_coordinate_excursions
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) {a : Real} (ha : 0 < a) :
    {omega | a < standardBrownianRadius W omega} ≤ᵐ[P]
      ((({omega : Omega | ∃ t : NNReal,
          t ≤ 1 ∧ a / 2 < |W t omega 0|} : Set Omega) ∪
        ({omega : Omega | ∃ t : NNReal,
          t ≤ 1 ∧ a / 2 < |W t omega 1|} : Set Omega)) : Set Omega) := by
  filter_upwards [hW.ae_continuous] with omega hcont
  intro homega
  change (∃ t : NNReal, t ≤ 1 ∧ a / 2 < |W t omega 0|) ∨
    (∃ t : NNReal, t ≤ 1 ∧ a / 2 < |W t omega 1|)
  by_contra hcoord
  push Not at hcoord
  have hbound : ∀ t : NNReal, t ≤ 1 → ‖W t omega‖ ≤ a := by
    intro t ht
    calc
      ‖W t omega‖ ≤ |W t omega 0| + |W t omega 1| :=
        plane_norm_le_abs_add _
      _ ≤ a / 2 + a / 2 := add_le_add (hcoord.1 t ht) (hcoord.2 t ht)
      _ = a := by ring
  exact (not_lt_of_ge (standardBrownianRadius_le_of_continuous hcont ha.le hbound)) homega

/-- Polynomial weak tail for the compact planar Brownian image.  The factor
`2 ^ q` only records the elementary reduction to its two coordinates. -/
theorem IsPlanarBrownian.standardBrownianRadius_weak_moment
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) {q a : Real} (hq : 1 ≤ q) (ha : 0 < a) :
    ENNReal.ofReal (a ^ q) * P {omega | a < standardBrownianRadius W omega} ≤
      ENNReal.ofReal
        (2 ^ q * ((∫ omega, |W 1 omega 0| ^ q ∂P) +
          ∫ omega, |W 1 omega 1| ^ q ∂P)) := by
  let E0 : Set Omega :=
    {omega | ∃ t : NNReal, t ≤ 1 ∧ a / 2 < |W t omega 0|}
  let E1 : Set Omega :=
    {omega | ∃ t : NNReal, t ≤ 1 ∧ a / 2 < |W t omega 1|}
  let I0 : Real := ∫ omega, |W 1 omega 0| ^ q ∂P
  let I1 : Real := ∫ omega, |W 1 omega 1| ^ q ∂P
  have hI0 : 0 ≤ I0 := integral_nonneg fun omega =>
    Real.rpow_nonneg (abs_nonneg _) q
  have hI1 : 0 ≤ I1 := integral_nonneg fun omega =>
    Real.rpow_nonneg (abs_nonneg _) q
  have h2q : 0 ≤ (2 : Real) ^ q := Real.rpow_nonneg (by norm_num) q
  have hhalfq : 0 ≤ (a / 2) ^ q :=
    Real.rpow_nonneg (div_nonneg ha.le (by norm_num)) q
  have hpow : (a / 2) ^ q * 2 ^ q = a ^ q := by
    rw [← Real.mul_rpow (div_nonneg ha.le (by norm_num)) (by norm_num)]
    congr 1
    ring
  have hcoef : ENNReal.ofReal (a ^ q) =
      ENNReal.ofReal (2 ^ q) * ENNReal.ofReal ((a / 2) ^ q) := by
    rw [← ENNReal.ofReal_mul h2q, mul_comm, hpow]
  have h0 : ENNReal.ofReal ((a / 2) ^ q) * P E0 ≤ ENNReal.ofReal I0 := by
    exact BrownianImages.IsBrownianReal.pathMax_weak_moment (hW.coord 0) hq (half_pos ha)
  have h1 : ENNReal.ofReal ((a / 2) ^ q) * P E1 ≤ ENNReal.ofReal I1 := by
    exact BrownianImages.IsBrownianReal.pathMax_weak_moment (hW.coord 1) hq (half_pos ha)
  have hsubset : P {omega | a < standardBrownianRadius W omega} ≤ P (E0 ∪ E1) :=
    measure_mono_ae (hW.radius_excursion_ae_subset_coordinate_excursions ha)
  calc
    ENNReal.ofReal (a ^ q) * P {omega | a < standardBrownianRadius W omega} ≤
        ENNReal.ofReal (a ^ q) * P (E0 ∪ E1) := by gcongr
    _ ≤ ENNReal.ofReal (a ^ q) * (P E0 + P E1) := by
      gcongr
      exact measure_union_le E0 E1
    _ = ENNReal.ofReal (2 ^ q) *
        (ENNReal.ofReal ((a / 2) ^ q) * P E0 +
          ENNReal.ofReal ((a / 2) ^ q) * P E1) := by
      rw [hcoef]
      ring
    _ ≤ ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal I0 + ENNReal.ofReal I1) := by
      gcongr
    _ = ENNReal.ofReal (2 ^ q * (I0 + I1)) := by
      rw [ENNReal.ofReal_mul h2q, ENNReal.ofReal_add hI0 hI1]
    _ = ENNReal.ofReal
        (2 ^ q * ((∫ omega, |W 1 omega 0| ^ q ∂P) +
          ∫ omega, |W 1 omega 1| ^ q ∂P)) := rfl

/-! ### From a weak higher moment to a strong lower moment -/

/-- A polynomial weak-tail estimate of order `q` implies every strictly
smaller positive moment.  This is the tail-integral argument, split at one so
that no negative power is used near zero. -/
theorem integrable_rpow_of_weak_tail
    {P : Measure Omega} [IsProbabilityMeasure P] {f : Omega → Real}
    (hf : AEMeasurable f P) (hf0 : 0 ≤ᵐ[P] f)
    {p q A : Real} (hp : 0 < p) (hpq : p < q) (hA : 0 ≤ A)
    (htail : ∀ a : Real, 0 < a →
      ENNReal.ofReal (a ^ q) * P {omega | a < f omega} ≤ ENNReal.ofReal A) :
    Integrable (fun omega => f omega ^ p) P := by
  let F : Real → ENNReal := fun t =>
    P {omega | t < f omega} * ENNReal.ofReal (t ^ (p - 1))
  have hsmall_int : IntegrableOn (fun t : Real => t ^ (p - 1)) (Ioc 0 1) := by
    refine IntegrableOn.congr_set_ae (t := Ioo 0 1) ?_
      (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
    linarith
  have hsmall : (∫⁻ t in Ioc (0 : Real) 1, F t) < ∞ := by
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc ?_)
      hsmall_int.lintegral_lt_top
    intro t ht
    dsimp only [F]
    calc
      P {omega | t < f omega} * ENNReal.ofReal (t ^ (p - 1)) ≤
          1 * ENNReal.ofReal (t ^ (p - 1)) := by
        gcongr
        calc
          P {omega | t < f omega} ≤ P Set.univ := measure_mono (subset_univ _)
          _ = 1 := measure_univ
      _ = ENNReal.ofReal (t ^ (p - 1)) := one_mul _
  have hlarge_int : IntegrableOn
      (fun t : Real => A * t ^ (p - q - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul A
  have hlarge : (∫⁻ t in Ioi (1 : Real), F t) < ∞ := by
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi ?_)
      hlarge_int.lintegral_lt_top
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hpow : t ^ q * t ^ (p - q - 1) = t ^ (p - 1) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    dsimp only [F]
    calc
      P {omega | t < f omega} * ENNReal.ofReal (t ^ (p - 1)) =
          (ENNReal.ofReal (t ^ q) * P {omega | t < f omega}) *
            ENNReal.ofReal (t ^ (p - q - 1)) := by
        rw [← hpow, ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le q)]
        ac_rfl
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (t ^ (p - q - 1)) := by
        gcongr
        exact htail t ht0
      _ = ENNReal.ofReal (A * t ^ (p - q - 1)) := by
        rw [ENNReal.ofReal_mul hA]
  have htail_int : (∫⁻ t in Ioi (0 : Real), F t) < ∞ := by
    have hsplit : Ioi (0 : Real) = Ioc 0 1 ∪ Ioi 1 := by
      ext t
      simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro ht
        by_cases h : t ≤ 1
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr (lt_of_not_ge h)
      · rintro (⟨ht, _⟩ | ht)
        · exact ht
        · exact zero_lt_one.trans ht
    have hdisj : Disjoint (Ioc (0 : Real) 1) (Ioi 1) := by
      exact Set.disjoint_left.2 fun _ hx hy => (not_lt_of_ge hx.2) hy
    rw [hsplit, lintegral_union measurableSet_Ioi hdisj]
    exact ENNReal.add_lt_top.2 ⟨hsmall, hlarge⟩
  have hmoment : (∫⁻ omega, ENNReal.ofReal (f omega ^ p) ∂P) < ∞ := by
    rw [lintegral_rpow_eq_lintegral_meas_lt_mul P hf0 hf hp]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top htail_int
  refine ⟨?_, ?_⟩
  · have hm : AEMeasurable ((fun x : Real => x ^ p) ∘ f) P :=
      (Real.continuous_rpow_const hp.le).measurable.comp_aemeasurable hf
    change AEStronglyMeasurable ((fun x : Real => x ^ p) ∘ f) P
    exact hm.aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_norm]
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hmoment
    filter_upwards [hf0] with omega homega
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg homega p)]

/-! ### The unit-interval Brownian maximal moment -/

/-- Every positive real moment of the radius of the compact Brownian image
over `[0,1]` is finite. -/
theorem IsPlanarBrownian.integrable_standardBrownianRadius_rpow
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) {p : Real} (hp : 0 < p) :
    Integrable (fun omega => standardBrownianRadius W omega ^ p) P := by
  letI : IsProbabilityMeasure P :=
    (hW.coord 0).isGaussianProcess.isProbabilityMeasure
  let q : Real := p + 1
  let A : Real :=
    2 ^ q * ((∫ omega, |W 1 omega 0| ^ q ∂P) +
      ∫ omega, |W 1 omega 1| ^ q ∂P)
  have hA : 0 ≤ A := by
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) q)
    exact add_nonneg
      (integral_nonneg fun omega => Real.rpow_nonneg (abs_nonneg _) q)
      (integral_nonneg fun omega => Real.rpow_nonneg (abs_nonneg _) q)
  apply integrable_rpow_of_weak_tail (q := q) (A := A)
    (hW.aemeasurable_standardBrownianRadius)
    (Filter.Eventually.of_forall fun omega =>
      compactRadius_nonneg (standardBrownianPiece W omega)) hp (by
      dsimp [q]
      linarith) hA
  intro a ha
  exact BrownianImages.IsPlanarBrownian.standardBrownianRadius_weak_moment hW
    (q := q) (by dsimp [q]; linarith) ha

/-- The precise unit-interval input required by the Minkowski-tube assembly:
for every real `p ≥ 1`, `(1 + R)^p` has finite expectation, where `R` is the
Hausdorff radius of the Brownian image of `[0,1]`. -/
theorem IsPlanarBrownian.integrable_one_add_standardBrownianRadius_rpow
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) {p : Real} (hp : 1 ≤ p) :
    Integrable (fun omega => (1 + standardBrownianRadius W omega) ^ p) P := by
  letI : IsProbabilityMeasure P :=
    (hW.coord 0).isGaussianProcess.isProbabilityMeasure
  let a : Fin 2 → Omega → Real := fun j omega =>
    if j = 0 then 1 else standardBrownianRadius W omega
  have haemeas : ∀ j, AEMeasurable (a j) P := by
    intro j
    fin_cases j
    · simp [a]
    · simpa [a] using
        hW.aemeasurable_standardBrownianRadius
  have ha : ∀ j omega, 0 ≤ a j omega := by
    intro j omega
    fin_cases j
    · simp [a]
    · simpa [a, standardBrownianRadius] using
        compactRadius_nonneg (standardBrownianPiece W omega)
  have hint : ∀ j, Integrable (fun omega => a j omega ^ p) P := by
    intro j
    fin_cases j
    · simp [a]
    · simpa [a] using hW.integrable_standardBrownianRadius_rpow
        (lt_of_lt_of_le zero_lt_one hp)
  have hsum := integrable_rpow_sum_and_integral_le a hp haemeas ha hint
  simpa [Fin.sum_univ_two, a, add_comm] using hsum.1

end

end BrownianImages
