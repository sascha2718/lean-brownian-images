/-
`thm:profile-asymptotics` of `sec:smoothing`: the two asymptotics of the expected
profile, `eq:hb-asymptotic` in the non-lattice case and `eq:ha-asymptotic` in the
lattice case.

* `profile_asymptotics_nonLattice`: dominated convergence against `A·K`.
* `exists_lattice_bound`: the uniform bound behind `eq:ha-asymptotic`, at any exponent.
  The two integrands agree where `2v - log η ≥ log 3`, and on the rest `K(η) ≤ ½η^{s-2}`,
  which integrates to `T^{s-1}/(1-s)` with `T = e^{2v - log 3}`.
* `profile_asymptotics_lattice`, `profile_asymptotics_lattice_bigO`: the two shapes.

Neither lattice statement needs a Frostman hypothesis on `μ_A`: boundedness of `G` comes
from `hagree` above `log 3` and `Φ ≤ 1` below it, and measurability from monotonicity
of `Φ`.
-/
import BrownianImages.Profile
import BrownianImages.Kernel
import BrownianImages.Cantor
import BrownianImages.SelfSimilar

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

/-! ### `eq:hb-asymptotic`: the non-lattice limit -/

/-- `thm:profile-asymptotics`, `eq:hb-asymptotic`: if `G` has the finite positive limit
`C`, then `H` has the finite positive limit `C ∫₀^∞ K`.  Dominated convergence with the
dominating function `A·K`, since `2v - log η → ∞` for every fixed `η > 0`. -/
theorem profile_asymptotics_nonLattice {s C : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {A : ℝ} (hμ : IsFrostman s A μ)
    (hCpos : 0 < C) (hC : Tendsto (G s μ) atTop (𝓝 C)) :
    0 < C * ∫ η in Set.Ioi (0:ℝ), kern s η ∧
      Tendsto (H s μ) atTop (𝓝 (C * ∫ η in Set.Ioi (0:ℝ), kern s η)) := by
  refine ⟨mul_pos hCpos (integral_kern_pos hs0 hs1), ?_⟩
  have hkint := kern_integrableOn (s := s) hs0 hs1
  have hGm : Measurable (G s μ) := measurable_G
  have hkey : Tendsto
      (fun v : ℝ => ∫ η in Set.Ioi (0:ℝ), kern s η * G s μ (2 * v - Real.log η))
      atTop (𝓝 (∫ η in Set.Ioi (0:ℝ), kern s η * C)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun η => A * kern s η)
      (Eventually.of_forall fun v => ?_) (Eventually.of_forall fun v => ?_)
      (hkint.const_mul A) ?_
    · exact ((continuousOn_kern s).aestronglyMeasurable measurableSet_Ioi).mul
        (hGm.comp (measurable_const.sub Real.measurable_log)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
      have hk : (0:ℝ) ≤ kern s η := (kern_pos (s := s) hη).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
      calc kern s η * |G s μ (2 * v - Real.log η)| ≤ kern s η * A :=
            mul_le_mul_of_nonneg_left (abs_G_le hs0 hμ _) hk
        _ = A * kern s η := mul_comm _ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
      have htop : Tendsto (fun v : ℝ => 2 * v - Real.log η) atTop atTop := by
        have h : Tendsto (fun v : ℝ => 2 * v + -Real.log η) atTop atTop :=
          tendsto_atTop_add_const_right _ _
            (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
        simpa [sub_eq_add_neg] using h
      exact (hC.comp htop).const_mul (kern s η)
  have hval : ∫ η in Set.Ioi (0:ℝ), kern s η * C = C * ∫ η in Set.Ioi (0:ℝ), kern s η := by
    rw [integral_mul_const, mul_comm]
  rw [hval] at hkey
  exact hkey.congr fun v => rfl

/-! ### `eq:ha-asymptotic`: the lattice bound -/

/-- A continuous periodic function is bounded, in the shape the estimate uses. -/
theorem exists_nonneg_bound_of_periodic {g : ℝ → ℝ} {p : ℝ} (hp : p ≠ 0) (hg : Continuous g)
    (hper : Function.Periodic g p) : ∃ M : ℝ, 0 ≤ M ∧ ∀ w, |g w| ≤ M := by
  have hcomp := hper.compact_of_continuous hp hg
  obtain ⟨a, ha⟩ := hcomp.bddAbove
  obtain ⟨b, hb⟩ := hcomp.bddBelow
  have hgub : ∀ w, g w ≤ a := fun w => ha (Set.mem_range_self w)
  have hglb : ∀ w, b ≤ g w := fun w => hb (Set.mem_range_self w)
  refine ⟨max a (-b), ?_, fun w => abs_le.mpr ⟨?_, ?_⟩⟩
  · rcases le_total (0:ℝ) a with h | h
    · exact h.trans (le_max_left _ _)
    · have h1 := hglb 0
      have h2 := hgub 0
      have : (0:ℝ) ≤ -b := by linarith
      exact this.trans (le_max_right _ _)
  · have h1 := hglb w
    have h2 : -b ≤ max a (-b) := le_max_right _ _
    linarith
  · exact (hgub w).trans (le_max_left _ _)

/-- The uniform bound behind `eq:ha-asymptotic`, for a general exponent and period: if `g` is a
continuous `p`-periodic function agreeing with `G` above `a`, then the expected
profile and the smoothed periodic profile differ by `O(e^{-2(1-s)v})`.  The two
integrands agree where `2v - log η ≥ a`, and on the remaining range
`η > e^{2v-a}` the kernel is at most `½ η^{s-2}`. -/
theorem exists_lattice_bound {s a p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {g : ℝ → ℝ} (hg : Continuous g)
    (hp : p ≠ 0) (hper : Function.Periodic g p)
    (hagree : ∀ w, a ≤ w → g w = G s μ w) :
    ∃ C > 0, ∀ v : ℝ, |H s μ v - smoothOp s g v| ≤ C * Real.exp (-2 * (1 - s) * v) := by
  have h1s : (0:ℝ) < 1 - s := by linarith
  obtain ⟨Mg, hMg0, hMg⟩ := exists_nonneg_bound_of_periodic hp hg hper
  set MG := Real.exp (s * a) + Mg with hMGdef
  have hGbd : ∀ w, |G s μ w| ≤ MG := by
    intro w
    rw [abs_of_nonneg (G_nonneg w)]
    rcases le_total w a with hw | hw
    · have := G_le_exp (μ := μ) hs0.le hw
      simp only [hMGdef]
      linarith
    · rw [← hagree w hw]
      have h1 : g w ≤ Mg := (le_abs_self _).trans (hMg w)
      have h2 : (0:ℝ) < Real.exp (s * a) := Real.exp_pos _
      simp only [hMGdef]
      linarith
  set B := MG + Mg with hBdef
  have hB0 : 0 < B := by
    have h2 : (0:ℝ) < Real.exp (s * a) := Real.exp_pos _
    simp only [hBdef, hMGdef]
    linarith
  have hdiff : ∀ w, |G s μ w - g w| ≤ B := by
    intro w
    have h1 := abs_le.mp (hGbd w)
    have h2 := abs_le.mp (hMg w)
    rw [abs_le, hBdef]
    constructor <;> linarith
  have hkint := kern_integrableOn (s := s) hs0 hs1
  have hGm : Measurable (G s μ) := measurable_G
  have hmeas1 : ∀ v : ℝ, AEStronglyMeasurable
      (fun η : ℝ => kern s η * G s μ (2 * v - Real.log η))
      (volume.restrict (Set.Ioi (0:ℝ))) := fun v =>
    ((continuousOn_kern s).aestronglyMeasurable measurableSet_Ioi).mul
      (hGm.comp (measurable_const.sub Real.measurable_log)).aestronglyMeasurable
  have hmeas2 : ∀ v : ℝ, AEStronglyMeasurable
      (fun η : ℝ => kern s η * g (2 * v - Real.log η))
      (volume.restrict (Set.Ioi (0:ℝ))) := fun v =>
    ((continuousOn_kern s).aestronglyMeasurable measurableSet_Ioi).mul
      (hg.measurable.comp (measurable_const.sub Real.measurable_log)).aestronglyMeasurable
  have hint1 : ∀ v : ℝ, IntegrableOn
      (fun η : ℝ => kern s η * G s μ (2 * v - Real.log η)) (Set.Ioi 0) := by
    intro v
    refine Integrable.mono' (hkint.const_mul MG) (hmeas1 v) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
    have hk : (0:ℝ) ≤ kern s η := (kern_pos (s := s) hη).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc kern s η * |G s μ (2 * v - Real.log η)| ≤ kern s η * MG :=
          mul_le_mul_of_nonneg_left (hGbd _) hk
      _ = MG * kern s η := mul_comm _ _
  have hint2 : ∀ v : ℝ, IntegrableOn
      (fun η : ℝ => kern s η * g (2 * v - Real.log η)) (Set.Ioi 0) := by
    intro v
    refine Integrable.mono' (hkint.const_mul Mg) (hmeas2 v) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
    have hk : (0:ℝ) ≤ kern s η := (kern_pos (s := s) hη).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc kern s η * |g (2 * v - Real.log η)| ≤ kern s η * Mg :=
          mul_le_mul_of_nonneg_left (hMg _) hk
      _ = Mg * kern s η := mul_comm _ _
  refine ⟨B * Real.exp ((1 - s) * a) / (2 * (1 - s)),
    div_pos (mul_pos hB0 (Real.exp_pos _)) (by linarith), fun v => ?_⟩
  set T := Real.exp (2 * v - a) with hTdef
  have hT : (0:ℝ) < T := Real.exp_pos _
  have hDint : IntegrableOn
      (fun η : ℝ => kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η)))
      (Set.Ioi 0) := by
    have h := (hint1 v).sub (hint2 v)
    refine h.congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [Pi.sub_apply]
    ring
  have hsub : H s μ v - smoothOp s g v
      = ∫ η in Set.Ioi (0:ℝ),
          kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η)) := by
    rw [H, smoothOp, ← integral_sub (hint1 v) (hint2 v)]
    refine setIntegral_congr_fun measurableSet_Ioi fun η _ => ?_
    ring
  have hzero : ∀ η ∈ Set.Ioc (0:ℝ) T,
      kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η)) = 0 := by
    intro η hη
    have hlog : Real.log η ≤ 2 * v - a := by
      have h := Real.log_le_log hη.1 hη.2
      rwa [hTdef, Real.log_exp] at h
    rw [hagree _ (by linarith : a ≤ 2 * v - Real.log η)]
    ring
  have hsplit : ∫ η in Set.Ioi (0:ℝ),
        kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η))
      = ∫ η in Set.Ioi T,
        kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η)) := by
    have hunion : Set.Ioc (0:ℝ) T ∪ Set.Ioi T = Set.Ioi (0:ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi hT.le
    have hdisj : Disjoint (Set.Ioc (0:ℝ) T) (Set.Ioi T) :=
      Set.disjoint_left.mpr fun x hx hx' => absurd hx' (not_lt.mpr hx.2)
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
      (hDint.mono_set (by rw [← hunion]; exact Set.subset_union_left))
      (hDint.mono_set (by rw [← hunion]; exact Set.subset_union_right)),
      setIntegral_eq_zero_of_forall_eq_zero hzero, zero_add]
  rw [hsub, hsplit]
  have hbint : IntegrableOn (fun η : ℝ => B * (2⁻¹ * η ^ (s - 2))) (Set.Ioi T) :=
    ((integrableOn_Ioi_rpow_of_lt (by linarith : s - 2 < -1) hT).const_mul 2⁻¹).const_mul B
  have hbound : |∫ η in Set.Ioi T,
        kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η))|
      ≤ ∫ η in Set.Ioi T, B * (2⁻¹ * η ^ (s - 2)) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun η => norm_nonneg _) hbint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
    have hη0 : (0:ℝ) < η := hT.trans hη
    have hk : (0:ℝ) ≤ kern s η := (kern_pos (s := s) hη0).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc kern s η * |G s μ (2 * v - Real.log η) - g (2 * v - Real.log η)|
        ≤ kern s η * B := mul_le_mul_of_nonneg_left (hdiff _) hk
      _ ≤ (2⁻¹ * η ^ (s - 2)) * B := mul_le_mul_of_nonneg_right (kern_le_rpow hη0) hB0.le
      _ = B * (2⁻¹ * η ^ (s - 2)) := by ring
  refine hbound.trans (le_of_eq ?_)
  have hconst : ∫ η in Set.Ioi T, B * (2⁻¹ * η ^ (s - 2))
      = (B * 2⁻¹) * ∫ η in Set.Ioi T, η ^ (s - 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun η _ => ?_
    ring
  have hTrpow : T ^ (s - 2 + 1) = Real.exp ((1 - s) * a) *
      Real.exp (-2 * (1 - s) * v) := by
    rw [hTdef, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hconst, integral_Ioi_rpow_of_lt (by linarith : s - 2 < -1) hT, hTrpow]
  have hne : s - 2 + 1 ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- `thm:profile-asymptotics`, `eq:ha-asymptotic`, as the uniform bound the proof
produces. -/
theorem profile_asymptotics_lattice {KA : Set ℝ} {μA : Measure ℝ}
    (hA : cantorSystem.IsNatural KA sCantor μA)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g (Real.log 3))
    (hagree : ∀ w, Real.log 3 ≤ w → g w = G sCantor μA w) :
    ∃ C > 0, ∀ v : ℝ, 0 ≤ v →
      |H sCantor μA v - smoothOp sCantor g v|
        ≤ C * Real.exp (-2 * (1 - sCantor) * v) := by
  haveI := hA.isProbabilityMeasure
  obtain ⟨C, hC0, hCbd⟩ :=
    exists_lattice_bound sCantor_pos sCantor_lt_one (μ := μA) hg log_three_pos.ne' hper hagree
  exact ⟨C, hC0, fun v _ => hCbd v⟩

/-- `eq:ha-asymptotic` in the asymptotic shape the paper writes it. -/
theorem profile_asymptotics_lattice_bigO {KA : Set ℝ} {μA : Measure ℝ}
    (hA : cantorSystem.IsNatural KA sCantor μA)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g (Real.log 3))
    (hagree : ∀ w, Real.log 3 ≤ w → g w = G sCantor μA w) :
    (fun v => H sCantor μA v - smoothOp sCantor g v)
      =O[atTop] fun v => Real.exp (-2 * (1 - sCantor) * v) := by
  haveI := hA.isProbabilityMeasure
  obtain ⟨C, hC0, hCbd⟩ :=
    exists_lattice_bound sCantor_pos sCantor_lt_one (μ := μA) hg log_three_pos.ne' hper hagree
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun v => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hCbd v

end BrownianImages
