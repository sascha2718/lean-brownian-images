/-
Internal proof infrastructure for `sec:renewal`: the natural measure of a strongly
separated self-similar system is Ahlfors regular of its similarity dimension.

The proof of the paper cuts the coding tree at the first level where the piece diameter
drops below the radius.  The formalisation runs the same cut one step at a time.  Below
the separation gap a ball of radius `r` meets at most one first-level piece `S_i K`, so
Hutchinson's identity collapses to a single term
`μ(B̄(x,r)) = r_i^s μ(B̄(S_i⁻¹x, r/r_i))`, and the radius grows by a factor at least
`1/max_i r_i > 1`.  Iterating until the radius reaches `ρ/2` is the stopping antichain,
and it needs no counting: the upper bound comes from `μ ≤ 1` at the stopping scale and
the lower bound from a uniform lower bound at the stopping scale, which compactness of
the support supplies.

* `AhlforsRegular.pre`, `AhlforsRegular.dist_map`: the inverse similarity and the exact
  scaling of distances under `S_i`.
* `AhlforsRegular.measure_eq_sum`: Hutchinson's identity evaluated on a set.
* `AhlforsRegular.exists_unique_meet`: below the gap a ball of positive mass meets
  exactly one piece of the attractor.
* `AhlforsRegular.measure_closedBall_step`, `AhlforsRegular.charged_pre`: the one-step
  recursion and the propagation of the support condition through it.
* `AhlforsRegular.exists_uniform_lower`: the mass of a fixed ball is bounded below
  uniformly over centres in the support, by compactness of the support.
* `AhlforsRegular.measure_closedBall_le_of_isNatural`: the upper Ahlfors bound, with
  the explicit constant `(2/ρ)^s`.
* `AhlforsRegular.exists_le_measure_closedBall_of_isNatural`: the lower half of
  the Ahlfors estimate.
* `AhlforsRegular.exists_isFrostman_of_isNatural`: the same upper bound read as
  `eq:frostman`, which is the Frostman hypothesis the later endpoints ask of `μ_A` and
  `μ_B`.
* `exists_isAhlforsClosed`: the internal endpoint `audit_ahlfors`.
* `exists_isAhlfors_homogeneous_pair`: the corresponding result for `μ_A` and `μ_B`, the
  internal endpoint `audit_ahlfors_named`.
-/
import BrownianImages.SelfSimilar
import BrownianImages.Frostman

namespace BrownianImages

open MeasureTheory
open scoped ENNReal NNReal

namespace AhlforsRegular

variable {ι : Type*} [Fintype ι] {S : System ι} {K : Set ℝ} {ρ s : ℝ} {μ : Measure ℝ}

/-- The points charging every ball, that is the support of `μ`.  This is the hypothesis
`IsAhlforsClosed` puts on the centre. -/
def Charged (μ : Measure ℝ) : Set ℝ := {x : ℝ | ∀ ε > 0, μ (Metric.ball x ε) ≠ 0}

/-- The centre of the preimage ball: `S_i⁻¹(x) = (x - b_i)/r_i`. -/
noncomputable def pre (S : System ι) (i : ι) (x : ℝ) : ℝ := (x - S.shift i) / S.ratio i

/-- `S_i` scales distances by `r_i`. -/
theorem dist_map (S : System ι) (i : ι) (x y : ℝ) :
    dist (S.map i y) x = S.ratio i * dist y (pre S i x) := by
  have hri := S.ratio_pos i
  rw [Real.dist_eq, Real.dist_eq, ← abs_of_pos hri, ← abs_mul]
  congr 1
  simp only [System.map, pre]
  field_simp
  ring

/-- The preimage of a closed ball under `S_i` is the closed ball of radius `r/r_i`. -/
theorem preimage_closedBall (S : System ι) (i : ι) (x r : ℝ) :
    S.map i ⁻¹' Metric.closedBall x r = Metric.closedBall (pre S i x) (r / S.ratio i) := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_map,
    le_div_iff₀ (S.ratio_pos i)]
  rw [mul_comm]

/-- The preimage of an open ball under `S_i` is the open ball of radius `r/r_i`. -/
theorem preimage_ball (S : System ι) (i : ι) (x r : ℝ) :
    S.map i ⁻¹' Metric.ball x r = Metric.ball (pre S i x) (r / S.ratio i) := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_map, lt_div_iff₀ (S.ratio_pos i)]
  rw [mul_comm]

/-- Hutchinson's identity evaluated on a measurable set. -/
theorem measure_eq_sum (hμ : S.IsNatural K s μ) {A : Set ℝ} (hA : MeasurableSet A) :
    μ A = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * μ (S.map i ⁻¹' A) := by
  conv_lhs => rw [hμ.selfSimilar]
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (S.measurable_map i) hA]

/-- A set missing the piece `S_i K` pulls back to a null set. -/
theorem measure_preimage_eq_zero (hμ : S.IsNatural K s μ) (i : ι) {A : Set ℝ}
    (h : S.map i '' K ∩ A = ∅) : μ (S.map i ⁻¹' A) = 0 := by
  refine measure_mono_null (fun y hy => ?_) hμ.support
  intro hyK
  exact Set.eq_empty_iff_forall_notMem.mp h (S.map i y) ⟨⟨y, hyK, rfl⟩, hy⟩

/-- Below the separation gap a ball meets at most one piece of the attractor. -/
theorem eq_of_meet (hsep : S.StronglySeparated K ρ) {x r : ℝ} (h2r : 2 * r < ρ) {i j : ι}
    (hi : (S.map i '' K ∩ Metric.closedBall x r).Nonempty)
    (hj : (S.map j '' K ∩ Metric.closedBall x r).Nonempty) : i = j := by
  by_contra hij
  obtain ⟨a, ⟨u, hu, rfl⟩, ha⟩ := hi
  obtain ⟨b, ⟨v, hv, rfl⟩, hb⟩ := hj
  have hsp := hsep.2 i j hij u hu v hv
  rw [Metric.mem_closedBall, Real.dist_eq] at ha hb
  have htri : |S.map i u - S.map j v| ≤ |S.map i u - x| + |x - S.map j v| :=
    abs_sub_le _ _ _
  rw [abs_sub_comm x (S.map j v)] at htri
  linarith

/-- Below the separation gap a ball of positive mass meets exactly one piece. -/
theorem exists_unique_meet (hsep : S.StronglySeparated K ρ) (hμ : S.IsNatural K s μ)
    {x r : ℝ} (h2r : 2 * r < ρ) (hpos : μ (Metric.closedBall x r) ≠ 0) :
    ∃ i : ι, ∀ j : ι, j ≠ i → S.map j '' K ∩ Metric.closedBall x r = ∅ := by
  by_cases hex : ∃ i : ι, (S.map i '' K ∩ Metric.closedBall x r).Nonempty
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, fun j hj => ?_⟩
    by_contra hjne
    exact hj (eq_of_meet hsep h2r (Set.nonempty_iff_ne_empty.mpr hjne) hi)
  · refine absurd ?_ hpos
    rw [measure_eq_sum hμ measurableSet_closedBall]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : S.map i '' K ∩ Metric.closedBall x r = ∅ := by
      by_contra hi
      exact hex ⟨i, Set.nonempty_iff_ne_empty.mpr hi⟩
    rw [measure_preimage_eq_zero hμ i hi, mul_zero]

/-- The one-step recursion of the stopping construction, on closed balls. -/
theorem measure_closedBall_step (hμ : S.IsNatural K s μ) {x r : ℝ} {i : ι}
    (h : ∀ j : ι, j ≠ i → S.map j '' K ∩ Metric.closedBall x r = ∅) :
    μ (Metric.closedBall x r)
      = ENNReal.ofReal (S.ratio i ^ s)
        * μ (Metric.closedBall (pre S i x) (r / S.ratio i)) := by
  rw [measure_eq_sum hμ measurableSet_closedBall,
    Finset.sum_eq_single i (fun j _ hj => by
      rw [measure_preimage_eq_zero hμ j (h j hj), mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi),
    preimage_closedBall]

/-- The one-step recursion on open balls. -/
theorem measure_ball_step (hμ : S.IsNatural K s μ) {x r : ℝ} {i : ι}
    (h : ∀ j : ι, j ≠ i → S.map j '' K ∩ Metric.ball x r = ∅) :
    μ (Metric.ball x r)
      = ENNReal.ofReal (S.ratio i ^ s)
        * μ (Metric.ball (pre S i x) (r / S.ratio i)) := by
  rw [measure_eq_sum hμ Metric.isOpen_ball.measurableSet,
    Finset.sum_eq_single i (fun j _ hj => by
      rw [measure_preimage_eq_zero hμ j (h j hj), mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi),
    preimage_ball]

/-- The support condition propagates through the one-step recursion. -/
theorem charged_pre (hμ : S.IsNatural K s μ) {x r : ℝ} (hr : 0 < r) {i : ι}
    (h : ∀ j : ι, j ≠ i → S.map j '' K ∩ Metric.closedBall x r = ∅)
    (hx : x ∈ Charged μ) : pre S i x ∈ Charged μ := by
  intro ε hε
  have hri := S.ratio_pos i
  set ε' : ℝ := min (S.ratio i * ε) r with hε'def
  have hε'pos : 0 < ε' := lt_min (by positivity) hr
  have hsmall : ∀ j : ι, j ≠ i → S.map j '' K ∩ Metric.ball x ε' = ∅ := by
    intro j hj
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    refine Set.eq_empty_iff_forall_notMem.mp (h j hj) y ⟨hy.1, ?_⟩
    exact Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (min_le_right _ _) hy.2)
  have hid := measure_ball_step hμ hsmall
  intro hzero
  refine hx ε' hε'pos ?_
  rw [hid]
  have hsub : μ (Metric.ball (pre S i x) (ε' / S.ratio i)) = 0 := by
    refine measure_mono_null (Metric.ball_subset_ball ?_) hzero
    rw [div_le_iff₀ hri]
    calc ε' ≤ S.ratio i * ε := min_le_left _ _
      _ = ε * S.ratio i := by ring
  rw [hsub, mul_zero]

/-- The support is closed. -/
theorem isClosed_charged (μ : Measure ℝ) : IsClosed (Charged μ) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro x hx
  simp only [Charged, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not] at hx
  obtain ⟨ε, hε, hε0⟩ := hx
  refine ⟨ε / 2, half_pos hε, fun y hy => ?_⟩
  simp only [Charged, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not]
  refine ⟨ε / 2, half_pos hε, measure_mono_null (fun z hz => ?_) hε0⟩
  rw [Metric.mem_ball] at hz hy ⊢
  calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by exact add_lt_add hz hy
    _ = ε := by ring

/-- The support sits inside the attractor. -/
theorem charged_subset (hμ : S.IsNatural K s μ) : Charged μ ⊆ K := by
  intro x hx
  by_contra hxK
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hμ.attractor.1.isClosed.isOpen_compl x hxK
  exact hx ε hε (measure_mono_null hball hμ.support)

/-- A uniform lower bound for the mass of a fixed ball centred anywhere in the support.
This is the input the stopping construction needs at the stopping scale. -/
theorem exists_uniform_lower (hμ : S.IsNatural K s μ) {t : ℝ} (ht : 0 < t) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Charged μ, ENNReal.ofReal c ≤ μ (Metric.closedBall x t) := by
  haveI := hμ.isProbabilityMeasure
  rcases (Charged μ).eq_empty_or_nonempty with hempty | hne
  · exact ⟨1, one_pos, fun x hx => absurd (hempty ▸ hx) (Set.notMem_empty x)⟩
  have hcomp : IsCompact (Charged μ) :=
    hμ.attractor.1.of_isClosed_subset (isClosed_charged μ) (charged_subset hμ)
  obtain ⟨F, hFsub, hFfin, hFcover⟩ := hcomp.elim_finite_subcover_image
    (c := fun y : ℝ => Metric.ball y (t / 2)) (fun y _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_biUnion hx (Metric.mem_ball_self (half_pos ht)))
  have hFne : (hFfin.toFinset).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.mp (hFcover hx)
    exact ⟨y, hFfin.mem_toFinset.mpr hy⟩
  refine ⟨hFfin.toFinset.inf' hFne (fun y => (μ (Metric.ball y (t / 2))).toReal), ?_, ?_⟩
  · refine (Finset.lt_inf'_iff _).2 fun y hy => ?_
    refine ENNReal.toReal_pos ((hFsub (hFfin.mem_toFinset.mp hy)) (t / 2) (half_pos ht))
      (measure_ne_top _ _)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hFcover hx)
    have hball : Metric.ball y (t / 2) ⊆ Metric.closedBall x t := by
      intro z hz
      rw [Metric.mem_ball] at hz
      rw [Metric.mem_ball, dist_comm] at hxy
      rw [Metric.mem_closedBall]
      calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ ≤ t / 2 + t / 2 := by exact add_le_add hz.le hxy.le
        _ = t := by ring
    refine le_trans ?_ (measure_mono hball)
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (Metric.ball y (t / 2)))]
    exact ENNReal.ofReal_le_ofReal
      (Finset.inf'_le _ (hFfin.mem_toFinset.mpr hy))

/-- The system has at least one letter: the attractor is non-empty and is the union of
its pieces. -/
theorem nonempty_index (hμ : S.IsNatural K s μ) : Nonempty ι := by
  obtain ⟨k, hk⟩ := hμ.attractor.2.1
  have hk' : k ∈ ⋃ i, S.map i '' K := by rw [← hμ.attractor.2.2.2]; exact hk
  obtain ⟨i, -⟩ := Set.mem_iUnion.mp hk'
  exact ⟨i⟩

/-- A ratio bound serving the stopping construction: a factor `q > 1` by which the
radius grows at every step. -/
theorem exists_growth_factor (S : System ι) [Nonempty ι] :
    ∃ q : ℝ, 1 < q ∧ ∀ i : ι, q * S.ratio i ≤ 1 := by
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty S.ratio with hMdef
  have hle : ∀ i : ι, S.ratio i ≤ M := fun i => Finset.le_sup' S.ratio (Finset.mem_univ i)
  have hMpos : 0 < M := lt_of_lt_of_le (S.ratio_pos (Classical.arbitrary ι))
    (hle (Classical.arbitrary ι))
  have hM1 : M < 1 := by
    rw [hMdef, Finset.sup'_lt_iff]
    exact fun i _ => S.ratio_lt_one i
  have hinv : M⁻¹ * M = 1 := inv_mul_cancel₀ hMpos.ne'
  have hipos : 0 < M⁻¹ := inv_pos.mpr hMpos
  exact ⟨M⁻¹, by nlinarith, fun i => by nlinarith [hle i]⟩

/-- The ratios are bounded away from zero, which keeps the stopping radius bounded. -/
theorem exists_ratio_lower (S : System ι) [Nonempty ι] :
    ∃ m : ℝ, 0 < m ∧ ∀ i : ι, m ≤ S.ratio i := by
  refine ⟨Finset.univ.inf' Finset.univ_nonempty S.ratio, ?_,
    fun i => Finset.inf'_le S.ratio (Finset.mem_univ i)⟩
  exact (Finset.lt_inf'_iff _).2 fun i _ => S.ratio_pos i

/-- The upper Ahlfors bound, with the explicit constant `(2/ρ)^s`.  The stopping
construction is the induction on `n`: below the separation gap the ball meets a single
piece, and the radius grows by the factor `q > 1` at every step, so after finitely many
steps the radius reaches the stopping scale `ρ/2`, where the total mass one is the
bound. -/
theorem measure_closedBall_le_of_isNatural (hs : 0 < s) (hsep : S.StronglySeparated K ρ)
    (hμ : S.IsNatural K s μ) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    μ (Metric.closedBall x r) ≤ ENNReal.ofReal ((2 / ρ) ^ s * r ^ s) := by
  haveI := hμ.isProbabilityMeasure
  haveI := nonempty_index hμ
  have hρ : 0 < ρ := hsep.1
  have h2ρ : (0:ℝ) < 2 / ρ := div_pos (by norm_num) hρ
  have base : ∀ y t : ℝ, 0 < t → ρ / 2 ≤ t →
      μ (Metric.closedBall y t) ≤ ENNReal.ofReal ((2 / ρ) ^ s * t ^ s) := by
    intro y t ht hb
    have h1 : (1:ℝ) ≤ 2 / ρ * t := by
      rw [show (2:ℝ) / ρ * t = 2 * t / ρ by ring, le_div_iff₀ hρ]
      linarith
    have h2 : (1:ℝ) ≤ (2 / ρ) ^ s * t ^ s := by
      rw [← Real.mul_rpow h2ρ.le ht.le]
      calc (1:ℝ) = (1:ℝ) ^ s := (Real.one_rpow s).symm
        _ ≤ (2 / ρ * t) ^ s := Real.rpow_le_rpow (by norm_num) h1 hs.le
    calc μ (Metric.closedBall y t) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal ((2 / ρ) ^ s * t ^ s) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h2
  obtain ⟨q, hq1, hqi⟩ := exists_growth_factor S
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq1
  have key : ∀ n : ℕ, ∀ y t : ℝ, 0 < t → ρ / 2 ≤ t * q ^ n →
      μ (Metric.closedBall y t) ≤ ENNReal.ofReal ((2 / ρ) ^ s * t ^ s) := by
    intro n
    induction n with
    | zero => intro y t ht hle; exact base y t ht (by simpa using hle)
    | succ n ih =>
      intro y t ht hle
      by_cases hb : ρ / 2 ≤ t
      · exact base y t ht hb
      have hb' : 2 * t < ρ := by linarith [not_le.mp hb]
      by_cases h0 : μ (Metric.closedBall y t) = 0
      · rw [h0]; exact zero_le
      obtain ⟨i, hi⟩ := exists_unique_meet hsep hμ hb' h0
      have hri := S.ratio_pos i
      have hqn : (0:ℝ) < q ^ n := pow_pos hq0 n
      have hgrow : t * q ≤ t / S.ratio i := by
        rw [le_div_iff₀ hri]
        nlinarith [hqi i]
      have hstep : ρ / 2 ≤ t / S.ratio i * q ^ n :=
        le_trans (le_trans hle (le_of_eq (by ring)))
          (mul_le_mul_of_nonneg_right hgrow hqn.le)
      have hIH := ih (pre S i y) (t / S.ratio i) (div_pos ht hri) hstep
      rw [measure_closedBall_step hμ hi]
      have hcancel : S.ratio i ^ s * (t / S.ratio i) ^ s = t ^ s := by
        rw [← Real.mul_rpow hri.le (div_pos ht hri).le]
        congr 1
        field_simp
      calc ENNReal.ofReal (S.ratio i ^ s)
              * μ (Metric.closedBall (pre S i y) (t / S.ratio i))
          ≤ ENNReal.ofReal (S.ratio i ^ s)
              * ENNReal.ofReal ((2 / ρ) ^ s * (t / S.ratio i) ^ s) :=
            mul_le_mul_right hIH _
        _ = ENNReal.ofReal ((2 / ρ) ^ s * t ^ s) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hri s).le]
            congr 1
            calc S.ratio i ^ s * ((2 / ρ) ^ s * (t / S.ratio i) ^ s)
                = (2 / ρ) ^ s * (S.ratio i ^ s * (t / S.ratio i) ^ s) := by ring
              _ = (2 / ρ) ^ s * t ^ s := by rw [hcancel]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ρ / 2 ≤ r * q ^ n := by
    obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt hq1).eventually_ge_atTop (ρ / (2 * r))).exists
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * r)] at hn
    linarith
  exact key n x r hr hn

/-- The lower Ahlfors bound.  The same stopping construction, run down from a
support point: the ball has positive mass at every scale, so it meets a single piece,
and at the stopping scale `ρ/2` compactness of the support gives a mass bound uniform
in the centre. -/
theorem exists_le_measure_closedBall_of_isNatural (hs : 0 < s)
    (hsep : S.StronglySeparated K ρ) (hμ : S.IsNatural K s μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Charged μ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ENNReal.ofReal (c * r ^ s) ≤ μ (Metric.closedBall x r) := by
  haveI := hμ.isProbabilityMeasure
  haveI := nonempty_index hμ
  have hρ : 0 < ρ := hsep.1
  obtain ⟨q, hq1, hqi⟩ := exists_growth_factor S
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq1
  obtain ⟨m, hm0, hmi⟩ := exists_ratio_lower S
  obtain ⟨c₀, hc₀, hcb⟩ := exists_uniform_lower hμ (half_pos hρ)
  set B : ℝ := max 1 (ρ / (2 * m)) with hBdef
  have hB1 : (1:ℝ) ≤ B := le_max_left _ _
  have hBpos : (0:ℝ) < B := lt_of_lt_of_le one_pos hB1
  have hBs : (0:ℝ) < B ^ s := Real.rpow_pos_of_pos hBpos s
  have base : ∀ y t : ℝ, y ∈ Charged μ → 0 < t → t ≤ B → ρ / 2 ≤ t →
      ENNReal.ofReal (c₀ / B ^ s * t ^ s) ≤ μ (Metric.closedBall y t) := by
    intro y t hy ht htB hb
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (le_trans (hcb y hy) (measure_mono (Metric.closedBall_subset_closedBall hb)))
    rw [div_mul_eq_mul_div, div_le_iff₀ hBs]
    nlinarith [Real.rpow_le_rpow ht.le htB hs.le]
  have key : ∀ n : ℕ, ∀ y t : ℝ, y ∈ Charged μ → 0 < t → t ≤ B → ρ / 2 ≤ t * q ^ n →
      ENNReal.ofReal (c₀ / B ^ s * t ^ s) ≤ μ (Metric.closedBall y t) := by
    intro n
    induction n with
    | zero => intro y t hy ht htB hle; exact base y t hy ht htB (by simpa using hle)
    | succ n ih =>
      intro y t hy ht htB hle
      by_cases hb : ρ / 2 ≤ t
      · exact base y t hy ht htB hb
      have hb' : 2 * t < ρ := by linarith [not_le.mp hb]
      have h0 : μ (Metric.closedBall y t) ≠ 0 := fun h =>
        hy t ht (le_antisymm (h ▸ measure_mono Metric.ball_subset_closedBall) zero_le)
      obtain ⟨i, hi⟩ := exists_unique_meet hsep hμ hb' h0
      have hri := S.ratio_pos i
      have hqn : (0:ℝ) < q ^ n := pow_pos hq0 n
      have hgrow : t * q ≤ t / S.ratio i := by
        rw [le_div_iff₀ hri]
        nlinarith [hqi i]
      have hstep : ρ / 2 ≤ t / S.ratio i * q ^ n :=
        le_trans (le_trans hle (le_of_eq (by ring)))
          (mul_le_mul_of_nonneg_right hgrow hqn.le)
      have htB' : t / S.ratio i ≤ B := by
        refine le_trans ?_ (le_max_right 1 (ρ / (2 * m)))
        rw [div_le_div_iff₀ hri (by linarith : (0:ℝ) < 2 * m)]
        nlinarith [hmi i, not_le.mp hb]
      have hIH := ih (pre S i y) (t / S.ratio i)
        (charged_pre hμ ht hi hy) (div_pos ht hri) htB' hstep
      rw [measure_closedBall_step hμ hi]
      have hcancel : S.ratio i ^ s * (t / S.ratio i) ^ s = t ^ s := by
        rw [← Real.mul_rpow hri.le (div_pos ht hri).le]
        congr 1
        field_simp
      refine le_trans (le_of_eq ?_) (mul_le_mul_right hIH _)
      rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hri s).le]
      congr 1
      calc c₀ / B ^ s * t ^ s
          = c₀ / B ^ s * (S.ratio i ^ s * (t / S.ratio i) ^ s) := by rw [hcancel]
        _ = S.ratio i ^ s * (c₀ / B ^ s * (t / S.ratio i) ^ s) := by ring
  refine ⟨c₀ / B ^ s, div_pos hc₀ hBs, fun x hx r hr0 hr1 => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ρ / 2 ≤ r * q ^ n := by
    obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt hq1).eventually_ge_atTop (ρ / (2 * r))).exists
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * r)] at hn
    linarith
  exact key n x r hx hr0 (le_trans hr1 hB1) hn

/-- Ahlfors regularity weakens when the constant grows. -/
theorem isAhlfors_mono {A A' : ℝ} (h : IsAhlfors s A μ) (hAA : A ≤ A') :
    IsAhlfors s A' μ := by
  obtain ⟨hA, hball⟩ := h
  have hApos : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  refine ⟨le_trans hA hAA, fun x hx r hr0 hr1 => ⟨?_, ?_⟩⟩
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hball x hx r hr0 hr1).1
    have hrs : (0:ℝ) ≤ r ^ s := (Real.rpow_pos_of_pos hr0 s).le
    nlinarith [inv_anti₀ hApos hAA]
  · refine le_trans (hball x hx r hr0 hr1).2 (ENNReal.ofReal_le_ofReal ?_)
    have hrs : (0:ℝ) ≤ r ^ s := (Real.rpow_pos_of_pos hr0 s).le
    nlinarith

/-- The natural measure of a strongly separated system is `s`-Frostman.  The upper
Ahlfors bound holds at every centre, not only in the support, and `IsNatural` carries
the support condition on `[0,1]`, so this is `eq:frostman` outright.  It is what the
later endpoints read the Frostman hypothesis of `μ_A` and `μ_B` off. -/
theorem exists_isFrostman_of_isNatural (hs : 0 < s) (hsep : S.StronglySeparated K ρ)
    (hμ : S.IsNatural K s μ) : ∃ A : ℝ, IsFrostman s A μ := by
  refine ⟨max 1 ((2 / ρ) ^ s), le_max_left _ _, hμ.support_Icc, fun x t ht0 ht1 => ?_⟩
  refine le_trans (measure_closedBall_le_of_isNatural hs hsep hμ x ht0)
    (ENNReal.ofReal_le_ofReal ?_)
  have hts : (0:ℝ) ≤ t ^ s := (Real.rpow_pos_of_pos ht0 s).le
  nlinarith [le_max_right (1:ℝ) ((2 / ρ) ^ s)]

end AhlforsRegular

/-- The natural measure of a strongly separated system is Ahlfors regular of its
similarity dimension, in the closed-ball form.  This is the internal endpoint
`audit_ahlfors`.  The dimension equation is a consequence of `IsNatural`. -/
theorem exists_isAhlforsClosed {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ}
    {ρ s : ℝ} (hs : 0 < s) (hsep : S.StronglySeparated K ρ) (_hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ A : ℝ, IsAhlforsClosed s A μ := by
  obtain ⟨c, hc, hlower⟩ :=
    AhlforsRegular.exists_le_measure_closedBall_of_isNatural hs hsep hμ
  refine ⟨max 1 (max ((2 / ρ) ^ s) c⁻¹), le_max_left _ _, fun x hx r hr0 hr1 => ⟨?_, ?_⟩⟩
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hlower x hx r hr0 hr1)
    have hinv : (max 1 (max ((2 / ρ) ^ s) c⁻¹))⁻¹ ≤ c := by
      have h := inv_anti₀ (inv_pos.mpr hc)
        (le_trans (le_max_right _ _) (le_max_right 1 (max ((2 / ρ) ^ s) c⁻¹)))
      rwa [inv_inv] at h
    have hrs : (0:ℝ) ≤ r ^ s := (Real.rpow_pos_of_pos hr0 s).le
    nlinarith
  · refine le_trans (AhlforsRegular.measure_closedBall_le_of_isNatural hs hsep hμ x hr0)
      (ENNReal.ofReal_le_ofReal ?_)
    have hrs : (0:ℝ) ≤ r ^ s := (Real.rpow_pos_of_pos hr0 s).le
    nlinarith [le_trans (le_max_left ((2 / ρ) ^ s) c⁻¹)
      (le_max_right 1 (max ((2 / ρ) ^ s) c⁻¹))]

/-- Ahlfors regularity for the two measures in the parameter-uniform application, with
one constant serving both. -/
theorem exists_isAhlfors_homogeneous_pair {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2) {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural KB (homogeneousDim lam) μB) :
    ∃ A : ℝ, IsAhlfors (homogeneousDim lam) A μA ∧
      IsAhlfors (homogeneousDim lam) A μB := by
  have hs0 := homogeneousDim_pos hlam0 hlam
  have hs1 := homogeneousDim_lt_one hlam0 hlam
  obtain ⟨A₁, hA₁⟩ := exists_isAhlforsClosed _ hs0
    (homogeneousSystem_stronglySeparated hlam0 hlam hA.attractor.2.2.1)
    (homogeneousSystem_isDimension hlam0 hlam) hA
  obtain ⟨A₂, hA₂⟩ := exists_isAhlforsClosed _ hs0
    (pairSystem_stronglySeparated (pairRatio_pos hs0)
      (pairRatio_lt_half hs0 hs1) hB.attractor.2.2.1)
    (pairSystem_isDimension hs0 hs1) hB
  refine ⟨max (2 ^ homogeneousDim lam * A₁) (2 ^ homogeneousDim lam * A₂),
    AhlforsRegular.isAhlfors_mono (hA₁.isAhlfors hs0.le) (le_max_left _ _),
    AhlforsRegular.isAhlfors_mono (hA₂.isAhlfors hs0.le) (le_max_right _ _)⟩

end BrownianImages
