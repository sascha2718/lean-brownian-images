/-
`thm:cross-piece-mass` of `sec:renewal`: under the strong open set condition, the mass
of a first-level piece `μ_i = (S_i)_* μ` within distance `h` of another piece `K_j`
decays like `h^η`, and the product `μ_i × μ_j` gives the `h`-neighbourhood of the
diagonal mass `O(h^{s+η})`.

The paper argues with the Bernoulli address distribution: a word `v` with `S_v K ⊆ U`
is chosen, and an address in which `v` occurs in one of the first `n` blocks after the
initial symbol codes a point at distance at least `b r_min^{1+mn}` from `K_j`.  Here
the same count is run on the measure itself: iterating Hutchinson's identity `m`
letters at a time, the block equal to `v` contributes nothing to the mass near `K_j`,
and each of the remaining blocks carries the factor `1 - p_v`.

* `IsNatural.measure_eq_sum_generation`: Hutchinson's identity iterated to generation
  `m`.
* `IsAttractor.exists_generationWord_image_subset`: a cylinder inside a given open
  set around a point of the attractor.
* `IsFeasible.preimage_cthickening_subset_compl`: the exclusion step, that a cylinder
  ending in `v` stays away from `K_j`.
* `IsFeasible.measure_preimage_cthickening_le_pow`: the geometric decay along the
  scales `b r_i r_min^{nm}`.
* `exists_rpow_bound_of_geometric`: geometric decay along a geometric sequence of
  scales is a power bound at every scale.
* `StrongOpenSetCondition.exists_cross_piece_bound`: `thm:cross-piece-mass`,
  `eq:boundary-mass` and `eq:cross-piece-mass`, with one constant and one exponent
  `η ∈ (0, 1-s)` for every pair `i ≠ j`.
-/
import BrownianImages.StoppingGeometry

namespace BrownianImages

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace System

variable {iota : Type u} [Fintype iota] [Nonempty iota] (S : System iota)

/-! ### Generation words -/

omit [Nonempty iota] in
/-- Every finite-word similarity, composed on the outside, maps a feasible set into
itself. -/
theorem IsFeasible.mapsTo_generationMap {U : Set ℝ} (hU : S.IsFeasible U) :
    ∀ (k : ℕ) (w : GenerationWord iota k), MapsTo (S.generationMap k w) U U
  | 0, _ => by simpa [generationMap] using Set.mapsTo_id U
  | k + 1, w => by
      rw [generationMap_succ]
      exact (hU.mapsTo w.2).comp (hU.mapsTo_generationMap k w.1)

/-- A generation-`k` ratio is at least `r_min^k`. -/
theorem minRatio_pow_le_generationRatio :
    ∀ (k : ℕ) (w : GenerationWord iota k), S.minRatio ^ k ≤ S.generationRatio k w
  | 0, _ => by simp [generationRatio]
  | k + 1, ⟨w, i⟩ => by
      rw [generationRatio, pow_succ]
      exact mul_le_mul (minRatio_pow_le_generationRatio k w) (S.minRatio_le i)
        S.minRatio_pos.le (S.generationRatio_pos k w).le

omit [Nonempty iota] in
/-- The affine form of a generation map. -/
theorem generationMap_eq_add_mul (k : ℕ) (w : GenerationWord iota k) (x : ℝ) :
    S.generationMap k w x =
      S.generationMap k w 0 + S.generationSign k w * S.generationRatio k w * x := by
  linear_combination S.generationMap_sub k w x 0

omit [Nonempty iota] in
/-- Hutchinson's identity iterated to generation `m`, read on a measurable set:
`μ(A) = ∑_{|w| = m} p_w μ(S_w⁻¹ A)`. -/
theorem IsNatural.measure_eq_sum_generation {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) :
    ∀ (m : ℕ) {A : Set ℝ}, MeasurableSet A →
      μ A = ∑ w : GenerationWord iota m,
        ENNReal.ofReal (S.generationWeight s m w) * μ (S.generationMap m w ⁻¹' A)
  | 0, A, _ => by simp [GenerationWord, generationWeight, generationMap]
  | m + 1, A, hA => by
      rw [hμ.measure_eq_sum S hA]
      change _ = ∑ w : GenerationWord iota m × iota, _
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hμ.measure_eq_sum_generation m (S.measurable_map i hA), Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      change ENNReal.ofReal (S.ratio i ^ s) *
          (ENNReal.ofReal (S.generationWeight s m w) * μ (S.generationMap m w ⁻¹' (S.map i ⁻¹' A)))
        = ENNReal.ofReal (S.generationWeight s m w * S.tubeWeight s i) *
          μ ((S.map i ∘ S.generationMap m w) ⁻¹' A)
      rw [Set.preimage_comp, tubeWeight, ENNReal.ofReal_mul (S.generationWeight_nonneg s m w)]
      ring

/-- Around every point of the attractor lying in an open set `U`, some cylinder of
positive generation lies inside `U`. -/
theorem IsAttractor.exists_generationWord_image_subset {K : Set ℝ} (hK : S.IsAttractor K)
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hxK : x ∈ K) (hxU : x ∈ U) :
    ∃ m : ℕ, 0 < m ∧ ∃ v : GenerationWord iota m, S.generationMap m v '' K ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hε (Hutchinson.maxRatio_lt_one S)
  have hm : Hutchinson.maxRatio S ^ (m₀ + 1) < ε :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (Hutchinson.maxRatio_pos S).le
      (Hutchinson.maxRatio_lt_one S).le (Nat.le_succ m₀)) hm₀
  obtain ⟨v, y, hyK, hvy⟩ := hK.exists_generation_preimage S (m₀ + 1) hxK
  refine ⟨m₀ + 1, Nat.succ_pos _, v, fun z hz => hball ?_⟩
  rw [Metric.mem_ball]
  have hzc : z ∈ (hK.generationCylinder S (m₀ + 1) v : Set ℝ) := by
    rw [hK.coe_generationCylinder]; exact hz
  have hxc : x ∈ (hK.generationCylinder S (m₀ + 1) v : Set ℝ) := by
    rw [hK.coe_generationCylinder]; exact ⟨y, hyK, hvy⟩
  calc dist z x ≤ Metric.diam (hK.generationCylinder S (m₀ + 1) v : Set ℝ) :=
        Metric.dist_le_diam_of_mem (hK.generationCylinder S (m₀ + 1) v).isCompact.isBounded
          hzc hxc
    _ ≤ Hutchinson.maxRatio S ^ (m₀ + 1) := hK.diam_generationCylinder_le S (m₀ + 1) v
    _ < ε := hm

/-! ### The exclusion step -/

/-- **The exclusion step.**  Let `f` be an affine map of slope `r ≠ 0` sending a
feasible set `U` into `S_i U`, and let `v` be a word whose cylinder `S_v K` has its
`b`-neighbourhood inside `U`.  Then the cylinder `f(S_v K)` stays at distance at least
`b |r|` from `K_j` for `j ≠ i`, so the preimage of the `h`-neighbourhood of `K_j` under
`f ∘ S_v` misses the attractor whenever `h < b |r|`. -/
theorem IsFeasible.preimage_cthickening_subset_compl {U : Set ℝ} (hU : S.IsFeasible U)
    {K : Set ℝ} (hK : S.IsAttractor K) {m : ℕ} {v : GenerationWord iota m} {b : ℝ}
    (hv : cthickening b (S.generationMap m v '' K) ⊆ U)
    {f : ℝ → ℝ} {c r : ℝ} (hf : ∀ x, f x = c + r * x) (hr : r ≠ 0)
    (hfU : f '' U ⊆ S.map i '' U) {j : iota} (hij : i ≠ j) {h : ℝ} (h0 : 0 ≤ h)
    (hhb : h < b * |r|) :
    (f ∘ S.generationMap m v) ⁻¹' cthickening h (S.map j '' K) ⊆ Kᶜ := by
  have hr' : 0 < |r| := abs_pos.mpr hr
  intro y hy hyK
  have hKj : IsCompact (S.map j '' K) := hK.1.image (Hutchinson.continuous_systemMap S j)
  rw [Set.mem_preimage, Function.comp_apply, hKj.cthickening_eq_biUnion_closedBall h0] at hy
  simp only [Set.mem_iUnion, exists_prop] at hy
  obtain ⟨z, hzKj, hz⟩ := hy
  rw [Metric.mem_closedBall, Real.dist_eq] at hz
  set d : ℝ := z - f (S.generationMap m v y) with hd
  have hdabs : |d| ≤ h := by rw [hd, abs_sub_comm]; exact hz
  have hfy' : f (S.generationMap m v y + d / r) = z := by
    rw [hf, hd, hf]
    field_simp
    ring
  have hy'U : S.generationMap m v y + d / r ∈ U := by
    refine hv (Metric.mem_cthickening_of_dist_le _ (S.generationMap m v y) b _
      ⟨y, hyK, rfl⟩ ?_)
    rw [Real.dist_eq, add_sub_cancel_left, abs_div, div_le_iff₀ hr']
    linarith
  have hzU : z ∈ S.map i '' U := hfU ⟨_, hy'U, hfy'⟩
  exact hU.notMem_piece_of_mem_image S hK hij hzU hzKj

/-! ### The geometric decay -/

/-- **The block count of `thm:cross-piece-mass`.**  For an affine map `f` of slope
`r ≠ 0` sending `U` into `S_i U`, the `μ`-mass of `f⁻¹` of the `h`-neighbourhood of
`K_j` is at most `(1 - p_v)^k` whenever `h < b |r| r_min^{km}`: iterating Hutchinson's
identity `m` letters at a time, the block `v` is excluded and every other block
carries a factor `1 - p_v`. -/
theorem IsFeasible.measure_preimage_cthickening_le_pow {U : Set ℝ} (hU : S.IsFeasible U)
    {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (hdim : S.IsDimension s)
    {m : ℕ} {v : GenerationWord iota m} {b : ℝ} (hb : 0 < b)
    (hv : cthickening b (S.generationMap m v '' K) ⊆ U) {i j : iota} (hij : i ≠ j) :
    ∀ (k : ℕ) (f : ℝ → ℝ) (c r : ℝ), (∀ x, f x = c + r * x) → r ≠ 0 →
      f '' U ⊆ S.map i '' U → ∀ h : ℝ, 0 ≤ h → h < b * |r| * S.minRatio ^ (k * m) →
        μ (f ⁻¹' cthickening h (S.map j '' K)) ≤
          ENNReal.ofReal ((1 - S.generationWeight s m v) ^ k)
  | 0, f, c, r, hf, hr, hfU, h, h0, hhb => by
      have := hμ.isProbabilityMeasure
      simpa using (prob_le_one : μ (f ⁻¹' cthickening h (S.map j '' K)) ≤ 1)
  | k + 1, f, c, r, hf, hr, hfU, h, h0, hhb => by
      classical
      have := hμ.isProbabilityMeasure
      have hrmin := S.minRatio_pos
      have hrmin1 := S.minRatio_le_one
      have hfeq : f = fun x => c + r * x := funext hf
      have hfmeas : Measurable f := by rw [hfeq]; fun_prop
      have hN : MeasurableSet (cthickening h (S.map j '' K)) :=
        Metric.isClosed_cthickening.measurableSet
      rw [hμ.measure_eq_sum_generation S m (hfmeas hN)]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v)]
      -- the block `v` contributes nothing
      have hr' : 0 < |r| := abs_pos.mpr hr
      have hvterm : μ (S.generationMap m v ⁻¹' (f ⁻¹' cthickening h (S.map j '' K))) = 0 := by
        refine measure_mono_null ?_ hμ.support
        rw [← Set.preimage_comp]
        refine hU.preimage_cthickening_subset_compl S hμ.attractor hv hf hr hfU hij h0 ?_
        calc h < b * |r| * S.minRatio ^ ((k + 1) * m) := hhb
          _ ≤ b * |r| * 1 := by
              gcongr
              exact pow_le_one₀ hrmin.le hrmin1
          _ = b * |r| := mul_one _
      rw [hvterm, mul_zero, zero_add]
      -- every other block carries the factor `1 - p_v`
      have hpv0 : 0 ≤ S.generationWeight s m v := S.generationWeight_nonneg s m v
      have hsum : ∑ u ∈ Finset.univ.erase v, S.generationWeight s m u
          = 1 - S.generationWeight s m v := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ v), S.sum_generationWeight hdim m]
      have hpv1 : S.generationWeight s m v ≤ 1 := by
        have := Finset.sum_nonneg fun u (_ : u ∈ Finset.univ.erase v) =>
          S.generationWeight_nonneg s m u
        linarith
      have hterm : ∀ u ∈ Finset.univ.erase v,
          ENNReal.ofReal (S.generationWeight s m u) *
              μ (S.generationMap m u ⁻¹' (f ⁻¹' cthickening h (S.map j '' K)))
            ≤ ENNReal.ofReal (S.generationWeight s m u) *
              ENNReal.ofReal ((1 - S.generationWeight s m v) ^ k) := by
        intro u _
        gcongr
        rw [← Set.preimage_comp]
        have hgen := S.minRatio_pow_le_generationRatio m u
        have hρ := S.generationRatio_pos m u
        have habs : |r * (S.generationSign m u * S.generationRatio m u)|
            = |r| * S.generationRatio m u := by
          rw [abs_mul, S.abs_generationSign_mul_generationRatio]
        refine hU.measure_preimage_cthickening_le_pow hμ hdim hb hv hij k
          (f ∘ S.generationMap m u) (c + r * S.generationMap m u 0)
          (r * (S.generationSign m u * S.generationRatio m u))
          ?_ (mul_ne_zero hr (S.generationSign_mul_generationRatio_ne_zero m u)) ?_ h h0 ?_
        · intro x
          rw [Function.comp_apply, hf, S.generationMap_eq_add_mul m u x]
          ring
        · rw [Set.image_comp]
          exact (Set.image_mono (hU.mapsTo_generationMap S m u).image_subset).trans hfU
        · rw [habs]
          calc h < b * |r| * S.minRatio ^ ((k + 1) * m) := hhb
            _ = b * (|r| * S.minRatio ^ m) * S.minRatio ^ (k * m) := by
                rw [show (k + 1) * m = m + k * m by ring, pow_add]
                ring
            _ ≤ b * (|r| * S.generationRatio m u) * S.minRatio ^ (k * m) := by
                gcongr
      calc (∑ u ∈ Finset.univ.erase v, ENNReal.ofReal (S.generationWeight s m u) *
            μ (S.generationMap m u ⁻¹' (f ⁻¹' cthickening h (S.map j '' K))))
          ≤ ∑ u ∈ Finset.univ.erase v, ENNReal.ofReal (S.generationWeight s m u) *
            ENNReal.ofReal ((1 - S.generationWeight s m v) ^ k) := Finset.sum_le_sum hterm
        _ = (∑ u ∈ Finset.univ.erase v, ENNReal.ofReal (S.generationWeight s m u)) *
            ENNReal.ofReal ((1 - S.generationWeight s m v) ^ k) := by
            rw [Finset.sum_mul]
        _ = ENNReal.ofReal ((1 - S.generationWeight s m v) ^ (k + 1)) := by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => S.generationWeight_nonneg s m u),
              hsum, ← ENNReal.ofReal_mul (by linarith), pow_succ]
            ring_nf

/-! ### From geometric scales to every scale -/

/-- A geometric bracket: every `0 < h ≤ h₀` lies between two consecutive members of
the sequence `h₀ q^n`. -/
theorem exists_geometric_bracket {h₀ q h : ℝ} (hh₀ : 0 < h₀) (hq0 : 0 < q) (hq1 : q < 1)
    (hh : 0 < h) (hh₀h : h ≤ h₀) :
    ∃ n : ℕ, h₀ * q ^ (n + 1) < h ∧ h ≤ h₀ * q ^ n := by
  classical
  have hex : ∃ n : ℕ, h₀ * q ^ (n + 1) < h := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hh hh₀) hq1
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hh₀] at hn
    calc h₀ * q ^ (n + 1) = q * (q ^ n * h₀) := by ring
      _ < 1 * h := by
          refine mul_lt_mul' hq1.le ?_ (by positivity) one_pos
          linarith
      _ = h := one_mul h
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero, mul_one]; exact hh₀h
  · obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have := Nat.find_min hex (show n' < Nat.find hex by omega)
    rw [hn']
    exact not_lt.mp this

/-- **Geometric decay is power decay.**  If a family of bounded monotone functions
`F a : (0, ∞) → [0, 1]` satisfies `F a (h₀ q^n) ≤ θ^n` for every `n`, with `0 < q < 1`
and `0 < θ < 1`, then `F a h ≤ C h^η` on `(0, 1]` for `η = log θ / log q` and one
constant `C`, uniformly in `a`. -/
theorem exists_rpow_bound_of_geometric {α : Type*} (F : α → ℝ → ℝ)
    (hmono : ∀ a, Monotone (F a)) (_hF0 : ∀ a h, 0 ≤ F a h) (hF1 : ∀ a h, F a h ≤ 1)
    {h₀ q θ : ℝ} (hh₀ : 0 < h₀) (hq0 : 0 < q) (hq1 : q < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgeo : ∀ a (n : ℕ), F a (h₀ * q ^ n) ≤ θ ^ n) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ a, ∀ h, 0 < h → h ≤ 1 → F a h ≤ C * h ^ η := by
  set η : ℝ := Real.log θ / Real.log q with hη
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hlogq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hη0 : 0 < η := div_pos_of_neg_of_neg hlogθ hlogq
  have hqη : q ^ η = θ := by
    rw [Real.rpow_def_of_pos hq0, hη, mul_div_cancel₀ _ hlogq.ne, Real.exp_log hθ0]
  have hqh₀ : 0 < q * h₀ := mul_pos hq0 hh₀
  set C : ℝ := (q * h₀) ^ (-η) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos hqh₀ _
  refine ⟨C, η, hC0, hη0, fun a h hh hh1 => ?_⟩
  -- `C h^η = (h / (q h₀))^η`
  have hCh : C * h ^ η = (h / (q * h₀)) ^ η := by
    rw [hC, Real.div_rpow hh.le hqh₀.le, Real.rpow_neg hqh₀.le, div_eq_mul_inv, mul_comm]
  rw [hCh]
  by_cases hcase : h ≤ h₀
  · obtain ⟨n, hlt, hle⟩ := exists_geometric_bracket hh₀ hq0 hq1 hh hcase
    calc F a h ≤ F a (h₀ * q ^ n) := hmono a hle
      _ ≤ θ ^ n := hgeo a n
      _ = (q ^ n) ^ η := by
          rw [← hqη, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
            ← Real.rpow_mul hq0.le, mul_comm]
      _ ≤ (h / (q * h₀)) ^ η := by
          refine Real.rpow_le_rpow (pow_nonneg hq0.le n) ?_ hη0.le
          rw [le_div_iff₀ hqh₀]
          calc q ^ n * (q * h₀) = h₀ * q ^ (n + 1) := by ring
            _ ≤ h := hlt.le
  · rw [not_le] at hcase
    calc F a h ≤ 1 := hF1 a h
      _ ≤ (h / (q * h₀)) ^ η := by
          refine Real.one_le_rpow ?_ hη0.le
          rw [le_div_iff₀ hqh₀, one_mul]
          calc q * h₀ ≤ 1 * h₀ := mul_le_mul_of_nonneg_right hq1.le hh₀.le
            _ = h₀ := one_mul h₀
            _ ≤ h := hcase.le

/-! ### The product bound -/

omit [Nonempty iota] in
/-- The `h`-neighbourhood of the diagonal under `μ_i × μ_j` is controlled by the
Frostman bound of `μ_j` on the set of points of `μ_i` within distance `h` of `K_j`:
`(μ_i × μ_j){|x-y| ≤ h} ≤ A (h/r_j)^s μ_i(N_h(K_j))`. -/
theorem IsNatural.prod_map_close_le {K : Set ℝ} {s A : ℝ} (hs : 0 ≤ s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (hA : IsFrostman s A μ) (i j : iota) {h : ℝ} (h0 : 0 < h) :
    ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ h}
      ≤ ENNReal.ofReal (A * (h / S.ratio j) ^ s) *
        (μ.map (S.map i)) (cthickening h (S.map j '' K)) := by
  have := hμ.isProbabilityMeasure
  have hrj := S.ratio_pos j
  have hKj : IsCompact (S.map j '' K) := hμ.attractor.1.image (Hutchinson.continuous_systemMap S j)
  have hN : MeasurableSet (cthickening h (S.map j '' K)) :=
    Metric.isClosed_cthickening.measurableSet
  rw [Measure.prod_apply (measurableSet_phiSet h)]
  simp only [mk_preimage_phiSet]
  -- the pointwise bound on the section mass
  have hpt : ∀ x : ℝ, (μ.map (S.map j)) (closedBall x h) ≤
      (cthickening h (S.map j '' K)).indicator (fun _ => ENNReal.ofReal (A * (h / S.ratio j) ^ s)) x := by
    intro x
    rw [Measure.map_apply (S.measurable_map j) measurableSet_closedBall,
      AhlforsRegular.preimage_closedBall]
    by_cases hx : x ∈ cthickening h (S.map j '' K)
    · rw [Set.indicator_of_mem hx]
      by_cases hh1 : h / S.ratio j ≤ 1
      · exact hA.measure_closedBall_le _ _ (div_pos h0 hrj) hh1
      · rw [not_le] at hh1
        calc μ (closedBall (AhlforsRegular.pre S j x) (h / S.ratio j)) ≤ 1 := prob_le_one
          _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal (A * (h / S.ratio j) ^ s) := by
              refine ENNReal.ofReal_le_ofReal ?_
              calc (1:ℝ) = 1 * 1 := (mul_one 1).symm
                _ ≤ A * (h / S.ratio j) ^ s :=
                    mul_le_mul hA.one_le_const (Real.one_le_rpow hh1.le hs) zero_le_one
                      (by linarith [hA.one_le_const])
    · rw [Set.indicator_of_notMem hx]
      refine le_of_eq (measure_mono_null ?_ hμ.support)
      intro y hy hyK
      rw [Metric.mem_closedBall, le_div_iff₀ hrj] at hy
      have hdist : dist (S.map j y) x ≤ h := by
        rw [AhlforsRegular.dist_map]
        linarith
      apply hx
      rw [hKj.cthickening_eq_biUnion_closedBall h0.le]
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨S.map j y, ⟨y, hyK, rfl⟩, by rw [Metric.mem_closedBall, dist_comm]; exact hdist⟩
  calc (∫⁻ x, (μ.map (S.map j)) (closedBall x h) ∂(μ.map (S.map i)))
      ≤ ∫⁻ x, (cthickening h (S.map j '' K)).indicator
          (fun _ => ENNReal.ofReal (A * (h / S.ratio j) ^ s)) x ∂(μ.map (S.map i)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (A * (h / S.ratio j) ^ s) *
        (μ.map (S.map i)) (cthickening h (S.map j '' K)) := lintegral_indicator_const hN _

/-! ### `thm:cross-piece-mass` -/

/-- **`thm:cross-piece-mass`.**  Under the strong open set condition there are `C > 0`
and `η ∈ (0, 1-s)` such that, for `i ≠ j` and `0 < h ≤ 1`,
`μ_i{x : dist(x, K_j) ≤ h} ≤ C h^η` (`eq:boundary-mass`) and
`(μ_i × μ_j){|x-y| ≤ h} ≤ C h^{s+η}` (`eq:cross-piece-mass`), where `μ_i = (S_i)_* μ`
and `K_j = S_j K`.  The feasible open set meeting `K` supplies a cylinder `S_v K` at
positive distance `b` from `U^c`; along the scales `b r_min^{1+nm} / 2` the mass near
`K_j` decays like `(1-p_v)^n`, which is a power bound at every scale; and the Frostman
bound of `μ_j` turns it into the product bound. -/
theorem StrongOpenSetCondition.exists_cross_piece_bound {K : Set ℝ}
    (hsosc : S.StrongOpenSetCondition K) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 - s ∧ ∀ i j : iota, i ≠ j → ∀ h : ℝ, 0 < h → h ≤ 1 →
      (μ.map (S.map i)) (cthickening h (S.map j '' K)) ≤ ENNReal.ofReal (C * h ^ η) ∧
      ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ h}
        ≤ ENNReal.ofReal (C * h ^ (s + η)) := by
  classical
  have := hμ.isProbabilityMeasure
  obtain ⟨U, hU, x, hxU, hxK⟩ := hsosc
  have hosc : S.OpenSetCondition := ⟨U, hU⟩
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  obtain ⟨m, hm, v, hv⟩ :=
    hμ.attractor.exists_generationWord_image_subset S hU.isOpen hxK hxU
  have hcompact : IsCompact (S.generationMap m v '' K) :=
    hμ.attractor.1.image (S.continuous_generationMap m v)
  obtain ⟨b, hb, hbU⟩ := hcompact.exists_cthickening_subset_open hU.isOpen hv
  have hrmin := S.minRatio_pos
  have hrmin1 : S.minRatio < 1 :=
    lt_of_le_of_lt (S.minRatio_le (Classical.arbitrary iota)) (S.ratio_lt_one _)
  -- the weight of `v` lies strictly between `0` and `1`
  have hpv0 : 0 < S.generationWeight s m v := S.generationWeight_pos s m v
  have hpv1 : S.generationWeight s m v < 1 := by
    rw [S.generationWeight_eq_ratio_rpow]
    refine Real.rpow_lt_one (S.generationRatio_pos m v).le ?_ hs0
    calc S.generationRatio m v ≤ Hutchinson.maxRatio S ^ m :=
          S.generationRatio_le_maxRatio_pow m v
      _ < 1 := pow_lt_one₀ (Hutchinson.maxRatio_pos S).le (Hutchinson.maxRatio_lt_one S) hm.ne'
  -- geometric decay along the scales `h₀ q^n`
  set θ : ℝ := 1 - S.generationWeight s m v with hθ
  set q : ℝ := S.minRatio ^ m with hq
  set h₀ : ℝ := b * S.minRatio / 2 with hh₀
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hq0 : 0 < q := pow_pos hrmin m
  have hq1 : q < 1 := pow_lt_one₀ hrmin.le hrmin1 hm.ne'
  have hh₀0 : 0 < h₀ := by rw [hh₀]; positivity
  set P := {p : iota × iota // p.1 ≠ p.2} with hP
  set F : P → ℝ → ℝ := fun p h =>
    ((μ.map (S.map p.1.1)) (cthickening h (S.map p.1.2 '' K))).toReal with hF
  have hmono : ∀ p : P, Monotone (F p) := by
    intro p h h' hhh'
    rw [hF]
    dsimp only
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (cthickening_mono hhh' _))
  have hF0 : ∀ (p : P) h, 0 ≤ F p h := fun _ _ => ENNReal.toReal_nonneg
  have hF1 : ∀ (p : P) h, F p h ≤ 1 := by
    intro p h
    rw [hF]
    dsimp only
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hgeo : ∀ (p : P) (n : ℕ), F p (h₀ * q ^ n) ≤ θ ^ n := by
    intro p n
    rw [hF]
    dsimp only
    refine ENNReal.toReal_le_of_le_ofReal (pow_nonneg hθ0.le n) ?_
    rw [Measure.map_apply (S.measurable_map p.1.1) Metric.isClosed_cthickening.measurableSet]
    refine hU.measure_preimage_cthickening_le_pow S hμ hdim hb hbU p.2 n (S.map p.1.1)
      (S.shift p.1.1) (S.sign p.1.1 * S.ratio p.1.1) (fun x => by simp [System.map]; ring)
      (S.sign_mul_ratio_ne_zero p.1.1) subset_rfl (h₀ * q ^ n) (by positivity) ?_
    rw [S.abs_sign_mul_ratio, hh₀, hq, ← pow_mul, mul_comm m n]
    have hri := S.minRatio_le p.1.1
    have hpow : 0 < S.minRatio ^ (n * m) := pow_pos hrmin _
    have hlt : b * S.minRatio / 2 < b * S.ratio p.1.1 := by nlinarith
    exact mul_lt_mul_of_pos_right hlt hpow
  obtain ⟨C₁, η₁, hC₁, hη₁, hbound⟩ :=
    exists_rpow_bound_of_geometric F hmono hF0 hF1 hh₀0 hq0 hq1 hθ0 hθ1 hgeo
  -- the exponent is decreased into `(0, 1-s)`
  set η : ℝ := min η₁ ((1 - s) / 2) with hη
  have hη0 : 0 < η := lt_min hη₁ (by linarith)
  have hηs : η < 1 - s := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hAone := hA.one_le_const
  have hrs : S.minRatio ^ s ≤ 1 := Real.rpow_le_one hrmin.le hrmin1.le hs0.le
  have hrs0 : 0 < S.minRatio ^ s := Real.rpow_pos_of_pos hrmin s
  set C : ℝ := A * C₁ / S.minRatio ^ s with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  have hC₁C : C₁ ≤ C := by
    rw [hC, le_div_iff₀ hrs0]
    nlinarith
  refine ⟨C, η, hC0, hη0, hηs, fun i j hij h h0 h1 => ?_⟩
  have hbd : (μ.map (S.map i)) (cthickening h (S.map j '' K)) ≤ ENNReal.ofReal (C₁ * h ^ η) := by
    have hFle := hbound ⟨(i, j), hij⟩ h h0 h1
    rw [hF] at hFle
    dsimp only at hFle
    rw [← ENNReal.ofReal_toReal (measure_ne_top (μ.map (S.map i)) _)]
    refine ENNReal.ofReal_le_ofReal (hFle.trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge h0 h1 hηη₁) hC₁.le
  refine ⟨hbd.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have := Real.rpow_nonneg h0.le η
    nlinarith
  · calc ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ h}
        ≤ ENNReal.ofReal (A * (h / S.ratio j) ^ s) *
          (μ.map (S.map i)) (cthickening h (S.map j '' K)) :=
          hμ.prod_map_close_le S hs0.le hA i j h0
      _ ≤ ENNReal.ofReal (A * (h / S.ratio j) ^ s) * ENNReal.ofReal (C₁ * h ^ η) := by
          gcongr
      _ = ENNReal.ofReal (A * (h / S.ratio j) ^ s * (C₁ * h ^ η)) :=
          (ENNReal.ofReal_mul (mul_nonneg (by linarith) (Real.rpow_nonneg (div_pos h0 (S.ratio_pos j)).le s))).symm
      _ ≤ ENNReal.ofReal (C * h ^ (s + η)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hrj := S.ratio_pos j
          have hdiv : (h / S.ratio j) ^ s ≤ h ^ s / S.minRatio ^ s := by
            rw [Real.div_rpow h0.le hrj.le]
            refine div_le_div_of_nonneg_left (Real.rpow_nonneg h0.le s) hrs0 ?_
            exact Real.rpow_le_rpow hrmin.le (S.minRatio_le j) hs0.le
          calc A * (h / S.ratio j) ^ s * (C₁ * h ^ η)
              ≤ A * (h ^ s / S.minRatio ^ s) * (C₁ * h ^ η) := by
                gcongr
            _ = C * h ^ (s + η) := by
                rw [hC, Real.rpow_add h0]
                field_simp

/-- **`thm:renewal-recursion`, the bound on the cross term.**  Under the strong open
set condition, `0 ≤ Φ_×(δ) ≤ C δ^{s+η}` for `0 < δ ≤ 1`, with `η ∈ (0, 1-s)`:
`eq:cross-piece-mass` term by term, and `∑_i p_i = 1`. -/
theorem StrongOpenSetCondition.exists_crossPhi_bound {K : Set ℝ}
    (hsosc : S.StrongOpenSetCondition K) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 - s ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      S.crossPhi s μ δ ≤ C * δ ^ (s + η) := by
  classical
  obtain ⟨C, η, hC, hη, hηs, hbound⟩ := hsosc.exists_cross_piece_bound S hs0 hs1 hdim hμ
  refine ⟨C, η, hC, hη, hηs, fun δ hδ0 hδ1 => ?_⟩
  have hδs : 0 ≤ C * δ ^ (s + η) := mul_nonneg hC.le (Real.rpow_nonneg hδ0.le _)
  have hterm : ∀ i j : iota,
      (if i = j then 0 else S.ratio i ^ s * S.ratio j ^ s *
        (((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal)
      ≤ S.ratio i ^ s * S.ratio j ^ s * (C * δ ^ (s + η)) := by
    intro i j
    have hpi : 0 ≤ S.ratio i ^ s := Real.rpow_nonneg (S.ratio_pos i).le s
    have hpj : 0 ≤ S.ratio j ^ s := Real.rpow_nonneg (S.ratio_pos j).le s
    split_ifs with hij
    · positivity
    · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hpi hpj)
      exact ENNReal.toReal_le_of_le_ofReal hδs (hbound i j hij δ hδ0 hδ1).2
  calc S.crossPhi s μ δ
      ≤ ∑ i, ∑ j, S.ratio i ^ s * S.ratio j ^ s * (C * δ ^ (s + η)) := by
        unfold System.crossPhi
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (∑ i, S.ratio i ^ s) * (∑ j, S.ratio j ^ s) * (C * δ ^ (s + η)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = C * δ ^ (s + η) := by rw [hdim, one_mul, one_mul]

end System

end

end BrownianImages
