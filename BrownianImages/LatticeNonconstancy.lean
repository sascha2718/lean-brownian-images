module

/-
`thm:lattice-nonconvergence` of `sec:renewal`, in the form that the correlation profile `G`
of a lattice system has no limit; with the identification of its periodic limit in
`LatticePeriodisation`, this is the non-constancy of `eq:lattice-periodisation`.

Suppose the log-ratios lie in `hℤ`, say `α_i = n_i h`, and `G(w) → C` as `w → ∞`.  The
renewal equation `eq:g-recursion` telescopes over the lattice `x + hℤ` to the periodised
source `eq:lattice-periodisation`, `∑_{k∈ℤ} z(x + kh) = C ∑ p_i n_i`, for every phase `x`.
Comparing the periodised sums at two phases `a ≤ b` gives the Lipschitz bound
`eq:cross-lipschitz` on the cross term, `e^{sa}(Φ_×(e^{-a}) - Φ_×(e^{-b})) ≤ C'(1 - e^{-s(b-a)})`.
Under the open set condition the two compositions `S_i S_j` and `S_j S_i` of distinct
first-level maps have the same linear part and differ by a non-zero translation, and one
more application of self-similarity inside the cross term turns the Lipschitz bound into
`Φ(δ) ≤ K δ`.  Then `G(w) ≤ K e^{-(1-s)w} → 0`, against the lower regularity bound
`G ≥ (r_min/2)^s`.

* `System.crossPhi_mono`: the cross term is monotone in the scale.
* `System.exists_nat_mul_of_lattice`: a lattice span writes every log-ratio as `n_i h`.
* `sum_range_shift_sub`: the telescoping identity behind `eq:lattice-periodisation`.
* `System.tendsto_sum_defect_of_periodic`: `eq:lattice-periodisation` as the limit of the
  symmetric partial sums, for any solution of the renewal equation vanishing at `-∞` and
  any periodic limit; `System.IsNatural.tendsto_sum_renewalDefect_of_periodic` reads it at
  `G`, and `System.IsNatural.tendsto_sum_renewalDefect` is the constant case.
* `System.IsNatural.crossPhi_sub_le_of_tendsto_G`: `eq:cross-lipschitz`.
* `System.IsFeasible.map_comp_ne`, `System.abs_abs_map_comp_sub_le`: the commutator of two
  first-level maps is a non-zero translation, and the distance estimate it gives.
* `System.IsNatural.smul_map_comp_le`: `μ_j ≥ p_i (S_j S_i)_* μ`.
* `System.IsNatural.sq_mul_phi_le_crossPhi_sub`: the transfer
  `(p_i p_j)² Φ(δ) ≤ Φ_×(x₀ + ρδ) - Φ_×(x₀ - 2ρδ)`.
* `System.IsNatural.not_tendsto_G_of_lattice`: `G` has no limit in the lattice case, the
  form of `thm:lattice-nonconvergence` this argument gives; `LatticePeriodisation` turns it
  into the non-constancy of `eq:lattice-periodisation` and assembles the lattice branch of
  `thm:profile-asymptotics`.
-/
public import BrownianImages.LatticeProfile
public import BrownianImages.FourierMultiplier
public import BrownianImages.HomogeneousNonconstancy

@[expose] public section

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The telescoping identity `∑_{k<L} (v(k+n) - v(k)) = ∑_{j<n} (v(L+j) - v(j))`, the
finite form of the summation in `eq:lattice-periodisation`. -/
theorem sum_range_shift_sub (v : ℕ → ℝ) (n : ℕ) :
    ∀ L : ℕ, ∑ k ∈ Finset.range L, (v (k + n) - v k)
      = ∑ j ∈ Finset.range n, (v (L + j) - v j)
  | 0 => by simp
  | L + 1 => by
      rw [Finset.sum_range_succ, sum_range_shift_sub v n L]
      have h : ∑ j ∈ Finset.range n, (v (L + 1 + j) - v j)
          = ∑ j ∈ Finset.range n, (v (L + j) - v j)
            + ∑ j ∈ Finset.range n, (v (L + (j + 1)) - v (L + j)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show L + 1 + j = L + (j + 1) by ring]
        ring
      rw [h, Finset.sum_range_sub (fun j => v (L + j)) n]
      simp only [add_zero]

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The cross term `Φ_×` is monotone in the scale. -/
theorem crossPhi_mono (s : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] {δ δ' : ℝ}
    (h : δ ≤ δ') : S.crossPhi s μ δ ≤ S.crossPhi s μ δ' := by
  classical
  unfold crossPhi
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact le_rfl
  · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.rpow_nonneg (S.ratio_pos i).le s)
      (Real.rpow_nonneg (S.ratio_pos j).le s))
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun p hp => le_trans hp h)

/-- A lattice span `h` writes every log-ratio as `n_i h` with `n_i : ℕ`. -/
theorem exists_nat_mul_of_lattice {h : ℝ} (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h) (i : ι) :
    ∃ n : ℕ, S.logRatio i = n * h := by
  have hmem : S.logRatio i ∈ AddSubgroup.closure (Set.range S.logRatio) :=
    AddSubgroup.subset_closure ⟨i, rfl⟩
  rw [hlat, AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  rw [zsmul_eq_mul] at hk
  have hpos := S.logRatio_pos i
  have hk0 : 0 ≤ k := by
    by_contra hneg
    push Not at hneg
    have hkr : (k : ℝ) < 0 := by exact_mod_cast hneg
    nlinarith
  refine ⟨k.toNat, ?_⟩
  rw [← hk]
  congr 1
  have := Int.toNat_of_nonneg hk0
  exact_mod_cast this.symm

/-- Under the open set condition two distinct first-level maps do not commute: `S_i S_j`
and `S_j S_i` have the same linear part, so they differ at `0`. -/
theorem IsFeasible.map_comp_ne {U : Set ℝ} (hU : S.IsFeasible U) {i j : ι} (hij : i ≠ j) :
    S.map i (S.map j 0) ≠ S.map j (S.map i 0) := by
  intro heq
  obtain ⟨u, hu⟩ := hU.nonempty
  have hfun : ∀ x, S.map i (S.map j x) = S.map j (S.map i x) := by
    intro x
    have h1 := S.map_sub i (S.map j x) (S.map j 0)
    have h2 := S.map_sub j x 0
    have h3 := S.map_sub j (S.map i x) (S.map i 0)
    have h4 := S.map_sub i x 0
    rw [h2] at h1
    rw [h4] at h3
    linear_combination h1 - h3 + heq
  have hmem1 : S.map i (S.map j u) ∈ S.map i '' U := ⟨S.map j u, hU.mapsTo j hu, rfl⟩
  have hmem2 : S.map i (S.map j u) ∈ S.map j '' U := by
    rw [hfun]
    exact ⟨S.map i u, hU.mapsTo i hu, rfl⟩
  exact Set.disjoint_left.mp (hU.disjoint i j hij) hmem1 hmem2

/-- `||S_i S_j x - S_j S_i y| - x₀| ≤ r_i r_j |x - y|` with `x₀ = |S_i S_j 0 - S_j S_i 0|`:
the two compositions differ by the translation `x₀` up to the common linear part. -/
theorem abs_abs_map_comp_sub_le (i j : ι) (x y : ℝ) :
    abs (|S.map i (S.map j x) - S.map j (S.map i y)| - |S.map i (S.map j 0) - S.map j (S.map i 0)|)
      ≤ S.ratio i * S.ratio j * |x - y| := by
  have h1 := S.map_sub i (S.map j x) (S.map j 0)
  have h2 := S.map_sub j x 0
  have h3 := S.map_sub j (S.map i y) (S.map i 0)
  have h4 := S.map_sub i y 0
  rw [h2] at h1
  rw [h4] at h3
  have hkey : S.map i (S.map j x) - S.map j (S.map i y)
      = (S.map i (S.map j 0) - S.map j (S.map i 0))
        + (S.sign i * S.ratio i) * (S.sign j * S.ratio j) * (x - y) := by
    linear_combination h1 - h3
  calc abs (|S.map i (S.map j x) - S.map j (S.map i y)|
          - |S.map i (S.map j 0) - S.map j (S.map i 0)|)
      ≤ |(S.map i (S.map j x) - S.map j (S.map i y))
          - (S.map i (S.map j 0) - S.map j (S.map i 0))| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |(S.sign i * S.ratio i) * (S.sign j * S.ratio j) * (x - y)| := by
        rw [hkey]
        congr 1
        ring
    _ = S.ratio i * S.ratio j * |x - y| := by
        rw [abs_mul, abs_mul, S.abs_sign_mul_ratio, S.abs_sign_mul_ratio]

/-- One more application of self-similarity inside a first-level piece:
`μ_j ≥ p_i (S_j S_i)_* μ`. -/
theorem IsNatural.smul_map_comp_le {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (i j : ι) :
    ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map j ∘ S.map i) ≤ μ.map (S.map j) := by
  rw [Measure.le_iff]
  intro B hB
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply ((S.measurable_map j).comp (S.measurable_map i)) hB,
    Measure.map_apply (S.measurable_map j) hB, hμ.measure_eq_sum S ((S.measurable_map j) hB),
    Set.preimage_comp]
  exact Finset.single_le_sum
    (f := fun k => ENNReal.ofReal (S.ratio k ^ s) * μ (S.map k ⁻¹' (S.map j ⁻¹' B)))
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- The transfer step of `thm:lattice-nonconvergence`: for `i ≠ j`, `x₀ = |S_i S_j 0 - S_j S_i 0|`,
`ρ = r_i r_j` and `0 < δ`,
`(p_i p_j)² Φ(δ) ≤ Φ_×(x₀ + ρδ) - Φ_×(x₀ - 2ρδ)`.  The pairs `(S_i S_j x, S_j S_i y)` with
`|x - y| ≤ δ` have distance within `ρδ` of `x₀`, and `μ_i × μ_j ≥ p_i p_j ((S_i S_j)_* μ × (S_j S_i)_* μ)`. -/
theorem IsNatural.sq_mul_phi_le_crossPhi_sub {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {i j : ι} (hij : i ≠ j) {x₀ ρ δ : ℝ}
    (hx₀ : x₀ = |S.map i (S.map j 0) - S.map j (S.map i 0)|) (hρ : ρ = S.ratio i * S.ratio j)
    (hδ : 0 < δ) :
    (S.ratio i ^ s * S.ratio j ^ s) ^ 2 * Phi μ δ
      ≤ S.crossPhi s μ (x₀ + ρ * δ) - S.crossPhi s μ (x₀ - 2 * ρ * δ) := by
  classical
  have := hμ.isProbabilityMeasure
  have hρpos : 0 < ρ := by rw [hρ]; exact mul_pos (S.ratio_pos i) (S.ratio_pos j)
  have hpi : 0 < S.ratio i ^ s := Real.rpow_pos_of_pos (S.ratio_pos i) s
  have hpj : 0 < S.ratio j ^ s := Real.rpow_pos_of_pos (S.ratio_pos j) s
  have hle : x₀ - 2 * ρ * δ ≤ x₀ + ρ * δ := by nlinarith
  have hmi : Measurable (S.map i ∘ S.map j) := (S.measurable_map i).comp (S.measurable_map j)
  have hmj : Measurable (S.map j ∘ S.map i) := (S.measurable_map j).comp (S.measurable_map i)
  have hdist : Measurable fun p : ℝ × ℝ => |p.1 - p.2| :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => |p.1 - p.2|).measurable
  -- the pairs with distances in `(x₀ - 2ρδ, x₀ + ρδ]`
  set Ann : Set (ℝ × ℝ) :=
    {p | x₀ - 2 * ρ * δ < |p.1 - p.2| ∧ |p.1 - p.2| ≤ x₀ + ρ * δ} with hAnn_def
  have hAnn : MeasurableSet Ann :=
    (measurableSet_lt measurable_const hdist).inter (measurableSet_le hdist measurable_const)
  set ν : Measure (ℝ × ℝ) := (μ.map (S.map i)).prod (μ.map (S.map j)) with hν_def
  -- the annulus is the difference of the two sets of close pairs
  have hunion : {p : ℝ × ℝ | |p.1 - p.2| ≤ x₀ + ρ * δ}
      = {p : ℝ × ℝ | |p.1 - p.2| ≤ x₀ - 2 * ρ * δ} ∪ Ann := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, hAnn_def]
    constructor
    · intro h
      by_cases h1 : |p.1 - p.2| ≤ x₀ - 2 * ρ * δ
      · exact Or.inl h1
      · exact Or.inr ⟨lt_of_not_ge h1, h⟩
    · rintro (h | ⟨_, h⟩)
      · exact h.trans hle
      · exact h
  have hdisj : Disjoint {p : ℝ × ℝ | |p.1 - p.2| ≤ x₀ - 2 * ρ * δ} Ann := by
    rw [Set.disjoint_left]
    rintro p hp ⟨h1, _⟩
    exact absurd hp (not_le.mpr h1)
  have hsplit : (ν {p : ℝ × ℝ | |p.1 - p.2| ≤ x₀ + ρ * δ}).toReal
      - (ν {p : ℝ × ℝ | |p.1 - p.2| ≤ x₀ - 2 * ρ * δ}).toReal = (ν Ann).toReal := by
    rw [hunion, measure_union hdisj hAnn,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    ring
  -- the pairs `(S_i S_j x, S_j S_i y)` with `|x - y| ≤ δ` land in the annulus
  have hsub : {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}
      ⊆ Prod.map (S.map i ∘ S.map j) (S.map j ∘ S.map i) ⁻¹' Ann := by
    rintro ⟨x, y⟩ hxy
    simp only [Set.mem_ofPred_eq] at hxy
    have hb := S.abs_abs_map_comp_sub_le i j x y
    rw [← hx₀, ← hρ, abs_le] at hb
    have hρδ : ρ * |x - y| ≤ ρ * δ := mul_le_mul_of_nonneg_left hxy hρpos.le
    simp only [Set.mem_preimage, Prod.map_apply, Function.comp_apply, hAnn_def,
      Set.mem_ofPred_eq]
    constructor <;> nlinarith [hb.1, hb.2]
  -- `μ_i × μ_j ≥ p_i p_j ((S_i S_j)_* μ × (S_j S_i)_* μ)` on the annulus
  have hle_i := hμ.smul_map_comp_le S j i
  have hle_j := hμ.smul_map_comp_le S i j
  have hlow : ENNReal.ofReal (S.ratio i ^ s * S.ratio j ^ s)
      * (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≤ ν Ann := by
    calc ENNReal.ofReal (S.ratio i ^ s * S.ratio j ^ s)
          * (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}
        ≤ ENNReal.ofReal (S.ratio i ^ s * S.ratio j ^ s)
          * (μ.prod μ) (Prod.map (S.map i ∘ S.map j) (S.map j ∘ S.map i) ⁻¹' Ann) :=
          mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le
      _ = ENNReal.ofReal (S.ratio j ^ s) * (ENNReal.ofReal (S.ratio i ^ s)
          * ((μ.map (S.map i ∘ S.map j)).prod (μ.map (S.map j ∘ S.map i))) Ann) := by
          rw [Measure.map_prod_map μ μ hmi hmj, Measure.map_apply (hmi.prodMap hmj) hAnn,
            ← mul_assoc, ← ENNReal.ofReal_mul hpj.le, mul_comm (S.ratio j ^ s) (S.ratio i ^ s)]
      _ = ∫⁻ x, (ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map j ∘ S.map i)) (Prod.mk x ⁻¹' Ann)
            ∂(ENNReal.ofReal (S.ratio j ^ s) • μ.map (S.map i ∘ S.map j)) := by
          rw [lintegral_smul_measure, Measure.prod_apply hAnn]
          simp only [Measure.smul_apply, smul_eq_mul]
          rw [lintegral_const_mul _ (measurable_measure_prodMk_left hAnn)]
      _ ≤ ∫⁻ x, (μ.map (S.map j)) (Prod.mk x ⁻¹' Ann) ∂(μ.map (S.map i)) :=
          lintegral_mono' hle_i fun x => Measure.le_iff.mp hle_j _ (measurable_prodMk_left hAnn)
      _ = ν Ann := (Measure.prod_apply hAnn).symm
  have hlow' : S.ratio i ^ s * S.ratio j ^ s * Phi μ δ ≤ (ν Ann).toReal := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_pos hpi hpj).le] at h
  -- extract the `(i, j)` term of the cross term
  set T : ι → ι → ℝ → ℝ := fun k l δ' => if k = l then 0 else
    S.ratio k ^ s * S.ratio l ^ s *
      (((μ.map (S.map k)).prod (μ.map (S.map l))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ'}).toReal
    with hT
  have hcross : ∀ δ', S.crossPhi s μ δ' = ∑ k, ∑ l, T k l δ' := fun δ' => rfl
  have hnn : ∀ k l, 0 ≤ T k l (x₀ + ρ * δ) - T k l (x₀ - 2 * ρ * δ) := by
    intro k l
    simp only [hT]
    split_ifs
    · simp
    · rw [← mul_sub]
      refine mul_nonneg (mul_nonneg (Real.rpow_nonneg (S.ratio_pos k).le s)
        (Real.rpow_nonneg (S.ratio_pos l).le s)) (sub_nonneg.mpr ?_)
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun p hp => le_trans hp hle)
  have hstep : S.ratio i ^ s * S.ratio j ^ s * (ν Ann).toReal
      ≤ S.crossPhi s μ (x₀ + ρ * δ) - S.crossPhi s μ (x₀ - 2 * ρ * δ) := by
    rw [hcross, hcross, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc S.ratio i ^ s * S.ratio j ^ s * (ν Ann).toReal
        = T i j (x₀ + ρ * δ) - T i j (x₀ - 2 * ρ * δ) := by
          simp only [hT, ite_eq_right hij]
          rw [← mul_sub, hsplit]
      _ ≤ ∑ l, (T i l (x₀ + ρ * δ) - T i l (x₀ - 2 * ρ * δ)) :=
          Finset.single_le_sum (fun l _ => hnn i l) (Finset.mem_univ j)
      _ ≤ ∑ k, ∑ l, (T k l (x₀ + ρ * δ) - T k l (x₀ - 2 * ρ * δ)) :=
          Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hnn k l)
            (Finset.mem_univ i)
  calc (S.ratio i ^ s * S.ratio j ^ s) ^ 2 * Phi μ δ
      = S.ratio i ^ s * S.ratio j ^ s * (S.ratio i ^ s * S.ratio j ^ s * Phi μ δ) := by ring
    _ ≤ S.ratio i ^ s * S.ratio j ^ s * (ν Ann).toReal :=
        mul_le_mul_of_nonneg_left hlow' (mul_pos hpi hpj).le
    _ ≤ _ := hstep

/-- **`eq:lattice-periodisation`**, as the limit of symmetric partial sums.  If every
log-ratio is `n_i h`, `f` vanishes at `-∞`, and `f - g → 0` at `+∞` for an `h`-periodic
`g`, the symmetric partial sums `∑_{|k|≤N} z(x + kh)` of the defect `z = f - ϑ * f`
converge to `g(x) ∑ p_i n_i`, for every phase `x`: the renewal equation writes `z` as
`∑ p_i (f(w) - f(w - n_i h))`, and each difference telescopes over the lattice. -/
theorem tendsto_sum_defect_of_periodic {s h : ℝ} (hdim : S.IsDimension s) {f : ℝ → ℝ}
    (hbot : Tendsto f atBot (𝓝 0)) (n : ι → ℕ) (hn : ∀ i, S.logRatio i = n i * h)
    {g : ℝ → ℝ} (hgp : Function.Periodic g h)
    (hg : Tendsto (fun w => f w - g w) atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1),
        (f (x + ((k : ℝ) - N) * h) - S.renewalConv s f (x + ((k : ℝ) - N) * h))) atTop
      (𝓝 (g x * ∑ i, S.ratio i ^ s * n i)) := by
  have hdim' : ∑ i, S.ratio i ^ s = 1 := hdim
  have hz : ∀ w, f w - S.renewalConv s f w
      = ∑ i, S.ratio i ^ s * (f w - f (w - n i * h)) := by
    intro w
    rw [renewalConv]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hdim', one_mul, hn]
  have hsum : ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N + 1),
        (f (x + ((k : ℝ) - N) * h) - S.renewalConv s f (x + ((k : ℝ) - N) * h))
      = ∑ i, S.ratio i ^ s * ∑ j ∈ Finset.range (n i),
          (f (x + (((2 * N + 1 + j : ℕ) : ℝ) - N - n i) * h)
            - f (x + ((j : ℝ) - N - n i) * h)) := by
    intro N
    simp only [hz]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have key := sum_range_shift_sub (fun k : ℕ => f (x + ((k : ℝ) - N - n i) * h)) (n i)
      (2 * N + 1)
    refine (Finset.sum_congr rfl fun k _ => ?_).trans
      (key.trans (Finset.sum_congr rfl fun j _ => ?_))
    · congr 2 <;> push_cast <;> ring
    · simp only []
  refine Tendsto.congr (fun N => (hsum N).symm) ?_
  rw [Finset.mul_sum]
  refine tendsto_finsetSum _ fun i _ => ?_
  have hh : 0 < h := by
    have := S.logRatio_pos i
    rw [hn i] at this
    rcases (Nat.eq_zero_or_pos (n i)) with h0 | h0
    · simp [h0] at this
    · exact pos_of_mul_pos_right this (by positivity)
  have hsumg : ∑ _j ∈ Finset.range (n i), (g x - 0) = n i * g x := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_zero]
  rw [show g x * (S.ratio i ^ s * n i) = S.ratio i ^ s * (n i * g x) by ring, ← hsumg]
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => Tendsto.sub ?_ ?_)
  · have ht : Tendsto (fun N : ℕ => (N : ℝ) * h + (x + (1 + j - n i) * h)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hh)
    have ht' : Tendsto (fun N : ℕ => x + (((2 * N + 1 + j : ℕ) : ℝ) - N - n i) * h)
        atTop atTop := ht.congr fun N => by push_cast; ring
    have hper : ∀ N : ℕ, g (x + (((2 * N + 1 + j : ℕ) : ℝ) - N - n i) * h) = g x := by
      intro N
      have := hgp.int_mul ((N : ℤ) + 1 + j - n i) x
      convert this using 2
      push_cast
      ring
    have hlim := (hg.comp ht').add_const (g x)
    rw [zero_add] at hlim
    refine hlim.congr fun N => ?_
    simp only [Function.comp_apply, hper]
    ring
  · have ht : Tendsto (fun N : ℕ => -((N : ℝ) * h) + (x + (j - n i) * h)) atTop atBot :=
      tendsto_atBot_add_const_right _ _
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hh))
    refine hbot.comp (ht.congr fun N => ?_)
    ring

/-- `eq:lattice-periodisation` for the correlation profile `G` and its renewal defect
`z = G - ϑ * G`, which vanishes at `-∞`. -/
theorem IsNatural.tendsto_sum_renewalDefect_of_periodic {K : Set ℝ} {s h : ℝ} (hs : 0 < s)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (n : ι → ℕ) (hn : ∀ i, S.logRatio i = n i * h) {g : ℝ → ℝ}
    (hgp : Function.Periodic g h) (hg : Tendsto (fun w => G s μ w - g w) atTop (𝓝 0))
    (x : ℝ) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1),
        S.renewalDefect s μ (x + ((k : ℝ) - N) * h)) atTop
      (𝓝 (g x * ∑ i, S.ratio i ^ s * n i)) := by
  have := hμ.isProbabilityMeasure
  exact S.tendsto_sum_defect_of_periodic hdim
    (HomogeneousNonconstancy.tendsto_G_atBot_zero hs) n hn hgp hg x

/-- `eq:lattice-periodisation` under a constant limit `G(w) → C`: the symmetric partial
sums of the renewal defect converge to `C ∑ p_i n_i`. -/
theorem IsNatural.tendsto_sum_renewalDefect {K : Set ℝ} {s h C : ℝ} (hs : 0 < s)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (n : ι → ℕ) (hn : ∀ i, S.logRatio i = n i * h)
    (hC : Tendsto (G s μ) atTop (𝓝 C)) (x : ℝ) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1),
        S.renewalDefect s μ (x + ((k : ℝ) - N) * h)) atTop
      (𝓝 (C * ∑ i, S.ratio i ^ s * n i)) :=
  hμ.tendsto_sum_renewalDefect_of_periodic S hs hdim n hn (g := fun _ => C) (fun _ => rfl)
    (by simpa using hC.sub_const C) x

/-- **`eq:cross-lipschitz`.**  Under `G(w) → C` and the lattice hypothesis, for `a ≤ b`,
`e^{sa}(Φ_×(e^{-a}) - Φ_×(e^{-b})) ≤ C'(1 - e^{-s(b-a)})` with `C' = C ∑ p_i n_i`: the
periodised sums at the phases `a` and `b` agree, their difference is a sum of non-negative
terms, and the term `k = 0` is the left-hand side. -/
theorem IsNatural.crossPhi_sub_le_of_tendsto_G {K : Set ℝ} {s h C : ℝ} (hs : 0 < s)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (n : ι → ℕ) (hn : ∀ i, S.logRatio i = n i * h)
    (hC : Tendsto (G s μ) atTop (𝓝 C)) {a b : ℝ} (hab : a ≤ b) :
    Real.exp (s * a) * (S.crossPhi s μ (Real.exp (-a)) - S.crossPhi s μ (Real.exp (-b)))
      ≤ (C * ∑ i, S.ratio i ^ s * n i) * (1 - Real.exp (-(s * (b - a)))) := by
  have := hμ.isProbabilityMeasure
  have hA := hμ.tendsto_sum_renewalDefect S hs hdim n hn hC a
  have hB := hμ.tendsto_sum_renewalDefect S hs hdim n hn hC b
  have hN : ∀ N : ℕ,
      Real.exp (s * a) * (S.crossPhi s μ (Real.exp (-a)) - S.crossPhi s μ (Real.exp (-b)))
        ≤ (∑ k ∈ Finset.range (2 * N + 1), S.renewalDefect s μ (a + ((k : ℝ) - N) * h))
          - Real.exp (-(s * (b - a))) *
            ∑ k ∈ Finset.range (2 * N + 1), S.renewalDefect s μ (b + ((k : ℝ) - N) * h) := by
    intro N
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ k : ℕ, S.renewalDefect s μ (a + ((k : ℝ) - N) * h)
        - Real.exp (-(s * (b - a))) * S.renewalDefect s μ (b + ((k : ℝ) - N) * h)
        = Real.exp (s * (a + ((k : ℝ) - N) * h)) *
          (S.crossPhi s μ (Real.exp (-(a + ((k : ℝ) - N) * h)))
            - S.crossPhi s μ (Real.exp (-(b + ((k : ℝ) - N) * h)))) := by
      intro k
      rw [renewalDefect_eq_crossPhi S hμ, renewalDefect_eq_crossPhi S hμ]
      have he : Real.exp (-(s * (b - a))) * Real.exp (s * (b + ((k : ℝ) - N) * h))
          = Real.exp (s * (a + ((k : ℝ) - N) * h)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      linear_combination (-(S.crossPhi s μ (Real.exp (-(b + ((k : ℝ) - N) * h))))) * he
    have hnonneg : ∀ k : ℕ, 0 ≤ Real.exp (s * (a + ((k : ℝ) - N) * h)) *
          (S.crossPhi s μ (Real.exp (-(a + ((k : ℝ) - N) * h)))
            - S.crossPhi s μ (Real.exp (-(b + ((k : ℝ) - N) * h)))) := by
      intro k
      refine mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr ?_)
      exact S.crossPhi_mono s μ (Real.exp_le_exp.mpr (by linarith))
    simp only [hterm]
    have hmem : N ∈ Finset.range (2 * N + 1) := Finset.mem_range.mpr (by omega)
    calc Real.exp (s * a) * (S.crossPhi s μ (Real.exp (-a)) - S.crossPhi s μ (Real.exp (-b)))
        = Real.exp (s * (a + ((N : ℝ) - N) * h)) *
          (S.crossPhi s μ (Real.exp (-(a + ((N : ℝ) - N) * h)))
            - S.crossPhi s μ (Real.exp (-(b + ((N : ℝ) - N) * h)))) := by simp
      _ ≤ _ := Finset.single_le_sum (fun k _ => hnonneg k) hmem
  have hlim := hA.sub (hB.const_mul (Real.exp (-(s * (b - a)))))
  have hle := ge_of_tendsto' hlim hN
  calc _ ≤ _ := hle
    _ = _ := by ring

variable [Nonempty ι]

/-- **`thm:lattice-nonconvergence`.**  Under the open set condition, if every log-ratio is
an integer multiple of some `h > 0`, the normalised correlation profile `G` has no limit
at `+∞`: a limit `C` would give `eq:lattice-periodisation` and `eq:cross-lipschitz`, hence
`Φ(δ) ≤ Kδ` and `G → 0`, while `G ≥ (r_min/2)^s > 0` on `[0, ∞)`. -/
theorem IsNatural.not_tendsto_G_of_lattice {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    (hlat : ∀ i, ∃ n : ℕ, S.logRatio i = n * h) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (C : ℝ) : ¬ Tendsto (G s μ) atTop (𝓝 C) := by
  classical
  intro hC
  have := hμ.isProbabilityMeasure
  choose n hn using hlat
  obtain ⟨U, hU⟩ := hosc
  -- the limit is positive
  have hCpos : 0 < C := by
    have hlow : (S.minRatio / 2) ^ s ≤ C :=
      ge_of_tendsto hC (eventually_atTop.2 ⟨0, fun w hw => hμ.lower_bound_G S hs0.le hw⟩)
    have hr := S.minRatio_pos
    exact (Real.rpow_pos_of_pos (by positivity) s).trans_le hlow
  -- two distinct letters, since `∑ r_i^s = 1` with every `r_i^s < 1`
  obtain ⟨i, j, hij⟩ : ∃ i j : ι, i ≠ j := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have huniv : (Finset.univ : Finset ι) = {i₀} := by
      ext k
      simp [hcon k i₀]
    have h1 : ∑ k, S.ratio k ^ s = S.ratio i₀ ^ s := by rw [huniv, Finset.sum_singleton]
    have hlt : S.ratio i₀ ^ s < 1 :=
      Real.rpow_lt_one (S.ratio_pos i₀).le (S.ratio_lt_one i₀) hs0
    rw [hdim] at h1
    linarith
  obtain ⟨x₀, hx₀def⟩ : ∃ x₀ : ℝ, x₀ = |S.map i (S.map j 0) - S.map j (S.map i 0)| := ⟨_, rfl⟩
  have hx₀ : 0 < x₀ := by rw [hx₀def]; exact abs_pos.mpr (sub_ne_zero.mpr (hU.map_comp_ne S hij))
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = S.ratio i * S.ratio j := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos (S.ratio_pos i) (S.ratio_pos j)
  have hpij : 0 < S.ratio i ^ s * S.ratio j ^ s :=
    mul_pos (Real.rpow_pos_of_pos (S.ratio_pos i) s) (Real.rpow_pos_of_pos (S.ratio_pos j) s)
  obtain ⟨C', hC'def⟩ : ∃ C' : ℝ, C' = C * ∑ k, S.ratio k ^ s * n k := ⟨_, rfl⟩
  have hC'nn : 0 ≤ C' := by
    rw [hC'def]
    exact mul_nonneg hCpos.le (Finset.sum_nonneg fun k _ =>
      mul_nonneg (Real.rpow_pos_of_pos (S.ratio_pos k) s).le (Nat.cast_nonneg _))
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ,
      Kc = C' * (2 * x₀) ^ s * (3 * ρ / x₀) / (S.ratio i ^ s * S.ratio j ^ s) ^ 2 := ⟨_, rfl⟩
  -- the linear bound `Φ(δ) ≤ K δ` for small `δ`
  have hPhi : ∀ δ : ℝ, 0 < δ → 2 * ρ * δ < x₀ → ρ * δ ≤ x₀ → Phi μ δ ≤ Kc * δ := by
    intro δ hδ h2 h1
    have htr := hμ.sq_mul_phi_le_crossPhi_sub S hij hx₀def hρdef hδ
    have hδ₁ : 0 < x₀ - 2 * ρ * δ := by linarith
    have hδ₂ : 0 < x₀ + ρ * δ := by positivity
    have hle : x₀ - 2 * ρ * δ ≤ x₀ + ρ * δ := by nlinarith
    have hlip := hμ.crossPhi_sub_le_of_tendsto_G S hs0 hdim n hn hC
      (a := -Real.log (x₀ + ρ * δ)) (b := -Real.log (x₀ - 2 * ρ * δ))
      (by linarith [Real.log_le_log hδ₁ hle])
    rw [← hC'def] at hlip
    have e1 : Real.exp (-(-Real.log (x₀ + ρ * δ))) = x₀ + ρ * δ := by
      rw [neg_neg, Real.exp_log hδ₂]
    have e2 : Real.exp (-(-Real.log (x₀ - 2 * ρ * δ))) = x₀ - 2 * ρ * δ := by
      rw [neg_neg, Real.exp_log hδ₁]
    have e3 : Real.exp (s * -Real.log (x₀ + ρ * δ)) = ((x₀ + ρ * δ) ^ s)⁻¹ := by
      rw [Real.rpow_def_of_pos hδ₂, ← Real.exp_neg]
      congr 1
      ring
    have e4 : Real.exp (-(s * (-Real.log (x₀ - 2 * ρ * δ) - -Real.log (x₀ + ρ * δ))))
        = ((x₀ - 2 * ρ * δ) / (x₀ + ρ * δ)) ^ s := by
      rw [Real.rpow_def_of_pos (div_pos hδ₁ hδ₂), Real.log_div hδ₁.ne' hδ₂.ne']
      congr 1
      ring
    rw [e1, e2, e3, e4] at hlip
    have hδ₂s : 0 < (x₀ + ρ * δ) ^ s := Real.rpow_pos_of_pos hδ₂ s
    have hge : (x₀ - 2 * ρ * δ) / (x₀ + ρ * δ) ≤ ((x₀ - 2 * ρ * δ) / (x₀ + ρ * δ)) ^ s := by
      have := Real.rpow_le_rpow_of_exponent_ge (div_pos hδ₁ hδ₂)
        ((div_le_one hδ₂).mpr hle) hs1.le
      rwa [Real.rpow_one] at this
    have hcross : S.crossPhi s μ (x₀ + ρ * δ) - S.crossPhi s μ (x₀ - 2 * ρ * δ)
        ≤ (x₀ + ρ * δ) ^ s * (C' * (1 - (x₀ - 2 * ρ * δ) / (x₀ + ρ * δ))) := by
      have h1' := mul_le_mul_of_nonneg_left hlip hδ₂s.le
      rw [← mul_assoc, mul_inv_cancel₀ hδ₂s.ne', one_mul] at h1'
      refine h1'.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC'nn) hδ₂s.le)
      linarith
    have hfrac : 1 - (x₀ - 2 * ρ * δ) / (x₀ + ρ * δ) = 3 * ρ * δ / (x₀ + ρ * δ) := by
      field_simp
      ring
    have hδ₂le : (x₀ + ρ * δ) ^ s ≤ (2 * x₀) ^ s :=
      Real.rpow_le_rpow hδ₂.le (by linarith) hs0.le
    have hbound : (x₀ + ρ * δ) ^ s * (C' * (1 - (x₀ - 2 * ρ * δ) / (x₀ + ρ * δ)))
        ≤ (2 * x₀) ^ s * (C' * (3 * ρ * δ / x₀)) := by
      rw [hfrac]
      refine mul_le_mul hδ₂le (mul_le_mul_of_nonneg_left ?_ hC'nn) (by positivity)
        (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) hx₀ (by linarith)
    have hfinal := htr.trans (hcross.trans hbound)
    have hpi' : S.ratio i ^ s ≠ 0 := (Real.rpow_pos_of_pos (S.ratio_pos i) s).ne'
    have hpj' : S.ratio j ^ s ≠ 0 := (Real.rpow_pos_of_pos (S.ratio_pos j) s).ne'
    have hrw : (2 * x₀) ^ s * (C' * (3 * ρ * δ / x₀))
        = (Kc * δ) * (S.ratio i ^ s * S.ratio j ^ s) ^ 2 := by
      rw [hKc]
      field_simp
    rw [hrw, mul_comm ((S.ratio i ^ s * S.ratio j ^ s) ^ 2) (Phi μ δ)] at hfinal
    exact le_of_mul_le_mul_right hfinal (by positivity)
  -- hence `G → 0`
  have hG0 : Tendsto (G s μ) atTop (𝓝 0) := by
    have hlim : Tendsto (fun w : ℝ => Kc * Real.exp ((s - 1) * w)) atTop (𝓝 0) := by
      have hneg : Tendsto (fun w : ℝ => (s - 1) * w) atTop atBot := by
        have h1 : Tendsto (fun w : ℝ => (1 - s) * w) atTop atTop :=
          tendsto_id.const_mul_atTop (by linarith)
        refine (tendsto_neg_atTop_atBot.comp h1).congr fun w => ?_
        simp only [Function.comp_apply]
        ring
      simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul Kc
    refine squeeze_zero' (Eventually.of_forall fun w => G_nonneg w) ?_ hlim
    filter_upwards [eventually_gt_atTop (Real.log (2 * ρ / x₀))] with w hw
    have hδ : Real.exp (-w) < x₀ / (2 * ρ) := by
      have hl : Real.log (x₀ / (2 * ρ)) = -Real.log (2 * ρ / x₀) := by
        rw [← Real.log_inv, inv_div]
      calc Real.exp (-w) < Real.exp (Real.log (x₀ / (2 * ρ))) :=
            Real.exp_lt_exp.mpr (by rw [hl]; linarith)
        _ = x₀ / (2 * ρ) := Real.exp_log (by positivity)
    have h2 : 2 * ρ * Real.exp (-w) < x₀ := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * ρ)).mp hδ
      linarith
    have h1 : ρ * Real.exp (-w) ≤ x₀ := by
      have := Real.exp_pos (-w)
      nlinarith
    calc G s μ w = Real.exp (s * w) * Phi μ (Real.exp (-w)) := rfl
      _ ≤ Real.exp (s * w) * (Kc * Real.exp (-w)) :=
          mul_le_mul_of_nonneg_left (hPhi _ (Real.exp_pos _) h2 h1) (Real.exp_pos _).le
      _ = Kc * Real.exp ((s - 1) * w) := by
          rw [show (s - 1) * w = s * w + -w by ring, Real.exp_add]
          ring
  have hC0 : C = 0 := tendsto_nhds_unique hC hG0
  exact hCpos.ne' hC0

end System

end BrownianImages
