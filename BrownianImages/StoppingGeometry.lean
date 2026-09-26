/-
`thm:stopping-overlap` of `sec:renewal`: the geometry of a stopping family under the
open set condition, and the Ahlfors regularity of the natural measure.

The stopping family `𝒲(u)` of the paper is the leaf set of the finite stopping tree
of `Minkowski.Stopping`, at threshold `u` and at a depth past which every branch has
stopped.  This module adds what the open set condition gives that tree.

* `image_stoppingLeafWord_subset`: the image of a set invariant under the maps, under
  the map of a leaf word, lies in the image under the map of its root.
* `IsFeasible.disjoint_image_stoppingLeafWord`: distinct leaves are incomparable words,
  so their images of a feasible open set are disjoint.
* `IsNatural.measure_preimage_eq_sum_leaves`: the self-similar decomposition
  `p_w (S_w)_* μ = ∑_{leaves} p_v (S_v)_* μ` below any node, `eq:stopping-family`.
* `IsFeasible.exists_multiplicity_bound`: the counting bound of the paper, a uniform
  bound on the number of stopping intervals `I_w` meeting a window `[x-u, x+u]`.
* `IsFeasible.exists_stopping_coloring`: the partition of the stopping intervals into
  at most `M` families with pairwise disjoint interiors.
* `OpenSetCondition.exists_isFrostman`, `OpenSetCondition.exists_isAhlforsClosed`: the
  natural measure is `s`-Ahlfors regular, hence `s`-Frostman.
-/
import BrownianImages.OpenSet
import BrownianImages.IntervalColoring
import BrownianImages.AhlforsRegular
import BrownianImages.Recursion
import BrownianImages.Minkowski.Stopping

namespace BrownianImages

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace System

variable {iota : Type u} [Fintype iota] [Nonempty iota] (S : System iota)

/-! ### The smallest ratio -/

/-- The smallest contraction ratio `r_min` of the system. -/
def minRatio : ℝ := Finset.univ.inf' Finset.univ_nonempty S.ratio

/-- Every ratio is at least the smallest one. -/
theorem minRatio_le (i : iota) : S.minRatio ≤ S.ratio i :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- The smallest ratio is positive. -/
theorem minRatio_pos : 0 < S.minRatio :=
  (Finset.lt_inf'_iff _).2 fun i _ => S.ratio_pos i

/-- The smallest ratio is at most one. -/
theorem minRatio_le_one : S.minRatio ≤ 1 :=
  (S.minRatio_le (Classical.arbitrary iota)).trans (S.ratio_lt_one _).le

/-! ### The map of a stopping word -/

/-- The similarity `S_w` of a stopping word, composed in prefix order. -/
abbrev stoppingWordMap (w : StoppingWord iota) : ℝ → ℝ := S.stoppingMap w.1 w.2

omit [Nonempty iota] in
/-- The map of a child word composes the letter on the inside. -/
theorem stoppingWordMap_child (w : StoppingWord iota) (i : iota) :
    S.stoppingWordMap (stoppingChild w i) = S.stoppingWordMap w ∘ S.map i := rfl

omit [Nonempty iota] in
/-- The root word acts as the identity. -/
theorem stoppingWordMap_root : S.stoppingWordMap (stoppingRoot : StoppingWord iota) = id := rfl

omit [Nonempty iota] in
/-- The map of a stopping word is affine with slope its ratio. -/
theorem stoppingWordMap_sub (w : StoppingWord iota) (x y : ℝ) :
    S.stoppingWordMap w x - S.stoppingWordMap w y = S.stoppingRatio w * (x - y) :=
  S.stoppingMap_sub w.1 w.2 x y

omit [Nonempty iota] in
/-- The map of a stopping word is injective. -/
theorem stoppingWordMap_injective (w : StoppingWord iota) :
    Function.Injective (S.stoppingWordMap w) := by
  intro x y hxy
  have h := S.stoppingWordMap_sub w x y
  rw [hxy, sub_self] at h
  have hr : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have : x - y = 0 := by
    rcases mul_eq_zero.mp h.symm with h0 | h0
    · exact absurd h0 hr.ne'
    · exact h0
  linarith

omit [Nonempty iota] in
/-- The map of a stopping word is continuous. -/
theorem continuous_stoppingWordMap (w : StoppingWord iota) :
    Continuous (S.stoppingWordMap w) :=
  S.continuous_stoppingMap w.1 w.2

omit [Nonempty iota] in
/-- The map of a stopping word is measurable. -/
theorem measurable_stoppingWordMap (w : StoppingWord iota) :
    Measurable (S.stoppingWordMap w) :=
  (S.continuous_stoppingWordMap w).measurable

omit [Nonempty iota] in
/-- The image of a closed interval under the map of a stopping word. -/
theorem stoppingWordMap_image_Icc (w : StoppingWord iota) {a b : ℝ} (_hab : a ≤ b) :
    S.stoppingWordMap w '' Icc a b = Icc (S.stoppingWordMap w a) (S.stoppingWordMap w b) := by
  have hr : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have hfun : S.stoppingWordMap w = fun x => S.stoppingRatio w * x + S.stoppingWordMap w 0 := by
    funext x
    have := S.stoppingWordMap_sub w x 0
    linarith
  rw [hfun]
  exact Set.image_affine_Icc' hr _ a b

omit [Nonempty iota] in
/-- The image of an open interval under the map of a stopping word. -/
theorem stoppingWordMap_image_Ioo (w : StoppingWord iota) (a b : ℝ) :
    S.stoppingWordMap w '' Ioo a b = Ioo (S.stoppingWordMap w a) (S.stoppingWordMap w b) := by
  have hr : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have hfun : S.stoppingWordMap w = fun x => S.stoppingRatio w * x + S.stoppingWordMap w 0 := by
    funext x
    have := S.stoppingWordMap_sub w x 0
    linarith
  rw [hfun]
  ext y
  simp only [Set.mem_image, Set.mem_Ioo]
  constructor
  · rintro ⟨x, ⟨hax, hxb⟩, rfl⟩
    constructor <;> nlinarith
  · rintro ⟨hay, hyb⟩
    refine ⟨(y - S.stoppingWordMap w 0) / S.stoppingRatio w, ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hr]; linarith
    · rw [div_lt_iff₀ hr]; linarith
    · field_simp
      ring

omit [Nonempty iota] in
/-- The stopping interval `I_w = S_w([0,1])`. -/
theorem stoppingWordMap_image_unitInterval (w : StoppingWord iota) :
    S.stoppingWordMap w '' Icc (0:ℝ) 1 =
      Icc (S.stoppingWordMap w 0) (S.stoppingWordMap w 0 + S.stoppingRatio w) := by
  rw [S.stoppingWordMap_image_Icc w zero_le_one]
  congr 1
  have := S.stoppingWordMap_sub w 1 0
  linarith

/-! ### Words below a node -/

omit [Nonempty iota] in
/-- For a set invariant under every map of the system, the image under the map of a
leaf word lies in the image under the map of the root of its tree. -/
theorem image_stoppingLeafWord_subset {V : Set ℝ} (hV : ∀ i, MapsTo (S.map i) V V)
    (delta : ℝ) :
    ∀ {n : ℕ} {w : StoppingWord iota} (leaf : S.StoppingLeaves delta n w),
      S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' V ⊆ S.stoppingWordMap w '' V
  | _, _, .cutoff _ => subset_rfl
  | _, _, .stop _ => subset_rfl
  | _, w, .branch _ i leaf => by
      rw [stoppingLeafWord_branch]
      refine (image_stoppingLeafWord_subset hV delta leaf).trans ?_
      rw [stoppingWordMap_child, Set.image_comp]
      exact Set.image_mono (hV i).image_subset

omit [Nonempty iota] in
/-- The stopping cylinder of a leaf lies in the cylinder of the root of its tree. -/
theorem IsAttractor.image_stoppingLeafWord_subset {K : Set ℝ} (hK : S.IsAttractor K)
    (delta : ℝ) {n : ℕ} {w : StoppingWord iota} (leaf : S.StoppingLeaves delta n w) :
    S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' K ⊆ S.stoppingWordMap w '' K :=
  S.image_stoppingLeafWord_subset (fun i => hK.mapsTo_map S i) delta leaf

omit [Nonempty iota] in
/-- Distinct leaves of a stopping tree are incomparable words, so their images of a
feasible open set are disjoint: the words first differ at some letter, and the
first-level images under that letter are disjoint. -/
theorem IsFeasible.disjoint_image_stoppingLeafWord {U : Set ℝ} (hU : S.IsFeasible U)
    (delta : ℝ) :
    ∀ (n : ℕ) (w : StoppingWord iota) (leaf₁ leaf₂ : S.StoppingLeaves delta n w),
      leaf₁ ≠ leaf₂ →
      Disjoint (S.stoppingWordMap (S.stoppingLeafWord delta leaf₁) '' U)
        (S.stoppingWordMap (S.stoppingLeafWord delta leaf₂) '' U)
  | 0, w, leaf₁, leaf₂, hne => by
      cases leaf₁
      cases leaf₂
      exact absurd rfl hne
  | n + 1, w, leaf₁, leaf₂, hne => by
      cases leaf₁ with
      | stop h₁ =>
        cases leaf₂ with
        | stop h₂ => exact absurd rfl hne
        | branch h₂ _ _ => exact absurd h₁ h₂
      | branch h₁ i c₁ =>
        cases leaf₂ with
        | stop h₂ => exact absurd h₂ h₁
        | branch h₂ j c₂ =>
          by_cases hij : i = j
          · subst hij
            have hc : c₁ ≠ c₂ := fun h => hne (by rw [h])
            simp only [stoppingLeafWord_branch]
            exact hU.disjoint_image_stoppingLeafWord delta n _ c₁ c₂ hc
          · simp only [stoppingLeafWord_branch]
            refine Set.disjoint_of_subset
              (S.image_stoppingLeafWord_subset hU.mapsTo delta c₁)
              (S.image_stoppingLeafWord_subset hU.mapsTo delta c₂) ?_
            rw [stoppingWordMap_child, stoppingWordMap_child, Set.image_comp, Set.image_comp]
            exact (Set.disjoint_image_iff (S.stoppingWordMap_injective w)).mpr
              (hU.disjoint i j hij)

/-! ### The self-similar decomposition below a node -/

omit [Nonempty iota] in
/-- `eq:stopping-family`: the self-similar decomposition of the natural measure over
the leaves of a stopping tree, read on a measurable set and below any node. -/
theorem IsNatural.measure_preimage_eq_sum_leaves {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (delta : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ∀ (n : ℕ) (w : StoppingWord iota),
      ENNReal.ofReal (S.stoppingWeight s w) * μ (S.stoppingWordMap w ⁻¹' A)
        = ∑ leaf : S.StoppingLeaves delta n w,
            ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
              μ (S.stoppingWordMap (S.stoppingLeafWord delta leaf) ⁻¹' A)
  | 0, w => by
      calc ENNReal.ofReal (S.stoppingWeight s w) * μ (S.stoppingWordMap w ⁻¹' A)
          = ∑ _unit : PUnit.{u + 1},
              ENNReal.ofReal (S.stoppingWeight s w) * μ (S.stoppingWordMap w ⁻¹' A) := by
            simp
        _ = _ := by
            apply Fintype.sum_equiv (S.stoppingLeavesCutoffEquiv delta w)
            intro leaf
            rfl
  | n + 1, w => by
      classical
      by_cases h : S.stoppingRatio w ≤ delta
      · calc ENNReal.ofReal (S.stoppingWeight s w) * μ (S.stoppingWordMap w ⁻¹' A)
            = ∑ _unit : PUnit.{u + 1},
                ENNReal.ofReal (S.stoppingWeight s w) * μ (S.stoppingWordMap w ⁻¹' A) := by
              simp
          _ = _ := by
              apply Fintype.sum_equiv (S.stoppingLeavesStopEquiv delta h)
              intro leaf
              rfl
      · have hstep : ENNReal.ofReal (S.stoppingWeight s w) * μ (S.stoppingWordMap w ⁻¹' A)
            = ∑ i : iota, ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
                μ (S.stoppingWordMap (stoppingChild w i) ⁻¹' A) := by
          rw [hμ.measure_eq_sum S (S.measurable_stoppingWordMap w hA), Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [stoppingWeight_child, stoppingWordMap_child, Set.preimage_comp, tubeWeight,
            ENNReal.ofReal_mul
              (show (0:ℝ) ≤ S.stoppingWeight s w from S.generationWeight_nonneg s w.1 w.2),
            mul_assoc]
        calc ENNReal.ofReal (S.stoppingWeight s w) * μ (S.stoppingWordMap w ⁻¹' A)
            = ∑ i : iota, ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
                μ (S.stoppingWordMap (stoppingChild w i) ⁻¹' A) := hstep
          _ = ∑ i : iota, ∑ leaf : S.StoppingLeaves delta n (stoppingChild w i),
                ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
                  μ (S.stoppingWordMap (S.stoppingLeafWord delta leaf) ⁻¹' A) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              exact hμ.measure_preimage_eq_sum_leaves delta hA n (stoppingChild w i)
          _ = ∑ child : (Σ i : iota, S.StoppingLeaves delta n (stoppingChild w i)),
                ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta child.2)) *
                  μ (S.stoppingWordMap (S.stoppingLeafWord delta child.2) ⁻¹' A) := by
              rw [Fintype.sum_sigma]
          _ = _ := by
              apply Fintype.sum_equiv (S.stoppingLeavesBranchEquiv delta h)
              intro leaf
              rfl

omit [Nonempty iota] in
/-- `eq:stopping-family` on a lower integral: the self-similar decomposition of the
natural measure over the leaves of a stopping tree, below any node. -/
theorem IsNatural.lintegral_comp_eq_sum_leaves {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (delta : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∀ (n : ℕ) (w : StoppingWord iota),
      ENNReal.ofReal (S.stoppingWeight s w) * ∫⁻ x, f (S.stoppingWordMap w x) ∂μ
        = ∑ leaf : S.StoppingLeaves delta n w,
            ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
              ∫⁻ x, f (S.stoppingWordMap (S.stoppingLeafWord delta leaf) x) ∂μ
  | 0, w => by
      calc ENNReal.ofReal (S.stoppingWeight s w) * ∫⁻ x, f (S.stoppingWordMap w x) ∂μ
          = ∑ _unit : PUnit.{u + 1},
              ENNReal.ofReal (S.stoppingWeight s w) * ∫⁻ x, f (S.stoppingWordMap w x) ∂μ := by
            simp
        _ = _ := by
            apply Fintype.sum_equiv (S.stoppingLeavesCutoffEquiv delta w)
            intro leaf
            rfl
  | n + 1, w => by
      classical
      by_cases h : S.stoppingRatio w ≤ delta
      · calc ENNReal.ofReal (S.stoppingWeight s w) * ∫⁻ x, f (S.stoppingWordMap w x) ∂μ
            = ∑ _unit : PUnit.{u + 1},
                ENNReal.ofReal (S.stoppingWeight s w) *
                  ∫⁻ x, f (S.stoppingWordMap w x) ∂μ := by
              simp
          _ = _ := by
              apply Fintype.sum_equiv (S.stoppingLeavesStopEquiv delta h)
              intro leaf
              rfl
      · have hstep : ENNReal.ofReal (S.stoppingWeight s w) *
            ∫⁻ x, f (S.stoppingWordMap w x) ∂μ
            = ∑ i : iota, ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
                ∫⁻ x, f (S.stoppingWordMap (stoppingChild w i) x) ∂μ := by
          have hsum : (∫⁻ x, f (S.stoppingWordMap w x) ∂μ)
              = ∑ i, ENNReal.ofReal (S.ratio i ^ s) *
                  ∫⁻ x, f (S.stoppingWordMap w (S.map i x)) ∂μ :=
            hμ.lintegral_eq_sum S (f := fun x => f (S.stoppingWordMap w x))
              (hf.comp (S.measurable_stoppingWordMap w))
          rw [hsum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [stoppingWeight_child, tubeWeight,
            ENNReal.ofReal_mul
              (show (0:ℝ) ≤ S.stoppingWeight s w from S.generationWeight_nonneg s w.1 w.2),
            mul_assoc]
          rfl
        calc ENNReal.ofReal (S.stoppingWeight s w) * ∫⁻ x, f (S.stoppingWordMap w x) ∂μ
            = ∑ i : iota, ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
                ∫⁻ x, f (S.stoppingWordMap (stoppingChild w i) x) ∂μ := hstep
          _ = ∑ i : iota, ∑ leaf : S.StoppingLeaves delta n (stoppingChild w i),
                ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
                  ∫⁻ x, f (S.stoppingWordMap (S.stoppingLeafWord delta leaf) x) ∂μ := by
              refine Finset.sum_congr rfl fun i _ => ?_
              exact hμ.lintegral_comp_eq_sum_leaves delta hf n (stoppingChild w i)
          _ = ∑ child : (Σ i : iota, S.StoppingLeaves delta n (stoppingChild w i)),
                ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta child.2)) *
                  ∫⁻ x, f (S.stoppingWordMap (S.stoppingLeafWord delta child.2) x) ∂μ := by
              rw [Fintype.sum_sigma]
          _ = _ := by
              apply Fintype.sum_equiv (S.stoppingLeavesBranchEquiv delta h)
              intro leaf
              rfl

omit [Nonempty iota] in
/-- The decomposition below the root: `μ(A) = ∑_{w ∈ 𝒲(u)} p_w μ(S_w⁻¹ A)`. -/
theorem IsNatural.measure_eq_sum_leaves {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (delta : ℝ) {A : Set ℝ} (hA : MeasurableSet A) (n : ℕ) :
    μ A = ∑ leaf : S.StoppingLeaves delta n (stoppingRoot : StoppingWord iota),
      ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
        μ (S.stoppingWordMap (S.stoppingLeafWord delta leaf) ⁻¹' A) := by
  have := hμ.measure_preimage_eq_sum_leaves S delta hA n stoppingRoot
  simpa [stoppingWordMap_root] using this

omit [Nonempty iota] in
/-- A set disjoint from the stopping interval `S_w([0,1])` carries no mass through
`S_w`: the natural measure sits on `[0,1]`. -/
theorem IsNatural.measure_preimage_stoppingWordMap_eq_zero {K : Set ℝ} {s : ℝ}
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (w : StoppingWord iota) {A : Set ℝ}
    (hdisj : Disjoint A (S.stoppingWordMap w '' Icc (0:ℝ) 1)) :
    μ (S.stoppingWordMap w ⁻¹' A) = 0 := by
  refine measure_mono_null ?_ hμ.support_Icc
  intro x hx hx01
  exact Set.disjoint_left.mp hdisj hx ⟨x, hx01, rfl⟩

omit [Nonempty iota] in
/-- The natural measure gives the unit interval full mass. -/
theorem IsNatural.measure_Icc_eq_one {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) : μ (Icc (0:ℝ) 1) = 1 := by
  have := hμ.isProbabilityMeasure
  exact (prob_compl_eq_zero_iff measurableSet_Icc).mp hμ.support_Icc

/-! ### The counting bound -/

/-- The two-sided bound on the ratios of the leaves of a deep enough tree at
threshold `delta ≤ 1`: `r_min δ ≤ r_w ≤ δ`. -/
theorem stoppingLeafRatio_bounds {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {n : ℕ} (hn : Hutchinson.maxRatio S ^ n ≤ delta)
    (leaf : S.StoppingLeaves delta n (stoppingRoot : StoppingWord iota)) :
    S.minRatio * delta ≤ S.stoppingRatio (S.stoppingLeafWord delta leaf) ∧
      S.stoppingRatio (S.stoppingLeafWord delta leaf) ≤ delta :=
  ⟨S.stoppingRatio_lower_of_leaf S.minRatio_pos.le S.minRatio_le_one hdelta0.le hdelta1
      S.minRatio_le leaf,
    S.stoppingLeafRatio_le hn leaf⟩

open scoped Classical in
/-- **The counting bound of `thm:stopping-overlap`.**  Under the open set condition
there is an integer `M` such that, at every threshold `0 < δ ≤ 1` and every centre `x`,
at most `M` stopping intervals `I_w`, `w ∈ 𝒲(δ)`, meet the window `[x-δ, x+δ]`.  The
images `S_w(J)` of an open interval `J ⊆ U` are pairwise disjoint, have length at least
`r_min δ |J|`, and all lie in a window of length comparable to `δ`. -/
theorem IsFeasible.exists_multiplicity_bound {U : Set ℝ} (hU : S.IsFeasible U) :
    ∃ M : ℕ, 0 < M ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ n : ℕ, Hutchinson.maxRatio S ^ n ≤ delta → ∀ x : ℝ,
        (Finset.univ.filter fun leaf : S.StoppingLeaves delta n stoppingRoot =>
          (S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' Icc (0:ℝ) 1 ∩
            Icc (x - delta) (x + delta)).Nonempty).card ≤ M := by
  classical
  obtain ⟨z, hz⟩ := hU.nonempty
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU.isOpen z hz
  rw [Real.ball_eq_Ioo] at hball
  set a : ℝ := z - ε with ha
  set b : ℝ := z + ε with hb
  have hab : a < b := by rw [ha, hb]; linarith
  set A₀ : ℝ := max |a| |b| with hA₀
  have hA₀0 : 0 ≤ A₀ := le_trans (abs_nonneg a) (le_max_left _ _)
  have hrmin := S.minRatio_pos
  set X : ℝ := 2 * (2 + A₀) / (S.minRatio * (b - a)) with hX
  have hX0 : 0 < X := by
    rw [hX]
    have : 0 < b - a := by linarith
    positivity
  refine ⟨⌈X⌉₊ + 1, Nat.succ_pos _, ?_⟩
  intro delta hdelta0 hdelta1 n hn x
  set T := Finset.univ.filter fun leaf : S.StoppingLeaves delta n stoppingRoot =>
    (S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' Icc (0:ℝ) 1 ∩
      Icc (x - delta) (x + delta)).Nonempty with hT
  set f : S.StoppingLeaves delta n stoppingRoot → Set ℝ := fun leaf =>
    S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' Ioo a b with hf
  -- the images of `J` are pairwise disjoint
  have hdisj : (T : Set (S.StoppingLeaves delta n stoppingRoot)).PairwiseDisjoint f := by
    intro leaf₁ _ leaf₂ _ hne
    refine Set.disjoint_of_subset (Set.image_mono hball) (Set.image_mono hball) ?_
    exact hU.disjoint_image_stoppingLeafWord S delta n _ leaf₁ leaf₂ hne
  have hmeas : ∀ leaf, MeasurableSet (f leaf) := by
    intro leaf
    rw [hf]
    dsimp only
    rw [S.stoppingWordMap_image_Ioo]
    exact measurableSet_Ioo
  -- each image has length at least `r_min δ (b - a)`
  have hlen : ∀ leaf ∈ T, ENNReal.ofReal (S.minRatio * delta * (b - a)) ≤ volume (f leaf) := by
    intro leaf _
    rw [hf]
    dsimp only
    rw [S.stoppingWordMap_image_Ioo, Real.volume_Ioo, S.stoppingWordMap_sub]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (S.stoppingLeafRatio_bounds hdelta0 hdelta1 hn leaf).1
    have hba : 0 ≤ b - a := by linarith
    exact mul_le_mul_of_nonneg_right this hba
  -- all images lie in a window of length `2 (2 + A₀) δ`
  have hsub : (⋃ leaf ∈ T, f leaf) ⊆ Icc (x - (2 + A₀) * delta) (x + (2 + A₀) * delta) := by
    intro y hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨leaf, hleaf, hy⟩ := hy
    rw [hT, Finset.mem_filter] at hleaf
    obtain ⟨-, ⟨y₀, hy₀I, hy₀W⟩⟩ := hleaf
    set w := S.stoppingLeafWord delta leaf with hw
    set c : ℝ := S.stoppingWordMap w 0 with hc
    set r : ℝ := S.stoppingRatio w with hr
    have hr0 : 0 < r := S.generationRatio_pos w.1 w.2
    have hrδ : r ≤ delta := (S.stoppingLeafRatio_bounds hdelta0 hdelta1 hn leaf).2
    have haff : ∀ t, S.stoppingWordMap w t = c + r * t := by
      intro t
      have := S.stoppingWordMap_sub w t 0
      rw [hc, hr]
      linarith
    rw [S.stoppingWordMap_image_unitInterval] at hy₀I
    obtain ⟨hcy₀, hy₀c⟩ := hy₀I
    obtain ⟨hxy₀, hy₀x⟩ := hy₀W
    rw [hf] at hy
    obtain ⟨t, ⟨hat, htb⟩, rfl⟩ := hy
    rw [haff]
    have hta : |t| ≤ A₀ := by
      rw [hA₀]
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht]
        exact le_trans (le_trans htb.le (le_abs_self b)) (le_max_right _ _)
      · rw [abs_of_neg ht]
        have := neg_le_abs a
        exact le_trans (by linarith : -t ≤ |a|) (le_max_left _ _)
    have hrt : |r * t| ≤ delta * A₀ := by
      rw [abs_mul, abs_of_pos hr0]
      exact mul_le_mul hrδ hta (abs_nonneg t) hdelta0.le
    have hrt' := abs_le.mp hrt
    constructor <;> nlinarith
  -- compare lengths
  have hsum : volume (⋃ leaf ∈ T, f leaf) = ∑ leaf ∈ T, volume (f leaf) :=
    measure_biUnion_finset hdisj fun leaf _ => hmeas leaf
  have hcount : (T.card : ℝ≥0∞) * ENNReal.ofReal (S.minRatio * delta * (b - a))
      ≤ ENNReal.ofReal (2 * (2 + A₀) * delta) := by
    calc (T.card : ℝ≥0∞) * ENNReal.ofReal (S.minRatio * delta * (b - a))
        = ∑ _leaf ∈ T, ENNReal.ofReal (S.minRatio * delta * (b - a)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ leaf ∈ T, volume (f leaf) := Finset.sum_le_sum hlen
      _ = volume (⋃ leaf ∈ T, f leaf) := hsum.symm
      _ ≤ volume (Icc (x - (2 + A₀) * delta) (x + (2 + A₀) * delta)) := measure_mono hsub
      _ = ENNReal.ofReal (2 * (2 + A₀) * delta) := by
          rw [Real.volume_Icc]
          congr 1
          ring
  have hcountR : (T.card : ℝ) * (S.minRatio * delta * (b - a)) ≤ 2 * (2 + A₀) * delta := by
    have hpos : 0 ≤ S.minRatio * delta * (b - a) := by
      have : 0 ≤ b - a := by linarith
      positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hcount
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcount
  have hcardX : (T.card : ℝ) ≤ X := by
    rw [hX, le_div_iff₀ (mul_pos hrmin (by linarith))]
    have hδ : 0 < delta := hdelta0
    nlinarith
  have : (T.card : ℝ) ≤ (⌈X⌉₊ : ℝ) := hcardX.trans (Nat.le_ceil X)
  have hnat : T.card ≤ ⌈X⌉₊ := by exact_mod_cast this
  omega

open scoped Classical in
/-- The multiplicity bound of `thm:stopping-overlap`: every point lies in at most `M`
of the stopping intervals. -/
theorem IsFeasible.exists_point_multiplicity_bound {U : Set ℝ} (hU : S.IsFeasible U) :
    ∃ M : ℕ, 0 < M ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ n : ℕ, Hutchinson.maxRatio S ^ n ≤ delta → ∀ x : ℝ,
        (Finset.univ.filter fun leaf : S.StoppingLeaves delta n stoppingRoot =>
          x ∈ S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' Icc (0:ℝ) 1).card ≤ M := by
  classical
  obtain ⟨M, hM, hbound⟩ := hU.exists_multiplicity_bound S
  refine ⟨M, hM, fun delta hdelta0 hdelta1 n hn x => le_trans (Finset.card_le_card ?_)
    (hbound delta hdelta0 hdelta1 n hn x)⟩
  intro leaf hleaf
  rw [Finset.mem_filter] at hleaf ⊢
  refine ⟨hleaf.1, x, hleaf.2, ?_⟩
  exact ⟨by linarith, by linarith⟩

/-- **The partition of `thm:stopping-overlap`.**  Under the open set condition the
stopping intervals at every threshold `0 < δ ≤ 1` can be coloured with `M` colours so
that intervals of one colour have pairwise disjoint interiors. -/
theorem IsFeasible.exists_stopping_coloring {U : Set ℝ} (hU : S.IsFeasible U) :
    ∃ M : ℕ, 0 < M ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ n : ℕ, Hutchinson.maxRatio S ^ n ≤ delta →
        ∃ c : S.StoppingLeaves delta n stoppingRoot → Fin M,
          ∀ leaf₁ leaf₂, leaf₁ ≠ leaf₂ → c leaf₁ = c leaf₂ →
            Disjoint
              (interior (S.stoppingWordMap (S.stoppingLeafWord delta leaf₁) '' Icc (0:ℝ) 1))
              (interior (S.stoppingWordMap (S.stoppingLeafWord delta leaf₂) '' Icc (0:ℝ) 1)) := by
  classical
  obtain ⟨M, hM, hbound⟩ := hU.exists_point_multiplicity_bound S
  refine ⟨M, hM, fun delta hdelta0 hdelta1 n hn => ?_⟩
  set aL : S.StoppingLeaves delta n stoppingRoot → ℝ := fun leaf =>
    S.stoppingWordMap (S.stoppingLeafWord delta leaf) 0 with haL
  set bL : S.StoppingLeaves delta n stoppingRoot → ℝ := fun leaf =>
    S.stoppingWordMap (S.stoppingLeafWord delta leaf) 0 +
      S.stoppingRatio (S.stoppingLeafWord delta leaf) with hbL
  have hab : ∀ leaf, aL leaf ≤ bL leaf := fun leaf => by
    rw [haL, hbL]
    dsimp only
    have : 0 < S.stoppingRatio (S.stoppingLeafWord delta leaf) :=
      S.generationRatio_pos (S.stoppingLeafWord delta leaf).1 (S.stoppingLeafWord delta leaf).2
    linarith
  have hI : ∀ leaf, S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' Icc (0:ℝ) 1
      = Icc (aL leaf) (bL leaf) := fun leaf => S.stoppingWordMap_image_unitInterval _
  obtain ⟨c, hc⟩ := IntervalColoring.exists_interval_coloring aL bL hab M hM fun x => by
    have := hbound delta hdelta0 hdelta1 n hn x
    simpa only [hI] using this
  refine ⟨c, fun leaf₁ leaf₂ hne hceq => ?_⟩
  rw [hI, hI, interior_Icc, interior_Icc]
  exact hc leaf₁ leaf₂ hne hceq

/-! ### Ahlfors regularity -/

/-- The upper Ahlfors bound of `thm:stopping-overlap`, at every centre:
`μ(B̄(x,δ)) ≤ M δ^s` for `0 < δ ≤ 1`.  Only the stopping intervals meeting the ball
contribute to `eq:stopping-family`, each with weight at most `δ^s`. -/
theorem IsFeasible.measure_closedBall_le {U : Set ℝ} (hU : S.IsFeasible U) {K : Set ℝ}
    {s : ℝ} (hs : 0 ≤ s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (x delta : ℝ), 0 < delta → delta ≤ 1 →
      μ (Metric.closedBall x delta) ≤ ENNReal.ofReal (M * delta ^ s) := by
  classical
  obtain ⟨M, hM, hbound⟩ := hU.exists_multiplicity_bound S
  refine ⟨M, hM, fun x delta hdelta0 hdelta1 => ?_⟩
  obtain ⟨n, hn⟩ := S.exists_stoppingDepth hdelta0
  rw [Real.closedBall_eq_Icc]
  rw [hμ.measure_eq_sum_leaves S delta measurableSet_Icc n]
  set T := Finset.univ.filter fun leaf : S.StoppingLeaves delta n stoppingRoot =>
    (S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' Icc (0:ℝ) 1 ∩
      Icc (x - delta) (x + delta)).Nonempty with hT
  have hzero : ∀ leaf ∉ T,
      ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
        μ (S.stoppingWordMap (S.stoppingLeafWord delta leaf) ⁻¹' Icc (x - delta) (x + delta))
          = 0 := by
    intro leaf hleaf
    rw [hT, Finset.mem_filter, not_and] at hleaf
    have hdisj : Disjoint (Icc (x - delta) (x + delta))
        (S.stoppingWordMap (S.stoppingLeafWord delta leaf) '' Icc (0:ℝ) 1) := by
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
      exact Set.not_nonempty_iff_eq_empty.mp (hleaf (Finset.mem_univ _))
    rw [hμ.measure_preimage_stoppingWordMap_eq_zero S _ hdisj, mul_zero]
  have hterm : ∀ leaf ∈ T,
      ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
        μ (S.stoppingWordMap (S.stoppingLeafWord delta leaf) ⁻¹' Icc (x - delta) (x + delta))
          ≤ ENNReal.ofReal (delta ^ s) := by
    intro leaf _
    have := hμ.isProbabilityMeasure
    calc ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
          μ (S.stoppingWordMap (S.stoppingLeafWord delta leaf) ⁻¹' Icc (x - delta) (x + delta))
        ≤ ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) * 1 := by
          gcongr
          exact prob_le_one
      _ = ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) := mul_one _
      _ ≤ ENNReal.ofReal (delta ^ s) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [S.stoppingWeight_eq_ratio_rpow]
          exact Real.rpow_le_rpow (S.generationRatio_pos _ _).le
            (S.stoppingLeafRatio_bounds hdelta0 hdelta1 hn leaf).2 hs
  calc (∑ leaf : S.StoppingLeaves delta n stoppingRoot,
        ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
          μ (S.stoppingWordMap (S.stoppingLeafWord delta leaf) ⁻¹' Icc (x - delta) (x + delta)))
      = ∑ leaf ∈ T,
        ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta leaf)) *
          μ (S.stoppingWordMap (S.stoppingLeafWord delta leaf) ⁻¹' Icc (x - delta) (x + delta)) :=
        (Finset.sum_subset (Finset.subset_univ T) fun leaf _ hleaf => hzero leaf hleaf).symm
    _ ≤ ∑ _leaf ∈ T, ENNReal.ofReal (delta ^ s) := Finset.sum_le_sum hterm
    _ = (T.card : ℝ≥0∞) * ENNReal.ofReal (delta ^ s) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal (delta ^ s) := by
        gcongr
        exact_mod_cast hbound delta hdelta0 hdelta1 n hn x
    _ = ENNReal.ofReal (M * delta ^ s) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The lower Ahlfors bound of `thm:stopping-overlap`, at every point of the attractor:
`μ(B̄(x,δ)) ≥ (r_min δ / 2)^s` for `0 < δ ≤ 1`.  The stopping interval at threshold
`δ/2` containing `x` lies in the ball and carries mass at least its weight. -/
theorem IsNatural.le_measure_closedBall_of_mem {K : Set ℝ} {s : ℝ} (hs : 0 ≤ s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) {x : ℝ} (hx : x ∈ K) {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ENNReal.ofReal ((S.minRatio * delta / 2) ^ s) ≤ μ (Metric.closedBall x delta) := by
  classical
  have hhalf0 : 0 < delta / 2 := by linarith
  have hhalf1 : delta / 2 ≤ 1 := by linarith
  obtain ⟨n, hn⟩ := S.exists_stoppingDepth hhalf0
  have hxcyl : x ∈ hμ.attractor.stoppingCylinder S (stoppingRoot : StoppingWord iota).1
      (stoppingRoot : StoppingWord iota).2 := by
    change x ∈ (hμ.attractor.stoppingCylinder S 0 PUnit.unit : Set ℝ)
    rw [IsAttractor.coe_stoppingCylinder]
    exact ⟨x, hx, rfl⟩
  obtain ⟨leaf, hleaf⟩ := hμ.attractor.exists_stoppingLeaf_mem S (delta / 2) n stoppingRoot hxcyl
  change x ∈ (hμ.attractor.stoppingCylinder S _ _ : Set ℝ) at hleaf
  rw [IsAttractor.coe_stoppingCylinder] at hleaf
  set w := S.stoppingLeafWord (delta / 2) leaf with hw
  obtain ⟨t₀, ht₀K, ht₀x⟩ := hleaf
  have ht₀ : t₀ ∈ Icc (0:ℝ) 1 := hμ.attractor.2.2.1 ht₀K
  have hr : S.stoppingRatio w ≤ delta / 2 :=
    (S.stoppingLeafRatio_bounds hhalf0 hhalf1 hn leaf).2
  have hrmin : S.minRatio * (delta / 2) ≤ S.stoppingRatio w :=
    (S.stoppingLeafRatio_bounds hhalf0 hhalf1 hn leaf).1
  -- the stopping interval lies in the ball
  have hIsub : S.stoppingWordMap w '' Icc (0:ℝ) 1 ⊆ Metric.closedBall x delta := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq, ← ht₀x, S.stoppingWordMap_sub, abs_mul,
      abs_of_pos (show 0 < S.stoppingRatio w from S.generationRatio_pos w.1 w.2)]
    have htt : |t - t₀| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, ht₀.1, ht₀.2]
    calc S.stoppingRatio w * |t - t₀| ≤ (delta / 2) * 1 :=
          mul_le_mul hr htt (abs_nonneg _) hhalf0.le
      _ ≤ delta := by linarith
  -- the interval carries at least the weight of its word
  have hmass : ENNReal.ofReal (S.stoppingWeight s w) ≤ μ (S.stoppingWordMap w '' Icc (0:ℝ) 1) := by
    have hmeasI : MeasurableSet (S.stoppingWordMap w '' Icc (0:ℝ) 1) := by
      rw [S.stoppingWordMap_image_unitInterval]
      exact measurableSet_Icc
    rw [hμ.measure_eq_sum_leaves S (delta / 2) hmeasI n]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ leaf))
    rw [← hw]
    have hpre : Icc (0:ℝ) 1 ⊆ S.stoppingWordMap w ⁻¹' (S.stoppingWordMap w '' Icc (0:ℝ) 1) :=
      Set.subset_preimage_image _ _
    calc ENNReal.ofReal (S.stoppingWeight s w)
        = ENNReal.ofReal (S.stoppingWeight s w) * μ (Icc (0:ℝ) 1) := by
          rw [hμ.measure_Icc_eq_one, mul_one]
      _ ≤ ENNReal.ofReal (S.stoppingWeight s w) *
          μ (S.stoppingWordMap w ⁻¹' (S.stoppingWordMap w '' Icc (0:ℝ) 1)) := by
          gcongr
  calc ENNReal.ofReal ((S.minRatio * delta / 2) ^ s)
      ≤ ENNReal.ofReal (S.stoppingWeight s w) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [S.stoppingWeight_eq_ratio_rpow]
        refine Real.rpow_le_rpow (by positivity [S.minRatio_pos]) ?_ hs
        linarith
    _ ≤ μ (S.stoppingWordMap w '' Icc (0:ℝ) 1) := hmass
    _ ≤ μ (Metric.closedBall x delta) := measure_mono hIsub

/-- **`thm:stopping-overlap`, the Frostman conclusion.**  Under the open set condition
the natural measure is `s`-Frostman: the upper Ahlfors bound holds at every centre,
and `IsNatural` carries the support condition on `[0,1]`. -/
theorem OpenSetCondition.exists_isFrostman (hosc : S.OpenSetCondition) {K : Set ℝ} {s : ℝ}
    (hs : 0 ≤ s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) : ∃ A : ℝ, IsFrostman s A μ := by
  obtain ⟨U, hU⟩ := hosc
  obtain ⟨M, -, hbound⟩ := hU.measure_closedBall_le S hs hμ
  refine ⟨max 1 M, le_max_left _ _, hμ.support_Icc, fun x delta hdelta0 hdelta1 => ?_⟩
  refine (hbound x delta hdelta0 hdelta1).trans (ENNReal.ofReal_le_ofReal ?_)
  have hds : (0:ℝ) ≤ delta ^ s := Real.rpow_nonneg hdelta0.le s
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) hds

/-- **`thm:stopping-overlap`, Ahlfors regularity.**  Under the open set condition the
natural measure is `s`-Ahlfors regular in the closed-ball form: the two-sided bound
holds at every point of the support, which lies in the attractor. -/
theorem OpenSetCondition.exists_isAhlforsClosed (hosc : S.OpenSetCondition) {K : Set ℝ}
    {s : ℝ} (hs : 0 ≤ s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ A : ℝ, IsAhlforsClosed s A μ := by
  obtain ⟨U, hU⟩ := hosc
  obtain ⟨M, -, hbound⟩ := hU.measure_closedBall_le S hs hμ
  have hrmin := S.minRatio_pos
  set A : ℝ := max 1 (max M ((2 / S.minRatio) ^ s)) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAM : (M : ℝ) ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hAr : (2 / S.minRatio) ^ s ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨A, hA1, fun x hx delta hdelta0 hdelta1 => ⟨?_, ?_⟩⟩
  · have hxK : x ∈ K := AhlforsRegular.charged_subset hμ hx
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (hμ.le_measure_closedBall_of_mem S hs hxK hdelta0 hdelta1)
    have hpow : (S.minRatio * delta / 2) ^ s = (2 / S.minRatio) ^ (-s) * delta ^ s := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div,
        ← Real.mul_rpow (by positivity) hdelta0.le]
      congr 1
      ring
    rw [hpow]
    have hds : (0:ℝ) ≤ delta ^ s := Real.rpow_nonneg hdelta0.le s
    refine mul_le_mul_of_nonneg_right ?_ hds
    rw [Real.rpow_neg (by positivity)]
    exact inv_anti₀ (by positivity) hAr
  · refine (hbound x delta hdelta0 hdelta1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hds : (0:ℝ) ≤ delta ^ s := Real.rpow_nonneg hdelta0.le s
    exact mul_le_mul_of_nonneg_right hAM hds

end System

end

end BrownianImages
