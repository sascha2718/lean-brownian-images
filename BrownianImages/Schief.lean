/-
`sec:introduction` of `BrownianImagesComplete.tex`: Schief's theorem, that the open set
condition gives a feasible open set meeting the attractor, cited there and in the proof
of `thm:cross-piece-mass`.

The argument is Schief's, in the form Käenmäki and Vilppolainen give it.  For a word
`i` let `N(i)` be the set of words `j` of the stopping family at the scale of `i` whose
interval `I_j = S_j[0,1]` lies within `3 r_i` of `I_i`, together with `i` itself.
Under the open set condition `N(i)` has boundedly many elements, so some word `h`
maximises `#N(h)`.  Prefixing by a word `i` maps `N(h)` into `N(ih)`, and maximality
forces equality: every neighbour of `ih` starts with the first letter of `i`.  Hence a
stopping word at the scale of `ih` that starts with another letter keeps distance more
than `3 r_{ih}` from `I_{ih}`.  Applied to the codings of `S_i x` and `S_j x` for a point
`x ∈ S_h K` and incomparable `i, j`, this separates the two images by `3 r_h max(r_i,r_j)`,
and the union of the balls `S_w(B(x, r_h))` is a feasible open set containing `x`.

Words are lists, `S_{[i₁,…,iₙ]} = S_{i₁} ∘ ⋯ ∘ S_{iₙ}`, so that prefixes are outer maps.

* `listMap`, `listRatio`, `listSign`, `listLeft`, `listInterval`: the map, ratio,
  orientation, left endpoint and interval of a word.
* `Incomparable`, `exists_common_prefix_of_incomparable`: incomparable words split as a
  common prefix followed by distinct letters.
* `IsStopping`: the stopping family at a threshold, with its finiteness and the
  existence of a stopping prefix of every long word.
* `IsFeasible.disjoint_listMap_image`: incomparable words have disjoint images of a
  feasible set.
* `neighbours`, `exists_neighbours_ncard_le`, `neighbours_append_eq`: the neighbour
  sets, their bound, and the equality at a maximiser.
* `OpenSetCondition.exists_separated_point`: the point whose images are separated.
* `OpenSetCondition.strongOpenSetCondition`, `openSetCondition_iff_strongOpenSetCondition`:
  Schief's theorem.
-/
import Mathlib.Data.Set.Finite.List
import BrownianImages.OpenSet
import BrownianImages.StoppingGeometry

namespace BrownianImages

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-! ### Words as lists -/

/-- The similarity of a word, `S_{[i₁,…,iₙ]} = S_{i₁} ∘ ⋯ ∘ S_{iₙ}`. -/
def listMap : List ι → ℝ → ℝ
  | [] => id
  | i :: w => S.map i ∘ listMap w

/-- The ratio of a word, the product of the ratios of its letters. -/
def listRatio (w : List ι) : ℝ := (w.map S.ratio).prod

/-- The orientation of a word, the product of the orientations of its letters. -/
def listSign (w : List ι) : ℝ := (w.map S.sign).prod

@[simp] theorem listMap_nil : S.listMap ([] : List ι) = id := rfl

@[simp] theorem listMap_cons (i : ι) (w : List ι) :
    S.listMap (i :: w) = S.map i ∘ S.listMap w := rfl

theorem listMap_append (u v : List ι) : S.listMap (u ++ v) = S.listMap u ∘ S.listMap v := by
  induction u with
  | nil => rfl
  | cons i u ih => simp [listMap_cons, ih, Function.comp_assoc]

@[simp] theorem listRatio_nil : S.listRatio ([] : List ι) = 1 := by simp [listRatio]

@[simp] theorem listRatio_cons (i : ι) (w : List ι) :
    S.listRatio (i :: w) = S.ratio i * S.listRatio w := by simp [listRatio]

theorem listRatio_append (u v : List ι) : S.listRatio (u ++ v) = S.listRatio u * S.listRatio v := by
  simp [listRatio]

@[simp] theorem listSign_nil : S.listSign ([] : List ι) = 1 := by simp [listSign]

@[simp] theorem listSign_cons (i : ι) (w : List ι) :
    S.listSign (i :: w) = S.sign i * S.listSign w := by simp [listSign]

theorem listSign_append (u v : List ι) : S.listSign (u ++ v) = S.listSign u * S.listSign v := by
  simp [listSign]

theorem listSign_eq (w : List ι) : S.listSign w = 1 ∨ S.listSign w = -1 := by
  induction w with
  | nil => exact Or.inl (by simp)
  | cons i w ih =>
    rw [listSign_cons]
    rcases S.sign_eq i with h | h <;> rcases ih with h' | h' <;> simp [h, h']

theorem abs_listSign (w : List ι) : |S.listSign w| = 1 := by
  rcases S.listSign_eq w with h | h <;> simp [h]

theorem listRatio_pos (w : List ι) : 0 < S.listRatio w := by
  induction w with
  | nil => simp
  | cons i w ih => simp [S.ratio_pos i, ih]

theorem listRatio_le_one (w : List ι) : S.listRatio w ≤ 1 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [listRatio_cons]
    calc S.ratio i * S.listRatio w ≤ 1 * 1 :=
          mul_le_mul (S.ratio_lt_one i).le ih (S.listRatio_pos w).le zero_le_one
      _ = 1 := one_mul 1

theorem listRatio_lt_one_of_ne_nil {w : List ι} (hw : w ≠ []) : S.listRatio w < 1 := by
  obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  rw [listRatio_cons]
  calc S.ratio i * S.listRatio w ≤ S.ratio i * 1 :=
        mul_le_mul_of_nonneg_left (S.listRatio_le_one w) (S.ratio_pos i).le
    _ = S.ratio i := mul_one _
    _ < 1 := S.ratio_lt_one i

/-- A word's ratio is at most that of any prefix. -/
theorem listRatio_le_of_prefix {u w : List ι} (h : u <+: w) : S.listRatio w ≤ S.listRatio u := by
  obtain ⟨v, rfl⟩ := h
  rw [listRatio_append]
  exact mul_le_of_le_one_right (S.listRatio_pos u).le (S.listRatio_le_one v)

theorem listRatio_dropLast_mul {w : List ι} (hw : w ≠ []) :
    S.listRatio w = S.listRatio w.dropLast * S.ratio (w.getLast hw) := by
  conv_lhs => rw [← List.dropLast_append_getLast hw]
  rw [listRatio_append, listRatio_cons, listRatio_nil, mul_one]

/-- The ratio of a word is at most `r_max^{|w|}`. -/
theorem listRatio_le_maxRatio_pow [Nonempty ι] (w : List ι) :
    S.listRatio w ≤ Hutchinson.maxRatio S ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [listRatio_cons, List.length_cons, pow_succ']
    exact mul_le_mul (Hutchinson.ratio_le_maxRatio S i) ih (S.listRatio_pos w).le
      (Hutchinson.maxRatio_pos S).le

/-- The word's similarity is affine with slope its signed ratio. -/
theorem listMap_sub (w : List ι) (x y : ℝ) :
    S.listMap w x - S.listMap w y = S.listSign w * S.listRatio w * (x - y) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [listMap_cons, Function.comp_apply, listRatio_cons, listSign_cons]
    rw [S.map_sub, ih]
    ring

theorem abs_listSign_mul_listRatio (w : List ι) :
    |S.listSign w * S.listRatio w| = S.listRatio w := by
  rw [abs_mul, abs_listSign, one_mul, abs_of_pos (S.listRatio_pos w)]

theorem listSign_mul_listRatio_ne_zero (w : List ι) : S.listSign w * S.listRatio w ≠ 0 := by
  intro h
  have := S.abs_listSign_mul_listRatio w
  rw [h, abs_zero] at this
  exact (S.listRatio_pos w).ne this

/-- The word's similarity scales distances by its ratio. -/
theorem abs_listMap_sub (w : List ι) (x y : ℝ) :
    |S.listMap w x - S.listMap w y| = S.listRatio w * |x - y| := by
  rw [listMap_sub, abs_mul, abs_listSign_mul_listRatio]

theorem listMap_apply (w : List ι) (x : ℝ) :
    S.listMap w x = S.listMap w 0 + S.listSign w * S.listRatio w * x := by
  linear_combination S.listMap_sub w x 0

theorem listMap_injective (w : List ι) : Function.Injective (S.listMap w) :=
  injective_of_affine (S.listMap_sub w) (S.listSign_mul_listRatio_ne_zero w)

theorem listMap_mapsTo_unitInterval (w : List ι) :
    MapsTo (S.listMap w) (Icc (0:ℝ) 1) (Icc 0 1) := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih => exact (S.mapsTo i).comp ih

/-- The left endpoint `ℓ_w = min(S_w(0), S_w(1))` of the interval `I_w`, in closed form. -/
noncomputable def listLeft (w : List ι) : ℝ :=
  S.listMap w 0 + (S.listSign w - 1) / 2 * S.listRatio w

theorem listLeft_eq_min (w : List ι) : S.listLeft w = min (S.listMap w 0) (S.listMap w 1) :=
  (min_eq_of_affine (S.listMap_sub w) (S.listSign_eq w) (S.listRatio_pos w)).symm

/-- `S_w(x) = ℓ_w + r_w ((1 - ε_w)/2 + ε_w x)`. -/
theorem listMap_eq_listLeft_add (w : List ι) (x : ℝ) :
    S.listMap w x = S.listLeft w + S.listRatio w * ((1 - S.listSign w) / 2 + S.listSign w * x) :=
  eq_left_add_of_affine (S.listMap_sub w) x

/-- The interval `I_w = S_w[0,1] = [ℓ_w, ℓ_w + r_w]` of a word. -/
noncomputable def listInterval (w : List ι) : Set ℝ :=
  Icc (S.listLeft w) (S.listLeft w + S.listRatio w)

theorem listMap_image_unitInterval (w : List ι) :
    S.listMap w '' Icc (0:ℝ) 1 = S.listInterval w :=
  image_unitInterval_of_affine (S.listMap_sub w) (S.listSign_eq w) (S.listRatio_pos w)

theorem listInterval_append_subset (u v : List ι) :
    S.listInterval (u ++ v) ⊆ S.listInterval u := by
  rw [← listMap_image_unitInterval, ← listMap_image_unitInterval, listMap_append, Set.image_comp]
  exact Set.image_mono (S.listMap_mapsTo_unitInterval v).image_subset

theorem listInterval_subset_of_prefix {u w : List ι} (h : u <+: w) :
    S.listInterval w ⊆ S.listInterval u := by
  obtain ⟨v, rfl⟩ := h
  exact S.listInterval_append_subset u v

theorem mem_listInterval_of_mem_image {w : List ι} {K : Set ℝ} (hK : K ⊆ Icc 0 1) {y : ℝ}
    (hy : y ∈ S.listMap w '' K) : y ∈ S.listInterval w := by
  rw [← listMap_image_unitInterval]
  exact Set.image_mono hK hy

/-- Points of the intervals of two words are at least the gap apart. -/
theorem listInterval_dist {i j : List ι} {x y : ℝ} (hx : x ∈ S.listInterval i)
    (hy : y ∈ S.listInterval j) :
    max (S.listLeft j - (S.listLeft i + S.listRatio i))
      (S.listLeft i - (S.listLeft j + S.listRatio j)) ≤ |x - y| := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (by linarith)]
    exact max_le (by linarith) (by linarith)
  · rw [abs_of_nonneg (by linarith)]
    exact max_le (by linarith) (by linarith)

/-! ### Prefixes and incomparable words -/

/-- Two words are incomparable when neither is a prefix of the other. -/
def Incomparable (i j : List ι) : Prop := ¬ i <+: j ∧ ¬ j <+: i

omit [Fintype ι] in
theorem incomparable_cons_of_ne {a b : ι} (hab : a ≠ b) (w v : List ι) :
    Incomparable (a :: w) (b :: v) :=
  ⟨fun h => hab (List.cons_prefix_cons.mp h).1, fun h => hab (List.cons_prefix_cons.mp h).1.symm⟩

omit [Fintype ι] in
theorem incomparable_append_left {u i j : List ι} (h : Incomparable i j) :
    Incomparable (u ++ i) (u ++ j) :=
  ⟨fun h' => h.1 ((List.prefix_append_right_inj u).mp h'),
    fun h' => h.2 ((List.prefix_append_right_inj u).mp h')⟩

omit [Fintype ι] in
/-- Incomparable words are a common prefix followed by distinct letters. -/
theorem exists_common_prefix_of_incomparable {i j : List ι} (h : Incomparable i j) :
    ∃ (u i' j' : List ι) (a b : ι), i = u ++ a :: i' ∧ j = u ++ b :: j' ∧ a ≠ b := by
  induction i generalizing j with
  | nil => exact absurd (List.nil_prefix) h.1
  | cons a i ih =>
    cases j with
    | nil => exact absurd (List.nil_prefix) h.2
    | cons b j =>
      by_cases hab : a = b
      · subst hab
        have h' : Incomparable i j :=
          ⟨fun h' => h.1 (List.cons_prefix_cons.mpr ⟨rfl, h'⟩),
            fun h' => h.2 (List.cons_prefix_cons.mpr ⟨rfl, h'⟩)⟩
        obtain ⟨u, i', j', c, d, rfl, rfl, hcd⟩ := ih h'
        exact ⟨a :: u, i', j', c, d, rfl, rfl, hcd⟩
      · exact ⟨[], i, j, a, b, rfl, rfl, hab⟩

/-- Incomparable words have disjoint images of a feasible set. -/
theorem IsFeasible.disjoint_listMap_image {U : Set ℝ} (hU : S.IsFeasible U) {i j : List ι}
    (h : Incomparable i j) : Disjoint (S.listMap i '' U) (S.listMap j '' U) := by
  obtain ⟨u, i', j', a, b, rfl, rfl, hab⟩ := exists_common_prefix_of_incomparable h
  have hmaps : ∀ w : List ι, MapsTo (S.listMap w) U U := by
    intro w
    induction w with
    | nil => exact mapsTo_id U
    | cons k w ih => exact (hU.mapsTo k).comp ih
  rw [listMap_append, listMap_append, Set.image_comp, Set.image_comp]
  refine Set.disjoint_image_of_injective (S.listMap_injective u) ?_
  · rw [listMap_cons, listMap_cons, Set.image_comp, Set.image_comp]
    exact Set.disjoint_of_subset (Set.image_mono (hmaps i').image_subset)
      (Set.image_mono (hmaps j').image_subset) (hU.disjoint a b hab)

/-! ### The attractor along words -/

theorem IsAttractor.listMap_image_subset {K : Set ℝ} (hK : S.IsAttractor K) (w : List ι) :
    S.listMap w '' K ⊆ K := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [listMap_cons, Set.image_comp]
    exact (Set.image_mono ih).trans (hK.mapsTo_map S i).image_subset

/-- The attractor is the union of its images under all words of a given length. -/
theorem IsAttractor.eq_iUnion_listMap_image {K : Set ℝ} (hK : S.IsAttractor K) (n : ℕ) :
    K = ⋃ w ∈ {w : List ι | w.length = n}, S.listMap w '' K := by
  induction n with
  | zero =>
    ext x
    simp only [List.length_eq_zero_iff, Set.mem_ofPred_eq, Set.iUnion_iUnion_eq_left, listMap_nil,
      Set.image_id]
  | succ n ih =>
    ext x
    constructor
    · intro hx
      have hx' := hx
      rw [hK.2.2.2] at hx'
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx'
      rw [ih] at hy
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hy
      obtain ⟨w, hw, z, hz, rfl⟩ := hy
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      exact ⟨i :: w, by simp [hw], z, hz, rfl⟩
    · intro hx
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hx
      obtain ⟨w, -, hxw⟩ := hx
      exact hK.listMap_image_subset S w hxw

theorem listMap_image_ball (w : List ι) (x ε : ℝ) :
    S.listMap w '' Metric.ball x ε = Metric.ball (S.listMap w x) (S.listRatio w * ε) := by
  rw [image_ball_of_affine (S.listMap_sub w) (S.listSign_mul_listRatio_ne_zero w),
    abs_listSign_mul_listRatio]

/-! ### The stopping family -/

/-- The stopping family at threshold `δ`: the words whose ratio is at most `δ` while the
ratio of the parent is not. -/
def IsStopping (δ : ℝ) (w : List ι) : Prop :=
  S.listRatio w ≤ δ ∧ δ < S.listRatio w.dropLast

theorem IsStopping.ne_nil {δ : ℝ} {w : List ι} (h : S.IsStopping δ w) : w ≠ [] := by
  rintro rfl
  simp only [IsStopping, listRatio_nil, List.dropLast_nil] at h
  exact absurd h.2 (not_lt.mpr h.1)

theorem IsStopping.minRatio_mul_lt [Nonempty ι] {δ : ℝ} {w : List ι} (h : S.IsStopping δ w) :
    S.minRatio * δ < S.listRatio w := by
  have hne := h.ne_nil
  rw [S.listRatio_dropLast_mul hne]
  calc S.minRatio * δ < S.minRatio * S.listRatio w.dropLast :=
        mul_lt_mul_of_pos_left h.2 S.minRatio_pos
    _ = S.listRatio w.dropLast * S.minRatio := mul_comm _ _
    _ ≤ S.listRatio w.dropLast * S.ratio (w.getLast hne) :=
        mul_le_mul_of_nonneg_left (S.minRatio_le _) (S.listRatio_pos _).le

/-- Distinct stopping words at one threshold are incomparable. -/
theorem IsStopping.incomparable {δ : ℝ} {i j : List ι} (hi : S.IsStopping δ i)
    (hj : S.IsStopping δ j) (hne : i ≠ j) : Incomparable i j := by
  have key : ∀ {i j : List ι}, S.IsStopping δ i → S.IsStopping δ j → i ≠ j → ¬ i <+: j := by
    intro i j hi hj hne hij
    obtain ⟨v, rfl⟩ := hij
    have hv : v ≠ [] := by rintro rfl; exact hne (by simp)
    have hpre : i <+: (i ++ v).dropLast := by
      rw [List.dropLast_append_of_ne_nil hv]
      exact List.prefix_append i _
    have := S.listRatio_le_of_prefix hpre
    linarith [hi.1, hj.2]
  exact ⟨key hi hj hne, key hj hi hne.symm⟩

/-- The stopping family at a positive threshold is finite. -/
theorem finite_isStopping [Nonempty ι] {δ : ℝ} (hδ : 0 < δ) :
    {w : List ι | S.IsStopping δ w}.Finite := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (Hutchinson.maxRatio_lt_one S)
  refine (List.finite_length_le ι N).subset fun w hw => ?_
  simp only [Set.mem_ofPred_eq] at hw ⊢
  by_contra hlen
  have hlen : N < w.length := not_le.mp hlen
  have hle : Hutchinson.maxRatio S ^ w.dropLast.length ≤ Hutchinson.maxRatio S ^ N := by
    refine pow_le_pow_of_le_one (Hutchinson.maxRatio_pos S).le (Hutchinson.maxRatio_lt_one S).le ?_
    rw [List.length_dropLast]
    omega
  have := S.listRatio_le_maxRatio_pow w.dropLast
  linarith [hw.2]

/-- Every word with ratio at most `δ < 1` has a stopping prefix. -/
theorem exists_isStopping_prefix {δ : ℝ} (hδ1 : δ < 1) :
    ∀ (n : ℕ) (w : List ι), w.length = n → S.listRatio w ≤ δ →
      ∃ c : List ι, c <+: w ∧ S.IsStopping δ c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hr
    have hne : w ≠ [] := by
      rintro rfl
      simp only [listRatio_nil] at hr
      linarith
    by_cases hd : δ < S.listRatio w.dropLast
    · exact ⟨w, List.prefix_refl w, hr, hd⟩
    · have hd : S.listRatio w.dropLast ≤ δ := not_lt.mp hd
      have hlt : w.dropLast.length < n := by
        rw [List.length_dropLast, ← hw]
        exact Nat.sub_lt (List.length_pos_of_ne_nil hne) one_pos
      obtain ⟨c, hc, hcs⟩ := ih _ hlt w.dropLast rfl hd
      exact ⟨c, hc.trans (List.dropLast_prefix w), hcs⟩

/-- Every point of an image `S_j K` lies in the interval of a stopping word below `j`. -/
theorem IsAttractor.exists_isStopping_mem [Nonempty ι] {K : Set ℝ} (hK : S.IsAttractor K)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (j : List ι) {y : ℝ} (hy : y ∈ S.listMap j '' K) :
    ∃ c w : List ι, S.IsStopping δ c ∧ y ∈ S.listInterval c ∧ c <+: j ++ w := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ0 (Hutchinson.maxRatio_lt_one S)
  obtain ⟨z, hz, rfl⟩ := hy
  rw [hK.eq_iUnion_listMap_image S n] at hz
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hz
  obtain ⟨v, hv, z', hz', rfl⟩ := hz
  have hyv : S.listMap j (S.listMap v z') ∈ S.listMap (j ++ v) '' K := by
    rw [listMap_append]
    exact ⟨z', hz', rfl⟩
  have hrv : S.listRatio (j ++ v) ≤ δ := by
    rw [listRatio_append]
    calc S.listRatio j * S.listRatio v ≤ 1 * S.listRatio v :=
          mul_le_mul_of_nonneg_right (S.listRatio_le_one j) (S.listRatio_pos v).le
      _ = S.listRatio v := one_mul _
      _ ≤ Hutchinson.maxRatio S ^ v.length := S.listRatio_le_maxRatio_pow v
      _ = Hutchinson.maxRatio S ^ n := by rw [hv]
      _ ≤ δ := hn.le
  obtain ⟨c, hc, hcs⟩ := S.exists_isStopping_prefix hδ1 _ (j ++ v) rfl hrv
  exact ⟨c, v, hcs, S.listInterval_subset_of_prefix hc
    (S.mem_listInterval_of_mem_image hK.2.2.1 hyv), hc⟩

/-! ### The neighbour sets -/

/-- The gap between the intervals of two words, negative when they overlap. -/
noncomputable def listGap (i j : List ι) : ℝ :=
  max (S.listLeft j - (S.listLeft i + S.listRatio i))
    (S.listLeft i - (S.listLeft j + S.listRatio j))

/-- The left endpoint of `I_{ui}` is the image of `ℓ_i` under `S_u` when `S_u` preserves
orientation, and the image of `ℓ_i + r_i` when it reverses it. -/
theorem listLeft_append (u i : List ι) :
    S.listLeft (u ++ i) =
      S.listMap u (S.listLeft i) + (S.listSign u - 1) / 2 * (S.listRatio u * S.listRatio i) := by
  unfold listLeft
  rw [listMap_append, Function.comp_apply, listSign_append, listRatio_append,
    S.listMap_apply u (S.listMap i 0),
    S.listMap_apply u (S.listMap i 0 + (S.listSign i - 1) / 2 * S.listRatio i)]
  ring

theorem listGap_append (u i j : List ι) :
    S.listGap (u ++ i) (u ++ j) = S.listRatio u * S.listGap i j := by
  unfold listGap
  rw [listLeft_append, listLeft_append, listRatio_append, listRatio_append,
    S.listMap_apply u (S.listLeft i), S.listMap_apply u (S.listLeft j)]
  have hu := S.listRatio_pos u
  rcases S.listSign_eq u with h | h
  · rw [h, mul_max_of_nonneg _ _ hu.le]
    congr 1 <;> ring
  · rw [h, mul_max_of_nonneg _ _ hu.le, max_comm]
    congr 1 <;> ring

/-- The neighbours of a word `i`: the stopping words at the scale of `i` whose interval
lies within `3 r_i` of `I_i`, together with `i` itself. -/
def neighbours (i : List ι) : Set (List ι) :=
  insert i {j | Incomparable i j ∧ S.IsStopping (S.listRatio i) j ∧
    S.listGap i j ≤ 3 * S.listRatio i}

theorem self_mem_neighbours (i : List ι) : i ∈ S.neighbours i := Set.mem_insert i _

theorem neighbours_finite [Nonempty ι] (i : List ι) : (S.neighbours i).Finite :=
  ((S.finite_isStopping (S.listRatio_pos i)).subset fun _ hj => hj.2.1).insert i

/-- Prefixing by a word maps neighbours to neighbours. -/
theorem append_mem_neighbours {h j : List ι} (hj : j ∈ S.neighbours h) (i : List ι) :
    i ++ j ∈ S.neighbours (i ++ h) := by
  rcases hj with rfl | ⟨hinc, ⟨hr1, hr2⟩, hgap⟩
  · exact S.self_mem_neighbours _
  have hne : j ≠ [] := by
    rintro rfl
    simp only [listRatio_nil, List.dropLast_nil] at hr1 hr2
    exact absurd hr2 (not_lt.mpr hr1)
  refine Set.mem_insert_of_mem _ ⟨incomparable_append_left hinc, ⟨?_, ?_⟩, ?_⟩
  · rw [listRatio_append, listRatio_append]
    exact mul_le_mul_of_nonneg_left hr1 (S.listRatio_pos i).le
  · rw [List.dropLast_append_of_ne_nil hne, listRatio_append, listRatio_append]
    exact mul_lt_mul_of_pos_left hr2 (S.listRatio_pos i)
  · rw [listGap_append, listRatio_append, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hgap (S.listRatio_pos i).le

/-- A finite family of pairwise disjoint intervals of length at least `ℓ` inside a
window of length `L` has at most `L / ℓ` members. -/
theorem card_mul_le_of_pairwiseDisjoint_Ioo {α : Type*} (T : Finset α) (c r : α → ℝ)
    {ℓ lo hi : ℝ} (hlohi : lo ≤ hi) (hr : ∀ a ∈ T, ℓ ≤ r a)
    (hdisj : (T : Set α).PairwiseDisjoint fun a => Ioo (c a) (c a + r a))
    (hsub : ∀ a ∈ T, Ioo (c a) (c a + r a) ⊆ Icc lo hi) :
    (T.card : ℝ) * ℓ ≤ hi - lo := by
  have hvol : ∀ a ∈ T, ENNReal.ofReal ℓ ≤ volume (Ioo (c a) (c a + r a)) := by
    intro a ha
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal (by linarith [hr a ha])
  have hsum : volume (⋃ a ∈ T, Ioo (c a) (c a + r a))
      = ∑ a ∈ T, volume (Ioo (c a) (c a + r a)) :=
    measure_biUnion_finset hdisj fun a _ => measurableSet_Ioo
  have hcount : (T.card : ℝ≥0∞) * ENNReal.ofReal ℓ ≤ ENNReal.ofReal (hi - lo) := by
    calc (T.card : ℝ≥0∞) * ENNReal.ofReal ℓ = ∑ _a ∈ T, ENNReal.ofReal ℓ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ T, volume (Ioo (c a) (c a + r a)) := Finset.sum_le_sum hvol
      _ = volume (⋃ a ∈ T, Ioo (c a) (c a + r a)) := hsum.symm
      _ ≤ volume (Icc lo hi) := measure_mono (Set.iUnion₂_subset hsub)
      _ = ENNReal.ofReal (hi - lo) := Real.volume_Icc
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hcount
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hcount

/-- **The neighbour sets are uniformly bounded** under the open set condition: the
images of an interval `J ⊆ U` under the neighbours of `i` are disjoint intervals of
length at least `r_min r_i |J|` inside a window of length comparable to `r_i`. -/
theorem IsFeasible.exists_neighbours_ncard_le [Nonempty ι] {U : Set ℝ} (hU : S.IsFeasible U) :
    ∃ B : ℕ, ∀ i : List ι, (S.neighbours i).ncard ≤ B := by
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
  have hba : 0 < b - a := by linarith
  set X : ℝ := (10 + 2 * A₀) / (S.minRatio * (b - a)) with hX
  refine ⟨⌈X⌉₊ + 1, fun i => ?_⟩
  set ri : ℝ := S.listRatio i with hri
  have hri0 : 0 < ri := S.listRatio_pos i
  set Tset : Set (List ι) := {j | S.IsStopping ri j ∧ S.listGap i j ≤ 3 * ri} with hTset
  have hTfin : Tset.Finite := (S.finite_isStopping hri0).subset fun _ h => h.1
  set T := hTfin.toFinset with hT
  have hsub : S.neighbours i ⊆ insert i Tset := by
    intro j hj
    rcases hj with rfl | ⟨-, h1, h2⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨h1, h2⟩
  have hncard : (S.neighbours i).ncard ≤ Tset.ncard + 1 :=
    (Set.ncard_le_ncard hsub (hTfin.insert i)).trans (Set.ncard_insert_le i Tset)
  -- the images of `(a, b) = B(z, ε)` are balls
  have hIoo : Ioo a b = Metric.ball z ε := by rw [Real.ball_eq_Ioo]
  have himg : ∀ j : List ι, Ioo (S.listMap j z - S.listRatio j * ε)
      (S.listMap j z - S.listRatio j * ε + S.listRatio j * (b - a)) = S.listMap j '' Ioo a b := by
    intro j
    rw [hIoo, listMap_image_ball, Real.ball_eq_Ioo]
    congr 1
    rw [ha, hb]
    ring
  have hpack := card_mul_le_of_pairwiseDisjoint_Ioo T (fun j => S.listMap j z - S.listRatio j * ε)
    (fun j => S.listRatio j * (b - a)) (ℓ := S.minRatio * ri * (b - a))
    (lo := S.listLeft i - (5 + A₀) * ri) (hi := S.listLeft i + (5 + A₀) * ri)
    (by nlinarith) ?_ ?_ ?_
  · have hcardX : (T.card : ℝ) ≤ X := by
      rw [hX, le_div_iff₀ (mul_pos hrmin hba)]
      have : (T.card : ℝ) * (S.minRatio * ri * (b - a)) ≤ (10 + 2 * A₀) * ri := by
        linarith
      nlinarith
    have hnat : T.card ≤ ⌈X⌉₊ := by exact_mod_cast hcardX.trans (Nat.le_ceil X)
    rw [Set.ncard_eq_toFinset_card Tset hTfin, ← hT] at hncard
    omega
  · intro j hj
    rw [hT, Set.Finite.mem_toFinset] at hj
    exact mul_le_mul_of_nonneg_right hj.1.minRatio_mul_lt.le hba.le
  · intro j hj j' hj' hne
    rw [hT, Finset.mem_coe, Set.Finite.mem_toFinset] at hj hj'
    simp only [Function.onFun]
    rw [himg, himg]
    refine Set.disjoint_of_subset (Set.image_mono hball) (Set.image_mono hball) ?_
    exact hU.disjoint_listMap_image S (hj.1.incomparable S hj'.1 hne)
  · intro j hj y hy
    rw [hT, Set.Finite.mem_toFinset] at hj
    obtain ⟨⟨hr1, -⟩, hgap⟩ := hj
    rw [himg] at hy
    obtain ⟨t, ⟨hat, htb⟩, rfl⟩ := hy
    have hgap' := max_le_iff.mp hgap
    have hrj := S.listRatio_pos j
    have hta : |t| ≤ A₀ := by
      rw [hA₀]
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht]
        exact le_trans (le_trans htb.le (le_abs_self b)) (le_max_right _ _)
      · rw [abs_of_neg ht]
        have := neg_le_abs a
        exact le_trans (by linarith : -t ≤ |a|) (le_max_left _ _)
    have hcoef : |(1 - S.listSign j) / 2 + S.listSign j * t| ≤ 1 + A₀ := by
      have h1 : |(1 - S.listSign j) / 2| ≤ 1 := by
        rcases S.listSign_eq j with h | h <;> rw [h] <;> norm_num
      calc |(1 - S.listSign j) / 2 + S.listSign j * t|
          ≤ |(1 - S.listSign j) / 2| + |S.listSign j * t| := abs_add_le _ _
        _ ≤ 1 + A₀ := by
          rw [abs_mul, S.abs_listSign, one_mul]
          linarith
    have hrt : |S.listRatio j * ((1 - S.listSign j) / 2 + S.listSign j * t)| ≤ ri * (1 + A₀) := by
      rw [abs_mul, abs_of_pos hrj]
      exact mul_le_mul hr1 hcoef (abs_nonneg _) hri0.le
    have hrt' := abs_le.mp hrt
    rw [S.listMap_eq_listLeft_add]
    constructor <;> nlinarith

/-- Some word has the most neighbours. -/
theorem IsFeasible.exists_neighbours_max [Nonempty ι] {U : Set ℝ} (hU : S.IsFeasible U) :
    ∃ h : List ι, ∀ i : List ι, (S.neighbours i).ncard ≤ (S.neighbours h).ncard := by
  classical
  obtain ⟨B, hB⟩ := hU.exists_neighbours_ncard_le S
  have hP : ∃ m : ℕ, ∀ i : List ι, (S.neighbours i).ncard ≤ m := ⟨B, hB⟩
  have hmspec : ∀ i, (S.neighbours i).ncard ≤ Nat.find hP := Nat.find_spec hP
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hP = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    have := hmspec []
    rw [h0] at this
    have hpos := (Set.ncard_pos (S.neighbours_finite [])).mpr ⟨[], S.self_mem_neighbours []⟩
    omega
  have hnot : ¬ ∀ i, (S.neighbours i).ncard ≤ k := Nat.find_min hP (by omega)
  obtain ⟨h, hh⟩ := not_forall.mp hnot
  have hh' := not_le.mp hh
  exact ⟨h, fun i => (hmspec i).trans (by omega)⟩

/-- **The neighbours of `ih` at a maximiser `h`** are exactly the words `ij` with
`j ∈ N(h)`: prefixing injects `N(h)` into `N(ih)`, and `#N(ih) ≤ #N(h)`. -/
theorem neighbours_append_eq [Nonempty ι] {h : List ι}
    (hmax : ∀ i : List ι, (S.neighbours i).ncard ≤ (S.neighbours h).ncard) (i : List ι) :
    S.neighbours (i ++ h) = (fun j => i ++ j) '' S.neighbours h := by
  have hsub : (fun j => i ++ j) '' S.neighbours h ⊆ S.neighbours (i ++ h) := by
    rintro _ ⟨j, hj, rfl⟩
    exact S.append_mem_neighbours hj i
  have hinj : Function.Injective (fun j : List ι => i ++ j) :=
    fun _ _ h => List.append_cancel_left h
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (S.neighbours_finite _)).symm
  rw [Set.ncard_image_of_injective _ hinj]
  exact hmax (i ++ h)

/-- **A stopping word starting with another letter is far from `I_{ih}`.**  At a
maximiser `h`, every neighbour of `ih` starts with the first letter of `i`, so a stopping
word at the scale of `ih` with another first letter keeps distance more than
`3 r_{ih}` from `I_{ih}`. -/
theorem three_mul_lt_listGap_of_head_ne [Nonempty ι] {h : List ι}
    (hmax : ∀ i : List ι, (S.neighbours i).ncard ≤ (S.neighbours h).ncard) {i : List ι}
    (hi : i ≠ []) {c : List ι} (hc : S.IsStopping (S.listRatio (i ++ h)) c)
    (hhead : c.head? ≠ i.head?) :
    3 * S.listRatio (i ++ h) < S.listGap (i ++ h) c := by
  by_contra hle
  have hle' := not_lt.mp hle
  obtain ⟨a, i', rfl⟩ := List.exists_cons_of_ne_nil hi
  obtain ⟨b, c', rfl⟩ := List.exists_cons_of_ne_nil hc.ne_nil
  simp only [List.head?_cons, ne_eq, Option.some.injEq] at hhead
  have hinc : Incomparable (a :: i' ++ h) (b :: c') :=
    incomparable_cons_of_ne (fun hab => hhead hab.symm) _ _
  have hmem : b :: c' ∈ S.neighbours (a :: i' ++ h) :=
    Set.mem_insert_of_mem _ ⟨hinc, hc, hle'⟩
  rw [S.neighbours_append_eq hmax] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  simp only [List.cons_append, List.cons.injEq] at hj
  exact hhead hj.1.symm

/-- **Schief's separated point.**  Under the open set condition there are `x ∈ K` and
`ε > 0` such that the images of `x` under incomparable words `i, j` are at least
`ε (r_i + r_j)` apart: any point of `S_h K`, for a maximiser `h`, with `ε = r_h`. -/
theorem IsFeasible.exists_separated_point [Nonempty ι] {U : Set ℝ} (hU : S.IsFeasible U)
    {K : Set ℝ} (hK : S.IsAttractor K) :
    ∃ x ∈ K, ∃ ε : ℝ, 0 < ε ∧ ∀ i j : List ι, Incomparable i j →
      ε * (S.listRatio i + S.listRatio j) ≤ |S.listMap i x - S.listMap j x| := by
  obtain ⟨h, hmax⟩ := hU.exists_neighbours_max S
  obtain ⟨z, hz⟩ := hK.2.1
  refine ⟨S.listMap h z, hK.listMap_image_subset S h ⟨z, hz, rfl⟩, S.listRatio h,
    S.listRatio_pos h, ?_⟩
  -- distinct first letters
  have key : ∀ (a b : ι) (i j : List ι), a ≠ b →
      3 * (S.listRatio (a :: i) * S.listRatio h)
        < |S.listMap (a :: i) (S.listMap h z) - S.listMap (b :: j) (S.listMap h z)| := by
    intro a b i j hab
    have hy : S.listMap (b :: j) (S.listMap h z) ∈ S.listMap (b :: j ++ h) '' K := by
      rw [listMap_append]
      exact ⟨z, hz, rfl⟩
    have hδ0 : 0 < S.listRatio (a :: i ++ h) := S.listRatio_pos _
    have hδ1 : S.listRatio (a :: i ++ h) < 1 := S.listRatio_lt_one_of_ne_nil (by simp)
    obtain ⟨c, w, hc, hyc, hcpre⟩ := hK.exists_isStopping_mem S hδ0 hδ1 (b :: j ++ h) hy
    have hhead : c.head? ≠ (a :: i).head? := by
      obtain ⟨b', c', rfl⟩ := List.exists_cons_of_ne_nil hc.ne_nil
      simp only [List.cons_append, List.cons_prefix_cons] at hcpre
      simp only [List.head?_cons, ne_eq, Option.some.injEq]
      rw [hcpre.1]
      exact fun hba => hab hba.symm
    have hgap := S.three_mul_lt_listGap_of_head_ne hmax (by simp : a :: i ≠ []) hc hhead
    have hx : S.listMap (a :: i) (S.listMap h z) ∈ S.listInterval (a :: i ++ h) := by
      have hx' : S.listMap (a :: i) (S.listMap h z) ∈ S.listMap (a :: i ++ h) '' K := by
        rw [listMap_append]
        exact ⟨z, hz, rfl⟩
      exact S.mem_listInterval_of_mem_image hK.2.2.1 hx'
    have hdist := S.listInterval_dist hx hyc
    rw [listRatio_append] at hgap
    unfold listGap at hgap
    linarith
  intro i j hinc
  obtain ⟨u, i', j', a, b, rfl, rfl, hab⟩ := exists_common_prefix_of_incomparable hinc
  have h1 := key a b i' j' hab
  have h2 := key b a j' i' hab.symm
  rw [abs_sub_comm] at h2
  rw [listMap_append, listMap_append, Function.comp_apply, Function.comp_apply, abs_listMap_sub,
    listRatio_append, listRatio_append]
  have hu := S.listRatio_pos u
  have hD := abs_nonneg (S.listMap (a :: i') (S.listMap h z) - S.listMap (b :: j') (S.listMap h z))
  have h3 : S.listRatio h * (S.listRatio (a :: i') + S.listRatio (b :: j'))
      ≤ |S.listMap (a :: i') (S.listMap h z) - S.listMap (b :: j') (S.listMap h z)| := by
    nlinarith
  calc S.listRatio h * (S.listRatio u * S.listRatio (a :: i') + S.listRatio u * S.listRatio (b :: j'))
      = S.listRatio u * (S.listRatio h * (S.listRatio (a :: i') + S.listRatio (b :: j'))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 hu.le

/-- **Schief's theorem.**  The open set condition gives a feasible open set meeting the
attractor: the union of the balls `S_w(B(x, ε))` around the images of the separated
point `x`. -/
theorem OpenSetCondition.strongOpenSetCondition [Nonempty ι] (hosc : S.OpenSetCondition)
    {K : Set ℝ} (hK : S.IsAttractor K) : S.StrongOpenSetCondition K := by
  obtain ⟨U, hU⟩ := hosc
  obtain ⟨x, hxK, ε, hε, hsep⟩ := hU.exists_separated_point S hK
  refine ⟨⋃ w : List ι, S.listMap w '' Metric.ball x ε, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨x, Set.mem_iUnion.mpr ⟨[], ⟨x, Metric.mem_ball_self hε, rfl⟩⟩, hxK⟩⟩
  · exact isOpen_iUnion fun w => by
      rw [listMap_image_ball]
      exact Metric.isOpen_ball
  · exact ⟨x, Set.mem_iUnion.mpr ⟨[], ⟨x, Metric.mem_ball_self hε, rfl⟩⟩⟩
  · refine (Metric.isBounded_Ioo (-ε) (1 + ε)).subset (Set.iUnion_subset fun w => ?_)
    rw [listMap_image_ball, Real.ball_eq_Ioo]
    have hx01 : S.listMap w x ∈ Icc (0:ℝ) 1 := S.listMap_mapsTo_unitInterval w (hK.2.2.1 hxK)
    have hr1 : S.listRatio w * ε ≤ ε := mul_le_of_le_one_left hε.le (S.listRatio_le_one w)
    exact Set.Ioo_subset_Ioo (by linarith [hx01.1]) (by linarith [hx01.2])
  · intro k y hy
    rw [Set.mem_iUnion] at hy ⊢
    obtain ⟨w, hw⟩ := hy
    refine ⟨k :: w, ?_⟩
    rw [listMap_cons, Set.image_comp]
    exact ⟨y, hw, rfl⟩
  · intro k l hkl
    rw [Set.image_iUnion, Set.image_iUnion]
    refine Set.disjoint_iUnion_left.mpr fun w => Set.disjoint_iUnion_right.mpr fun v => ?_
    rw [← Set.image_comp, ← Set.image_comp, ← listMap_cons, ← listMap_cons, listMap_image_ball,
      listMap_image_ball]
    refine Metric.ball_disjoint_ball ?_
    rw [Real.dist_eq]
    have := hsep (k :: w) (l :: v) (incomparable_cons_of_ne hkl w v)
    calc S.listRatio (k :: w) * ε + S.listRatio (l :: v) * ε
        = ε * (S.listRatio (k :: w) + S.listRatio (l :: v)) := by ring
      _ ≤ _ := this

/-- **Schief's theorem** as an equivalence: for a system with an attractor `K`, the open
set condition and the strong open set condition on `K` are the same. -/
theorem openSetCondition_iff_strongOpenSetCondition [Nonempty ι] {K : Set ℝ}
    (hK : S.IsAttractor K) : S.OpenSetCondition ↔ S.StrongOpenSetCondition K :=
  ⟨fun h => h.strongOpenSetCondition S hK, fun h => h.openSetCondition S⟩

end System

end BrownianImages
