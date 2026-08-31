/-
The finite stopping tree used in the upper tube-moment estimate.

The fixed-generation words in `MinkowskiGeneration` compose new letters on
the outside, which is convenient for Hutchinson iteration but not for a
nested stopping tree.  Here the same recursive word type is equipped with the
opposite (prefix) composition: a child of `w` is `S_w \circ S_i`.  Its ratio
and natural weight are still `generationRatio` and `generationWeight`.

The type `StoppingLeaves S delta n w` recursively stops as soon as the ratio
of `w` is at most `delta`, and otherwise branches over every letter, with a
hard depth cutoff `n`.  It is a finite nonempty type rather than a finset.
This makes the mass identity exact without any bookkeeping about duplicate
finset unions.  Once `maxRatio S ^ n <= delta`, the cutoff is never premature.
-/
import BrownianImages.MinkowskiGeneration

namespace BrownianImages

open Set TopologicalSpace
open scoped NNReal Topology

noncomputable section

universe u

namespace System

variable {iota : Type u} [Fintype iota] [Nonempty iota] (S : System iota)

/-! ### Nested finite words -/

/-- The prefix-ordered similarity represented by a generation word.  A new
letter is composed on the inside, so its cylinder is a child of the old one. -/
def stoppingMap (S : System iota) :
    (k : ℕ) -> GenerationWord iota k -> ℝ -> ℝ
  | 0, _ => id
  | Nat.succ k, w => S.stoppingMap k w.1 ∘ S.map w.2

omit [Nonempty iota] in
@[simp]
theorem stoppingMap_zero (w : GenerationWord iota 0) :
    S.stoppingMap 0 w = id := rfl

omit [Nonempty iota] in
@[simp]
theorem stoppingMap_succ (k : ℕ) (w : GenerationWord iota (k + 1)) :
    S.stoppingMap (k + 1) w = S.stoppingMap k w.1 ∘ S.map w.2 := rfl

omit [Nonempty iota] in
theorem continuous_stoppingMap :
    ∀ (k : ℕ) (w : GenerationWord iota k), Continuous (S.stoppingMap k w)
  | 0, _ => continuous_id
  | Nat.succ k, w =>
      (continuous_stoppingMap k w.1).comp (S.continuous_map w.2)

omit [Nonempty iota] in
/-- Every prefix map preserves the ambient unit interval. -/
theorem mapsTo_stoppingMap_unitInterval :
    ∀ (k : ℕ) (w : GenerationWord iota k),
      MapsTo (S.stoppingMap k w) (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1)
  | 0, _ => by simpa [stoppingMap] using Set.mapsTo_id (Set.Icc (0 : ℝ) 1)
  | Nat.succ k, w =>
      (mapsTo_stoppingMap_unitInterval k w.1).comp (S.mapsTo w.2)

omit [Nonempty iota] in
/-- The prefix map has the product contraction ratio recorded by
`generationRatio`. -/
theorem stoppingMap_sub :
    ∀ (k : ℕ) (w : GenerationWord iota k) (x y : ℝ),
      S.stoppingMap k w x - S.stoppingMap k w y =
        S.generationRatio k w * (x - y)
  | 0, _, x, y => by simp [stoppingMap, generationRatio]
  | Nat.succ k, ⟨w, i⟩, x, y => by
      change
        S.stoppingMap k w (S.map i x) - S.stoppingMap k w (S.map i y) =
          (S.generationRatio k w * S.ratio i) * (x - y)
      rw [stoppingMap_sub k w]
      simp only [System.map]
      ring

omit [Nonempty iota] in
/-- Affine normal form of a prefix map. -/
theorem stoppingMap_eq_zero_add_ratio_mul
    (k : ℕ) (w : GenerationWord iota k) (x : ℝ) :
    S.stoppingMap k w x = S.stoppingMap k w 0 +
      S.generationRatio k w * x := by
  have h := S.stoppingMap_sub k w x 0
  simpa [add_comm] using (sub_eq_iff_eq_add.mp h)

omit [Nonempty iota] in
/-- Prefix cylinders remain inside the invariant attractor. -/
theorem IsAttractor.mapsTo_stoppingMap {K : Set ℝ} (hK : S.IsAttractor K) :
    ∀ (k : ℕ) (w : GenerationWord iota k), MapsTo (S.stoppingMap k w) K K
  | 0, _ => by simpa [stoppingMap] using Set.mapsTo_id K
  | Nat.succ k, ⟨w, i⟩ =>
      (mapsTo_stoppingMap hK k w).comp (hK.mapsTo_map S i)

/-- The nested compact cylinder associated to a stopping word. -/
def IsAttractor.stoppingCylinder {K : Set ℝ} (hK : S.IsAttractor K)
    (k : ℕ) (w : GenerationWord iota k) : NonemptyCompacts ℝ :=
  hK.toNonemptyCompacts.map (S.stoppingMap k w)
    (S.continuous_stoppingMap k w)

omit [Nonempty iota] in
@[simp]
theorem IsAttractor.coe_stoppingCylinder {K : Set ℝ}
    (hK : S.IsAttractor K) (k : ℕ) (w : GenerationWord iota k) :
    (hK.stoppingCylinder S k w : Set ℝ) = S.stoppingMap k w '' K := by
  rw [IsAttractor.stoppingCylinder, NonemptyCompacts.coe_map,
    IsAttractor.coe_toNonemptyCompacts]

omit [Nonempty iota] in
/-- A cylinder is the union of its one-letter children, in elementwise form. -/
theorem IsAttractor.exists_mem_stoppingCylinder_child {K : Set ℝ}
    (hK : S.IsAttractor K) {k : ℕ} {w : GenerationWord iota k}
    {x : ℝ} (hx : x ∈ hK.stoppingCylinder S k w) :
    ∃ i : iota, x ∈ hK.stoppingCylinder S (k + 1) (w, i) := by
  change x ∈ (hK.stoppingCylinder S k w : Set ℝ) at hx
  rw [hK.coe_stoppingCylinder S k w] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ ⋃ i, S.map i '' K := hK.2.2.2 ▸ hy
  obtain ⟨i, z, hz, hiz⟩ := Set.mem_iUnion.1 hy'
  refine ⟨i, ?_⟩
  change S.stoppingMap k w y ∈
    (hK.stoppingCylinder S (k + 1) (w, i) : Set ℝ)
  rw [hK.coe_stoppingCylinder S (k + 1) (w, i)]
  refine ⟨z, hz, ?_⟩
  change S.stoppingMap k w (S.map i z) = S.stoppingMap k w y
  rw [hiz]

/-! ### A finite stopping tree -/

/-- A word of arbitrary finite length. -/
abbrev StoppingWord (iota : Type u) := Σ k : ℕ, GenerationWord iota k

/-- The root of the stopping tree. -/
def stoppingRoot : StoppingWord iota := ⟨0, PUnit.unit⟩

/-- Add one child letter to a word. -/
def stoppingChild (w : StoppingWord iota) (i : iota) : StoppingWord iota :=
  ⟨w.1 + 1, (w.2, i)⟩

/-- Product ratio of an arbitrary finite word. -/
def stoppingRatio (w : StoppingWord iota) : ℝ :=
  S.generationRatio w.1 w.2

/-- Product natural weight of an arbitrary finite word. -/
def stoppingWeight (s : ℝ) (w : StoppingWord iota) : ℝ :=
  S.generationWeight s w.1 w.2

/-- Left endpoint of a stopping cylinder, bundled as a nonnegative time. -/
def stoppingAnchor (w : StoppingWord iota) : NNReal :=
  ⟨S.stoppingMap w.1 w.2 0,
    (S.mapsTo_stoppingMap_unitInterval w.1 w.2
      (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)).1⟩

/-- Length of the host interval of a stopping cylinder. -/
def stoppingLength (w : StoppingWord iota) : NNReal :=
  ⟨S.stoppingRatio w, (S.generationRatio_pos w.1 w.2).le⟩

omit [Nonempty iota] in
@[simp]
theorem coe_stoppingAnchor (w : StoppingWord iota) :
    (S.stoppingAnchor w : ℝ) = S.stoppingMap w.1 w.2 0 := rfl

omit [Nonempty iota] in
@[simp]
theorem coe_stoppingLength (w : StoppingWord iota) :
    (S.stoppingLength w : ℝ) = S.stoppingRatio w := rfl

omit [Nonempty iota] in
theorem stoppingLength_ne_zero (w : StoppingWord iota) :
    S.stoppingLength w ≠ 0 := by
  exact ne_of_gt (S.generationRatio_pos w.1 w.2)

omit [Nonempty iota] in
@[simp]
theorem stoppingRatio_root : S.stoppingRatio (stoppingRoot : StoppingWord iota) = 1 :=
  rfl

omit [Nonempty iota] in
@[simp]
theorem stoppingWeight_root (s : ℝ) :
    S.stoppingWeight s (stoppingRoot : StoppingWord iota) = 1 := rfl

omit [Nonempty iota] in
@[simp]
theorem stoppingRatio_child (w : StoppingWord iota) (i : iota) :
    S.stoppingRatio (stoppingChild w i) =
      S.stoppingRatio w * S.ratio i := rfl

omit [Nonempty iota] in
@[simp]
theorem stoppingWeight_child (s : ℝ) (w : StoppingWord iota) (i : iota) :
    S.stoppingWeight s (stoppingChild w i) =
      S.stoppingWeight s w * S.tubeWeight s i := rfl

/-- The leaves obtained by stopping at ratio `delta`, with at most `n`
further branching steps.  Constructors record why recursion stopped or
branched, so eliminating a leaf never requires transport between `if`-types. -/
inductive StoppingLeaves (S : System iota) (delta : ℝ) :
    (n : ℕ) -> StoppingWord iota -> Type u
  | cutoff (w : StoppingWord iota) : StoppingLeaves S delta 0 w
  | stop {n : ℕ} {w : StoppingWord iota}
      (h : S.stoppingRatio w ≤ delta) : StoppingLeaves S delta (n + 1) w
  | branch {n : ℕ} {w : StoppingWord iota}
      (h : ¬S.stoppingRatio w ≤ delta) (i : iota)
      (leaf : StoppingLeaves S delta n (stoppingChild w i)) :
      StoppingLeaves S delta (n + 1) w

/-- At depth zero there is exactly the cutoff leaf. -/
def stoppingLeavesCutoffEquiv (delta : ℝ) (w : StoppingWord iota) :
    PUnit.{u + 1} ≃ S.StoppingLeaves delta 0 w where
  toFun _ := .cutoff w
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv leaf := by cases leaf; rfl

/-- Once the current word crosses the threshold, its leaf type is a
singleton. -/
def stoppingLeavesStopEquiv (delta : ℝ) {n : ℕ} {w : StoppingWord iota}
    (h : S.stoppingRatio w ≤ delta) :
    PUnit.{u + 1} ≃ S.StoppingLeaves delta (n + 1) w where
  toFun _ := .stop h
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv leaf := by
    cases leaf with
    | stop h' => congr 1
    | branch h' i child => exact (h' h).elim

/-- Before crossing the threshold, the leaves are the disjoint union of the
leaves below the children. -/
def stoppingLeavesBranchEquiv (delta : ℝ) {n : ℕ} {w : StoppingWord iota}
    (h : ¬S.stoppingRatio w ≤ delta) :
    (Σ i : iota, S.StoppingLeaves delta n (stoppingChild w i)) ≃
      S.StoppingLeaves delta (n + 1) w where
  toFun leaf := .branch h leaf.1 leaf.2
  invFun leaf := by
    cases leaf with
    | stop h' => exact (h h').elim
    | branch _ i child => exact ⟨i, child⟩
  left_inv leaf := by cases leaf; rfl
  right_inv leaf := by
    cases leaf with
    | stop h' => exact (h h').elim
    | branch h' i child => congr 1

noncomputable instance stoppingLeavesFintype (S : System iota) (delta : ℝ) :
    ∀ (n : ℕ) (w : StoppingWord iota), Fintype (S.StoppingLeaves delta n w)
  | 0, w => Fintype.ofEquiv PUnit.{u + 1}
      (S.stoppingLeavesCutoffEquiv delta w)
  | Nat.succ n, w => by
      by_cases h : S.stoppingRatio w ≤ delta
      · exact Fintype.ofEquiv PUnit.{u + 1}
          (S.stoppingLeavesStopEquiv delta h)
      · letI (i : iota) : Fintype
            (S.StoppingLeaves delta n (stoppingChild w i)) :=
          stoppingLeavesFintype S delta n (stoppingChild w i)
        exact Fintype.ofEquiv
          (Σ i : iota, S.StoppingLeaves delta n (stoppingChild w i))
          (S.stoppingLeavesBranchEquiv delta h)

noncomputable instance stoppingLeavesNonempty (S : System iota) (delta : ℝ) :
    ∀ (n : ℕ) (w : StoppingWord iota), Nonempty (S.StoppingLeaves delta n w)
  | 0, w => ⟨.cutoff w⟩
  | Nat.succ n, w => by
      by_cases h : S.stoppingRatio w ≤ delta
      · exact ⟨.stop h⟩
      · let i : iota := Classical.arbitrary iota
        exact ⟨.branch h i (Classical.choice
          (stoppingLeavesNonempty S delta n (stoppingChild w i)))⟩

/-- The actual word represented by a stopping leaf. -/
def stoppingLeafWord (S : System iota) (delta : ℝ) :
    {n : ℕ} -> {w : StoppingWord iota} ->
      S.StoppingLeaves delta n w -> StoppingWord iota
  | _, _, .cutoff w => w
  | _, w, .stop _ => w
  | _, _, .branch _ _ leaf => S.stoppingLeafWord delta leaf

omit [Nonempty iota] in
@[simp]
theorem stoppingLeafWord_cutoff (delta : ℝ) (w : StoppingWord iota) :
    S.stoppingLeafWord delta (StoppingLeaves.cutoff w) = w := rfl

omit [Nonempty iota] in
@[simp]
theorem stoppingLeafWord_stop (delta : ℝ) {n : ℕ} {w : StoppingWord iota}
    (h : S.stoppingRatio w ≤ delta) :
    S.stoppingLeafWord delta (StoppingLeaves.stop (n := n) h) = w := rfl

omit [Nonempty iota] in
@[simp]
theorem stoppingLeafWord_branch (delta : ℝ) {n : ℕ}
    {w : StoppingWord iota} (h : ¬S.stoppingRatio w ≤ delta) (i : iota)
    (leaf : S.StoppingLeaves delta n (stoppingChild w i)) :
    S.stoppingLeafWord delta (StoppingLeaves.branch h i leaf) =
      S.stoppingLeafWord delta leaf := rfl

/-! ### Exact mass, cover, and scale properties -/

omit [Nonempty iota] in
/-- The natural weights of all leaves of a (possibly depth-truncated)
stopping tree add up to the weight of its root. -/
theorem sum_stoppingLeafWeight {s : ℝ} (hdim : S.IsDimension s) (delta : ℝ) :
    ∀ (n : ℕ) (w : StoppingWord iota),
      (∑ leaf : S.StoppingLeaves delta n w,
          S.stoppingWeight s (S.stoppingLeafWord delta leaf)) =
        S.stoppingWeight s w
  | 0, w => by
      calc
        (∑ leaf : S.StoppingLeaves delta 0 w,
            S.stoppingWeight s (S.stoppingLeafWord delta leaf)) =
            ∑ _unit : PUnit.{u + 1}, S.stoppingWeight s w := by
          apply Fintype.sum_equiv (S.stoppingLeavesCutoffEquiv delta w).symm
          intro leaf
          cases leaf
          rfl
        _ = S.stoppingWeight s w := by simp
  | Nat.succ n, w => by
      classical
      by_cases h : S.stoppingRatio w ≤ delta
      · calc
          (∑ leaf : S.StoppingLeaves delta (n + 1) w,
              S.stoppingWeight s (S.stoppingLeafWord delta leaf)) =
              ∑ _unit : PUnit.{u + 1}, S.stoppingWeight s w := by
            apply Fintype.sum_equiv (S.stoppingLeavesStopEquiv delta h).symm
            intro leaf
            cases leaf with
            | stop _ => rfl
            | branch h' i child => exact (h' h).elim
          _ = S.stoppingWeight s w := by simp
      · calc
          (∑ leaf : S.StoppingLeaves delta (n + 1) w,
              S.stoppingWeight s (S.stoppingLeafWord delta leaf)) =
              ∑ child : (Σ i : iota,
                S.StoppingLeaves delta n (stoppingChild w i)),
                S.stoppingWeight s (S.stoppingLeafWord delta child.2) := by
            apply Fintype.sum_equiv
              (S.stoppingLeavesBranchEquiv delta h).symm
            intro leaf
            cases leaf with
            | stop h' => exact (h h').elim
            | branch _ i child => rfl
          _ = ∑ i : iota, ∑ leaf : S.StoppingLeaves delta n
                (stoppingChild w i),
              S.stoppingWeight s (S.stoppingLeafWord delta leaf) := by
            rw [Fintype.sum_sigma]
          _ = ∑ i : iota, S.stoppingWeight s (stoppingChild w i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact sum_stoppingLeafWeight hdim delta n (stoppingChild w i)
          _ = S.stoppingWeight s w := by
            simp only [stoppingWeight_child, ← Finset.mul_sum,
              S.sum_tubeWeight hdim, mul_one]

omit [Nonempty iota] in
/-- Every point of a prefix cylinder lies in a cylinder indexed by one of the
stopping leaves. -/
theorem IsAttractor.exists_stoppingLeaf_mem {K : Set ℝ}
    (hK : S.IsAttractor K) (delta : ℝ) :
    ∀ (n : ℕ) (w : StoppingWord iota) {x : ℝ},
      x ∈ hK.stoppingCylinder S w.1 w.2 ->
        ∃ leaf : S.StoppingLeaves delta n w,
          x ∈ hK.stoppingCylinder S
            (S.stoppingLeafWord delta leaf).1
            (S.stoppingLeafWord delta leaf).2
  | 0, w, x, hx => by
      exact ⟨.cutoff w, hx⟩
  | Nat.succ n, w, x, hx => by
      by_cases h : S.stoppingRatio w ≤ delta
      · exact ⟨.stop h, hx⟩
      · obtain ⟨i, hxi⟩ := hK.exists_mem_stoppingCylinder_child S hx
        obtain ⟨leaf, hleaf⟩ :=
          hK.exists_stoppingLeaf_mem delta n (stoppingChild w i) hxi
        exact ⟨.branch h i leaf, hleaf⟩

/-- If the remaining maximal contraction brings the current ratio below the
threshold, every leaf ratio is below the threshold. -/
theorem stoppingLeafRatio_le_of_mul_maxRatio_pow_le (delta : ℝ) :
    ∀ (n : ℕ) (w : StoppingWord iota),
      S.stoppingRatio w * Hutchinson.maxRatio S ^ n ≤ delta ->
      ∀ leaf : S.StoppingLeaves delta n w,
        S.stoppingRatio (S.stoppingLeafWord delta leaf) ≤ delta
  | 0, w, hscale, leaf => by
      cases leaf
      change S.stoppingRatio w ≤ delta
      simpa using hscale
  | Nat.succ n, w, hscale, leaf => by
      cases leaf with
      | stop h => exact h
      | branch h i child =>
          apply stoppingLeafRatio_le_of_mul_maxRatio_pow_le delta n
            (stoppingChild w i) ?_ child
          have hratio_nonneg : 0 ≤ S.stoppingRatio w :=
            (S.generationRatio_pos w.1 w.2).le
          have hpow_nonneg : 0 ≤ Hutchinson.maxRatio S ^ n :=
            pow_nonneg (Hutchinson.maxRatio_pos S).le n
          calc
            S.stoppingRatio (stoppingChild w i) *
                  Hutchinson.maxRatio S ^ n =
                S.stoppingRatio w * S.ratio i *
                  Hutchinson.maxRatio S ^ n := by rw [stoppingRatio_child]
            _ ≤ S.stoppingRatio w * Hutchinson.maxRatio S *
                  Hutchinson.maxRatio S ^ n := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left
                    (Hutchinson.ratio_le_maxRatio S i) hratio_nonneg)
                  hpow_nonneg
            _ = S.stoppingRatio w * Hutchinson.maxRatio S ^ (n + 1) := by
                rw [pow_succ]
                ring
            _ ≤ delta := hscale

/-- The leaves of a sufficiently deep tree are all genuine stopping words. -/
theorem stoppingLeafRatio_le {delta : ℝ} {n : ℕ}
    (hscale : Hutchinson.maxRatio S ^ n ≤ delta)
    (leaf : S.StoppingLeaves delta n (stoppingRoot : StoppingWord iota)) :
    S.stoppingRatio
        (S.stoppingLeafWord delta leaf) ≤
      delta := by
  apply S.stoppingLeafRatio_le_of_mul_maxRatio_pow_le delta n
    (stoppingRoot : StoppingWord iota)
  simpa using hscale

omit [Nonempty iota] in
/-- Product weights are the `s`-powers of product ratios. -/
theorem stoppingWeight_eq_ratio_rpow (s : ℝ) (w : StoppingWord iota) :
    S.stoppingWeight s w = S.stoppingRatio w ^ s :=
  S.generationWeight_eq_ratio_rpow s w.1 w.2

omit [Nonempty iota] in
/-- Exact stopping-antichain mass identity at the similarity dimension. -/
theorem sum_stoppingLeafRatio_rpow {s : ℝ} (hdim : S.IsDimension s)
    (delta : ℝ) (n : ℕ) (w : StoppingWord iota) :
    (∑ leaf : S.StoppingLeaves delta n w,
      S.stoppingRatio (S.stoppingLeafWord delta leaf) ^ s) =
        S.stoppingRatio w ^ s := by
  simpa only [← S.stoppingWeight_eq_ratio_rpow s] using
    S.sum_stoppingLeafWeight hdim delta n w

omit [Nonempty iota] in
/-- A leaf never contracts past one additional one-letter ratio after the
threshold crossing. -/
theorem min_stoppingRatio_mul_delta_le_leafRatio
    {rmin delta : ℝ} (hrmin0 : 0 ≤ rmin) (hrmin1 : rmin ≤ 1)
    (hdelta : 0 ≤ delta) (hmin : ∀ i, rmin ≤ S.ratio i) :
    ∀ {n : ℕ} {w : StoppingWord iota}
      (leaf : S.StoppingLeaves delta n w),
      min (S.stoppingRatio w) (rmin * delta) ≤
        S.stoppingRatio (S.stoppingLeafWord delta leaf)
  | _, _, .cutoff w => min_le_left _ _
  | _, w, .stop h => min_le_left _ _
  | _, w, .branch h i leaf => by
      have hparent : delta < S.stoppingRatio w := lt_of_not_ge h
      have hrootLower : rmin * delta ≤ S.stoppingRatio w :=
        (mul_le_of_le_one_left hdelta hrmin1).trans hparent.le
      have hchildLower : rmin * delta ≤
          S.stoppingRatio (stoppingChild w i) := by
        rw [stoppingRatio_child]
        have := mul_le_mul (hmin i) hparent.le hdelta
          (S.ratio_pos i).le
        nlinarith
      rw [min_eq_right hrootLower]
      change rmin * delta ≤
        S.stoppingRatio (S.stoppingLeafWord delta leaf)
      simpa only [min_eq_right hchildLower] using
        (min_stoppingRatio_mul_delta_le_leafRatio hrmin0 hrmin1
          hdelta hmin leaf)

omit [Nonempty iota] in
/-- At the root, every stopping ratio is at least `rmin * delta`. -/
theorem stoppingRatio_lower_of_leaf {rmin delta : ℝ}
    (hrmin0 : 0 ≤ rmin) (hrmin1 : rmin ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hmin : ∀ i, rmin ≤ S.ratio i) {n : ℕ}
    (leaf : S.StoppingLeaves delta n (stoppingRoot : StoppingWord iota)) :
    rmin * delta ≤ S.stoppingRatio (S.stoppingLeafWord delta leaf) := by
  have hprod : rmin * delta ≤ 1 :=
    (mul_le_of_le_one_left hdelta0 hrmin1).trans hdelta1
  simpa only [stoppingRatio_root, min_eq_right hprod] using
    S.min_stoppingRatio_mul_delta_le_leafRatio hrmin0 hrmin1 hdelta0 hmin leaf

/-- Every positive threshold admits a finite depth at which all branches have
crossed it. -/
theorem exists_stoppingDepth {delta : ℝ} (hdelta : 0 < delta) :
    ∃ n : ℕ, Hutchinson.maxRatio S ^ n ≤ delta := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hdelta
    (Hutchinson.maxRatio_lt_one S)
  exact ⟨n, hn.le⟩

end System

end

end BrownianImages
