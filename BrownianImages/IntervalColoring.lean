/-
`thm:stopping-overlap` of `sec:renewal`, the combinatorial half: a finite family of
closed intervals in which every point lies in at most `M` members can be partitioned
into at most `M` subfamilies with pairwise disjoint interiors.

The paper orders the intervals by their left endpoints and assigns each interval a
class not occupied by an earlier interval whose interior extends past that endpoint.
The proof below runs the same greedy colouring as an induction on the finite set of
intervals, removing at each step an interval of maximal left endpoint: the earlier
intervals whose interiors meet it all contain its left endpoint, so together with it
they are at most `M` intervals and some class is free.

* `exists_interval_coloring`: the colouring, for intervals `Icc (a i) (b i)` indexed by
  a finite type.
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.Linarith

namespace BrownianImages

open Set

namespace IntervalColoring

variable {α : Type*} [DecidableEq α]

/-- Two closed intervals whose open interiors meet, the second having the larger
left endpoint, both contain that left endpoint. -/
theorem left_mem_of_not_disjoint_interior {a b a' b' : ℝ} (hle : a ≤ a')
    (hmeet : ¬ Disjoint (Ioo a b) (Ioo a' b')) :
    a' ∈ Icc a b := by
  rw [Set.not_disjoint_iff] at hmeet
  obtain ⟨y, ⟨_, hyb⟩, ⟨hay', _⟩⟩ := hmeet
  exact ⟨hle, by linarith⟩

/-- The greedy colouring on a finite set of indices, by induction on the set. -/
theorem exists_coloring_on (a b : α → ℝ) (hab : ∀ i, a i ≤ b i) (M : ℕ) (hM : 0 < M)
    (hmult : ∀ x : ℝ, ∀ T : Finset α, (∀ i ∈ T, x ∈ Icc (a i) (b i)) → T.card ≤ M) :
    ∀ T : Finset α, ∃ c : α → Fin M, ∀ i ∈ T, ∀ j ∈ T, i ≠ j → c i = c j →
      Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)) := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => ⟨0, hM⟩, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    obtain ⟨i₀, hi₀, hmax⟩ := T.exists_max_image a hne
    set T' := T.erase i₀ with hT'
    have hT'lt : T' ⊂ T := Finset.erase_ssubset hi₀
    obtain ⟨c', hc'⟩ := ih T' hT'lt
    -- the earlier intervals whose interiors meet the interior of `i₀`
    set N : Finset α := T'.filter fun j => ¬ Disjoint (Ioo (a j) (b j)) (Ioo (a i₀) (b i₀))
      with hN
    have hNleft : ∀ j ∈ N, a i₀ ∈ Icc (a j) (b j) := by
      intro j hj
      rw [hN, Finset.mem_filter] at hj
      obtain ⟨hjT', hjmeet⟩ := hj
      have hjT : j ∈ T := Finset.mem_of_mem_erase hjT'
      exact left_mem_of_not_disjoint_interior (hmax j hjT) hjmeet
    have hcard : (insert i₀ N).card ≤ M := by
      refine hmult (a i₀) (insert i₀ N) fun j hj => ?_
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact ⟨le_rfl, hab j⟩
      · exact hNleft j hj
    have hi₀N : i₀ ∉ N := by
      rw [hN, Finset.mem_filter]
      exact fun h => (Finset.notMem_erase i₀ T) h.1
    have hNcard : N.card < M := by
      have := Finset.card_insert_of_notMem hi₀N
      omega
    -- a colour not used on `N`
    have hfree : ∃ k : Fin M, k ∉ N.image c' := by
      have hlt : (N.image c').card < (Finset.univ : Finset (Fin M)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt Finset.card_image_le hNcard
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hfree
    refine ⟨Function.update c' i₀ k, ?_⟩
    intro i hi j hj hij hcij
    have hmem : ∀ l ∈ T, l ≠ i₀ → l ∈ T' := fun l hl hl0 => Finset.mem_erase.mpr ⟨hl0, hl⟩
    by_cases hi0 : i = i₀
    · subst hi0
      have hj0 : j ≠ i := fun h => hij h.symm
      rw [Function.update_self, Function.update_of_ne hj0] at hcij
      have hjT' : j ∈ T' := hmem j hj hj0
      have hjN : j ∉ N := by
        intro hjN
        exact hk (Finset.mem_image.mpr ⟨j, hjN, hcij.symm⟩)
      rw [hN, Finset.mem_filter, not_and, not_not] at hjN
      exact (hjN hjT').symm
    · by_cases hj0 : j = i₀
      · subst hj0
        rw [Function.update_self, Function.update_of_ne hi0] at hcij
        have hiT' : i ∈ T' := hmem i hi hi0
        have hiN : i ∉ N := by
          intro hiN
          exact hk (Finset.mem_image.mpr ⟨i, hiN, hcij⟩)
        rw [hN, Finset.mem_filter, not_and, not_not] at hiN
        exact hiN hiT'
      · rw [Function.update_of_ne hi0, Function.update_of_ne hj0] at hcij
        exact hc' i (hmem i hi hi0) j (hmem j hj hj0) hij hcij

/-- **Interval colouring.**  If every real number lies in at most `M ≥ 1` of the closed
intervals `Icc (a i) (b i)`, then the intervals can be coloured with `M` colours so
that intervals of one colour have disjoint interiors. -/
theorem exists_interval_coloring {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α → ℝ) (hab : ∀ i, a i ≤ b i) (M : ℕ) (hM : 0 < M)
    (hmult : ∀ x : ℝ,
      (Finset.univ.filter fun i => x ∈ Icc (a i) (b i)).card ≤ M) :
    ∃ c : α → Fin M, ∀ i j, i ≠ j → c i = c j →
      Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)) := by
  classical
  have hmult' : ∀ x : ℝ, ∀ T : Finset α, (∀ i ∈ T, x ∈ Icc (a i) (b i)) → T.card ≤ M := by
    intro x T hT
    refine le_trans (Finset.card_le_card ?_) (hmult x)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hT i hi⟩
  obtain ⟨c, hc⟩ := exists_coloring_on a b hab M hM hmult' Finset.univ
  exact ⟨c, fun i j hij hcij => hc i (Finset.mem_univ i) j (Finset.mem_univ j) hij hcij⟩

end IntervalColoring

end BrownianImages
