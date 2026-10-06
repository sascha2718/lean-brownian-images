/-
Two elementary facts about functions of one real variable, used to turn the one-sided
finite-difference bounds of `TwoContraction.Moment` into strict monotonicity of the mean
in `thm:two-contraction-distinction`, without differentiating the moment `M(s)`.

* `eventually_lt_of_hasDerivAt_pos`: a positive derivative makes a function locally
  strictly increasing on both sides.
* `strictMonoOn_of_local`: `thm:local-monotonicity`, a function locally strictly
  increasing on both sides at every point of an interval is strictly increasing there.
  No continuity is needed.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRightNhds

namespace BrownianImages

open Set Filter
open scoped Topology

/-- A positive derivative makes a function locally strictly increasing on both sides. -/
theorem eventually_lt_of_hasDerivAt_pos {φ : ℝ → ℝ} {φ' x : ℝ} (h : HasDerivAt φ φ' x)
    (hpos : 0 < φ') :
    (∀ᶠ y in 𝓝[>] x, φ x < φ y) ∧ (∀ᶠ y in 𝓝[<] x, φ y < φ x) := by
  have hslope := hasDerivAt_iff_tendsto_slope.1 h
  have hev : ∀ᶠ y in 𝓝[≠] x, 0 < slope φ x y := hslope.eventually (lt_mem_nhds hpos)
  constructor
  · have hev' : ∀ᶠ y in 𝓝[>] x, 0 < slope φ x y :=
      nhdsWithin_mono _ (fun y hy => ne_of_gt hy) hev
    filter_upwards [hev', self_mem_nhdsWithin] with y hy hxy
    rw [slope_def_field] at hy
    have : 0 < y - x := sub_pos.2 hxy
    have := (div_pos_iff_of_pos_right this).1 hy
    linarith
  · have hev' : ∀ᶠ y in 𝓝[<] x, 0 < slope φ x y :=
      nhdsWithin_mono _ (fun y hy => ne_of_lt hy) hev
    filter_upwards [hev', self_mem_nhdsWithin] with y hy hxy
    rw [slope_def_field] at hy
    have hneg : y - x < 0 := sub_neg.2 hxy
    have := (div_pos_iff.1 hy)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith

/-- **`thm:local-monotonicity`.**  A function that, at every point of an interval, is
larger slightly to the right and smaller slightly to the left is strictly increasing on
the interval. -/
theorem strictMonoOn_of_local {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hloc : ∀ x ∈ I, (∀ᶠ y in 𝓝[>] x, f x < f y) ∧ (∀ᶠ y in 𝓝[<] x, f y < f x)) :
    StrictMonoOn f I := by
  -- the weak form on `[x, y]`
  have hweak : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → f x ≤ f y := by
    intro x hx y hy hxy
    set T : Set ℝ := {t | t ∈ Icc x y ∧ ∀ u ∈ Icc x t, f x ≤ f u} with hT
    have hxT : x ∈ T := ⟨⟨le_rfl, hxy⟩, fun u hu => by rw [le_antisymm hu.2 hu.1]⟩
    have hbdd : BddAbove T := ⟨y, fun t ht => ht.1.2⟩
    have hne : T.Nonempty := ⟨x, hxT⟩
    set t := sSup T with ht
    have hxt : x ≤ t := le_csSup hbdd hxT
    have hty : t ≤ y := csSup_le hne fun s hs => hs.1.2
    have htab : t ∈ I := hI.out hx hy ⟨hxt, hty⟩
    -- every point strictly below `t` is controlled
    have hbelow : ∀ u ∈ Icc x t, u < t → f x ≤ f u := by
      intro u hu hut
      obtain ⟨s, hs, hus⟩ := (lt_csSup_iff hbdd hne).1 hut
      exact hs.2 u ⟨hu.1, hus.le⟩
    -- `t` itself is controlled
    have htT : t ∈ T := by
      refine ⟨⟨hxt, hty⟩, fun u hu => ?_⟩
      rcases lt_or_eq_of_le hu.2 with hlt | heq
      · exact hbelow u hu hlt
      · rw [heq]
        rcases lt_or_eq_of_le hxt with hxt' | hxteq
        · obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hloc t htab).2
          set v := max l x + (t - max l x) / 2 with hv
          have hlx : max l x < t := max_lt hl hxt'
          have hv1 : max l x < v := by rw [hv]; linarith
          have hv2 : v < t := by rw [hv]; linarith
          have hfv : f v < f t := hsub ⟨lt_of_le_of_lt (le_max_left _ _) hv1, hv2⟩
          have := hbelow v ⟨(le_max_right _ _).trans hv1.le, hv2.le⟩ hv2
          linarith
        · rw [← hxteq]
    -- `t = y`
    have hty' : t = y := by
      by_contra hne'
      have hlt : t < y := lt_of_le_of_ne hty hne'
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hloc t htab).1
      set t' := min (t + (u - t) / 2) y with ht'
      have hu' : t < u := hu
      have ht't : t < t' := lt_min (by linarith) hlt
      have ht'T : t' ∈ T := by
        refine ⟨⟨hxt.trans ht't.le, min_le_right _ _⟩, fun w hw => ?_⟩
        rcases le_or_gt w t with hwt | hwt
        · exact htT.2 w ⟨hw.1, hwt⟩
        · have hw2 : w < u := lt_of_le_of_lt hw.2
            (lt_of_le_of_lt (min_le_left _ _) (by linarith))
          have h1 : f t < f w := hsub ⟨hwt, hw2⟩
          have h2 := htT.2 t ⟨hxt, le_rfl⟩
          linarith
      have := le_csSup hbdd ht'T
      linarith
    rw [← hty']
    exact htT.2 t ⟨hxt, le_rfl⟩
  intro x hx y hy hxy
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hloc x hx).1
  set v := min (x + (u - x) / 2) (x + (y - x) / 2) with hv
  have hu' : x < u := hu
  have hxv : x < v := lt_min (by linarith) (by linarith)
  have hvu : v < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hvy : v < y := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hfv : f x < f v := hsub ⟨hxv, hvu⟩
  have hvab : v ∈ I := hI.out hx hy ⟨hxv.le, hvy.le⟩
  exact lt_of_lt_of_le hfv (hweak v hvab y hy hvy.le)

end BrownianImages
