/-
`thm:neighbourhood-overlap` of `sec:reconstruction`, under the strong open set
condition: the expected overlap of the Brownian `r`-neighbourhoods of two distinct
first-level pieces is `O(r^{α+2η})`, and so is the expected multiple-counting defect.

The first-level time intervals may overlap, so the Gaussian-gap estimate is applied
not to the pieces but to the stopping cylinders at temporal scale `ρ = r²` below each
of them.  For two such cylinders the expected overlap is at most `C ρ² / max(ρ, d)`,
where `d` is the gap between their time intervals: for `d ≤ ρ` by the area of one
neighbourhood, for `d > ρ` by the Gaussian density of the increment across the gap.
The number of cylinder pairs with gap at most `h` is controlled through
`eq:cross-piece-mass`, since the stopping words carry the natural measure, and a dyadic
sum over the gaps gives the bound.

* `tubeOverlapArea_le_tubeArea_left`, `tubeOverlapArea_le_sum_of_subset_iUnion`: the
  deterministic overlap-area inequalities.
* `IsPlanarBrownian.integrable_and_integral_tubeArea_stoppingCylinder_le`: the area of
  the `r`-neighbourhood of a cylinder of temporal length at most `r²` has expectation
  `O(r²)`, from the Brownian maximal estimate.
* `IsPlanarBrownian.integral_tubeOverlapArea_stoppingCylinders_le`:
  `eq:stopping-brownian-overlap`.
* `IsNatural.card_closePairs_le`: `eq:stopping-close-pairs`.
* `sum_dyadic_le`: the dyadic summation.
* `IsNatural.exists_pairwise_tubeOverlap_node_of_sosc`,
  `IsNatural.exists_tubeDefect_node_of_sosc`: the same bounds below an arbitrary node
  of the stopping tree, with the factor `r_w^{s-η}` that Brownian scaling predicts; the
  concentration argument consumes them at every internal node.
* `IsNatural.exists_pairwise_tubeOverlap_of_sosc`, `IsNatural.tubeOverlap_of_sosc`:
  `thm:neighbourhood-overlap`.
-/
import BrownianImages.CrossPiece
import BrownianImages.Minkowski.StoppingTubeUpper
import BrownianImages.Minkowski.BrownianMaximalMoment
import BrownianImages.Minkowski.BrownianOverlapGeometry
import BrownianImages.Minkowski.DefectExpectation
import BrownianImages.Minkowski.TubeRenewal

namespace BrownianImages

open MeasureTheory ProbabilityTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe u

/-! ### Deterministic overlap-area inequalities -/

/-- The thickening of a compact planar set has finite area. -/
theorem volume_thickening_compactPlane_ne_top (r : ℝ) (F : CompactPlane) :
    volume (Metric.thickening r (F : Set Plane)) ≠ ∞ :=
  (F.isCompact.isBounded.thickening).measure_lt_top.ne

/-- The overlap area of two neighbourhoods is at most the area of the first. -/
theorem tubeOverlapArea_le_tubeArea_left (r : ℝ) (F G : CompactPlane) :
    tubeOverlapArea r F G ≤ tubeArea r F := by
  rw [tubeOverlapArea_eq_measureReal]
  exact measureReal_mono Set.inter_subset_left (volume_thickening_compactPlane_ne_top r F)

/-- The overlap area is measurable in the pair of compact sets. -/
theorem measurable_tubeOverlapArea_pair {r : ℝ} (hr : 0 < r) :
    Measurable (fun p : CompactPlane × CompactPlane => tubeOverlapArea r p.1 p.2) := by
  have h0 : ∀ G : CompactPlane, translateCompact 0 G = G := by
    intro G
    apply NonemptyCompacts.ext
    rw [coe_translateCompact]
    ext x
    simp
  have heq : (fun p : CompactPlane × CompactPlane => tubeOverlapArea r p.1 p.2)
      = fun p => translatedTubeOverlap r (p, (0 : Plane)) := by
    funext p
    simp only [translatedTubeOverlap, h0]
  rw [heq]
  exact (measurable_translatedTubeOverlap hr).comp (measurable_id.prodMk measurable_const)

/-- Overlap area is subadditive over finite covers of the two sets. -/
theorem tubeOverlapArea_le_sum_of_subset_iUnion {J J' : Type*} [Fintype J] [Fintype J']
    (r : ℝ) (F G : CompactPlane) (FJ : J → CompactPlane) (GJ : J' → CompactPlane)
    (hF : (F : Set Plane) ⊆ ⋃ j, (FJ j : Set Plane))
    (hG : (G : Set Plane) ⊆ ⋃ j, (GJ j : Set Plane)) :
    tubeOverlapArea r F G ≤ ∑ j, ∑ j', tubeOverlapArea r (FJ j) (GJ j') := by
  simp only [tubeOverlapArea_eq_measureReal]
  have hsub : Metric.thickening r (F : Set Plane) ∩ Metric.thickening r (G : Set Plane)
      ⊆ ⋃ p : J × J', Metric.thickening r (FJ p.1 : Set Plane) ∩
        Metric.thickening r (GJ p.2 : Set Plane) := by
    rintro x ⟨hxF, hxG⟩
    have h1 := Metric.thickening_subset_of_subset r hF hxF
    have h2 := Metric.thickening_subset_of_subset r hG hxG
    rw [Metric.thickening_iUnion] at h1 h2
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h1
    obtain ⟨j', hj'⟩ := Set.mem_iUnion.mp h2
    exact Set.mem_iUnion.mpr ⟨(j, j'), hj, hj'⟩
  have hfin : ∀ p : J × J', volume (Metric.thickening r (FJ p.1 : Set Plane) ∩
      Metric.thickening r (GJ p.2 : Set Plane)) ≠ ∞ := fun p =>
    ne_top_of_le_ne_top (volume_thickening_compactPlane_ne_top r (FJ p.1))
      (measure_mono Set.inter_subset_left)
  calc volume.real (Metric.thickening r (F : Set Plane) ∩ Metric.thickening r (G : Set Plane))
      ≤ volume.real (⋃ p : J × J', Metric.thickening r (FJ p.1 : Set Plane) ∩
          Metric.thickening r (GJ p.2 : Set Plane)) := by
        refine measureReal_mono hsub ?_
        exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun p _ => hfin p)
          (measure_iUnion_fintype_le volume _)
    _ ≤ ∑ p : J × J', volume.real (Metric.thickening r (FJ p.1 : Set Plane) ∩
          Metric.thickening r (GJ p.2 : Set Plane)) := measureReal_iUnion_fintype_le _
    _ = ∑ j, ∑ j', volume.real (Metric.thickening r (FJ j : Set Plane) ∩
          Metric.thickening r (GJ j' : Set Plane)) := Fintype.sum_prod_type _

/-! ### The dyadic summation -/

/-- **The dyadic summation of `thm:neighbourhood-overlap`.**  If a finite family of gaps
`d p ∈ [0, 1]` has at most `N₀ h^β` members below every `h ≥ ρ`, with `β < 1`, then
`∑_p C ρ² / max(ρ, d p) ≤ 2 C N₀ ρ^{1+β} / (1 - 2^{β-1})`: group the members by the
dyadic scale `2^k ρ` of their gap and sum the geometric series. -/
theorem sum_dyadic_le {ι : Type*} [Fintype ι] (d : ι → ℝ) {ρ C N₀ β : ℝ} (hρ : 0 < ρ)
    (hC : 0 ≤ C) (hN₀ : 0 ≤ N₀) (hβ : β < 1) (hd1 : ∀ p, d p ≤ 1)
    (hcount : ∀ h : ℝ, ρ ≤ h →
      ((Finset.univ.filter fun p => d p ≤ h).card : ℝ) ≤ N₀ * h ^ β) :
    ∑ p, C * ρ ^ 2 / max ρ (d p) ≤ 2 * C * N₀ * ρ ^ (1 + β) / (1 - (2:ℝ) ^ (β - 1)) := by
  classical
  -- a dyadic level past every gap
  obtain ⟨Kmax, hKmax⟩ := exists_pow_lt_of_lt_one hρ (by norm_num : (1:ℝ) / 2 < 1)
  have hKρ : 1 ≤ (2:ℝ) ^ Kmax * ρ := by
    have h2 : (1:ℝ) / 2 ^ Kmax < ρ := by rwa [one_div_pow] at hKmax
    rw [div_lt_iff₀ (by positivity)] at h2
    linarith
  have hex : ∀ p, ∃ k : ℕ, d p ≤ (2:ℝ) ^ k * ρ := fun p => ⟨Kmax, (hd1 p).trans hKρ⟩
  set kidx : ι → ℕ := fun p => Nat.find (hex p) with hkidx
  have hkspec : ∀ p, d p ≤ (2:ℝ) ^ kidx p * ρ := fun p => Nat.find_spec (hex p)
  have hkmin : ∀ p (k : ℕ), k < kidx p → (2:ℝ) ^ k * ρ < d p := fun p k hk =>
    not_le.mp (Nat.find_min (hex p) hk)
  have hkle : ∀ p, kidx p ≤ Kmax := fun p => Nat.find_le ((hd1 p).trans hKρ)
  set q : ℝ := (2:ℝ) ^ (β - 1) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  -- the bound on one dyadic level
  have hlevel : ∀ p, C * ρ ^ 2 / max ρ (d p) ≤ 2 * C * ρ / (2:ℝ) ^ kidx p := by
    intro p
    rcases Nat.eq_zero_or_pos (kidx p) with h0 | hpos
    · rw [h0, pow_zero, div_one]
      have hmax : ρ ≤ max ρ (d p) := le_max_left _ _
      calc C * ρ ^ 2 / max ρ (d p) ≤ C * ρ ^ 2 / ρ :=
            div_le_div_of_nonneg_left (by positivity) hρ hmax
        _ = C * ρ := by field_simp
        _ ≤ 2 * C * ρ := by nlinarith
    · have hlt := hkmin p (kidx p - 1) (Nat.sub_lt hpos one_pos)
      have hmax : (2:ℝ) ^ (kidx p - 1) * ρ ≤ max ρ (d p) := hlt.le.trans (le_max_right _ _)
      have hpow : (2:ℝ) ^ kidx p = 2 * (2:ℝ) ^ (kidx p - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      calc C * ρ ^ 2 / max ρ (d p) ≤ C * ρ ^ 2 / ((2:ℝ) ^ (kidx p - 1) * ρ) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hmax
        _ = 2 * C * ρ / (2:ℝ) ^ kidx p := by
            rw [hpow]
            field_simp
  -- the number of members on one dyadic level
  have hcard : ∀ k : ℕ, ((Finset.univ.filter fun p => kidx p = k).card : ℝ)
      ≤ N₀ * ((2:ℝ) ^ k * ρ) ^ β := by
    intro k
    refine le_trans ?_ (hcount ((2:ℝ) ^ k * ρ) ?_)
    · have hsub : (Finset.univ.filter fun p => kidx p = k)
          ⊆ Finset.univ.filter fun p => d p ≤ (2:ℝ) ^ k * ρ := by
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        refine ⟨hp.1, ?_⟩
        rw [← hp.2]
        exact hkspec p
      exact_mod_cast Finset.card_le_card hsub
    · calc ρ = 1 * ρ := (one_mul ρ).symm
        _ ≤ (2:ℝ) ^ k * ρ := by gcongr; exact one_le_pow₀ (by norm_num)
  -- the geometric series
  have hterm : ∀ k : ℕ, N₀ * ((2:ℝ) ^ k * ρ) ^ β * (2 * C * ρ / (2:ℝ) ^ k)
      = 2 * C * N₀ * ρ ^ (1 + β) * q ^ k := by
    intro k
    have h2k : (0:ℝ) < (2:ℝ) ^ k := by positivity
    have hqk : q ^ k = (2:ℝ) ^ ((k : ℝ) * β) / (2:ℝ) ^ k := by
      rw [hq, ← Real.rpow_natCast q k, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_sub (by norm_num)]
      congr 1
      ring
    have h2kβ : ((2:ℝ) ^ k) ^ β = (2:ℝ) ^ ((k : ℝ) * β) := by
      rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_mul (by norm_num)]
    rw [Real.mul_rpow (by positivity) hρ.le, h2kβ, hqk, Real.rpow_add hρ, Real.rpow_one]
    field_simp
  calc ∑ p, C * ρ ^ 2 / max ρ (d p)
      = ∑ k ∈ Finset.range (Kmax + 1), ∑ p ∈ Finset.univ.filter (fun p => kidx p = k),
          C * ρ ^ 2 / max ρ (d p) := by
        rw [Finset.sum_fiberwise_of_maps_to]
        intro p _
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (hkle p)
    _ ≤ ∑ k ∈ Finset.range (Kmax + 1), ∑ p ∈ Finset.univ.filter (fun p => kidx p = k),
          2 * C * ρ / (2:ℝ) ^ k := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_filter] at hp
        rw [← hp.2]
        exact hlevel p
    _ = ∑ k ∈ Finset.range (Kmax + 1),
          ((Finset.univ.filter fun p => kidx p = k).card : ℝ) * (2 * C * ρ / (2:ℝ) ^ k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.range (Kmax + 1), N₀ * ((2:ℝ) ^ k * ρ) ^ β * (2 * C * ρ / (2:ℝ) ^ k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_right (hcard k) (by positivity)
    _ = 2 * C * N₀ * ρ ^ (1 + β) * ∑ k ∈ Finset.range (Kmax + 1), q ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => hterm k
    _ ≤ 2 * C * N₀ * ρ ^ (1 + β) * (1 - q)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine ((summable_geometric_of_lt_one hq0.le hq1).sum_le_tsum _
          (fun i _ => pow_nonneg hq0.le i)).trans_eq ?_
        exact tsum_geometric_of_lt_one hq0.le hq1
    _ = 2 * C * N₀ * ρ ^ (1 + β) / (1 - (2:ℝ) ^ (β - 1)) := by
        rw [div_eq_mul_inv]

/-! ### The area of a stopping cylinder's neighbourhood -/

open _root_.BrownianImages.System (StoppingWord stoppingRoot stoppingChild)

variable {iota : Type u} [Fintype iota] [Nonempty iota] (S : System iota)
variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  {W : NNReal → Omega → Plane}

omit [Nonempty iota] in
/-- **The Brownian maximal estimate for a stopping cylinder.**  The `r`-neighbourhood of
the Brownian image of a cylinder of temporal length at most `r²` has expected area at
most `C r²`, with `C = π 𝔼(1 + R)²` for the unit Brownian radius `R`. -/
theorem IsPlanarBrownian.integrable_and_integral_tubeArea_stoppingCylinder_le
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P) {K : Set ℝ} (hK : S.IsAttractor K)
    (w : StoppingWord iota) {r : ℝ} (hr : 0 < r) (hlen : S.stoppingRatio w ≤ r ^ 2)
    (hunit : Integrable (fun omega => (1 + standardBrownianRadius W omega) ^ (2:ℝ)) P) :
    Integrable (fun omega =>
      tubeArea r (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)) P ∧
    (∫ omega, tubeArea r (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega) ∂P)
      ≤ (Real.pi * ∫ omega, (1 + standardBrownianRadius W omega) ^ (2:ℝ) ∂P) * r ^ 2 := by
  have hℓ : S.stoppingLength w ≠ 0 := S.stoppingLength_ne_zero w
  have hlen' : ((S.stoppingLength w : NNReal) : ℝ) ≤ r ^ 2 := by
    rw [System.coe_stoppingLength]; exact hlen
  obtain ⟨hint, hbound⟩ := hW.intervalOscillation_moment_le_of_standard (S.stoppingAnchor w)
    hℓ hr (by norm_num : (1:ℝ) ≤ 2) hlen' hunit
  set osc : Omega → ℝ :=
    brownianIntervalOscillationRadius W (S.stoppingAnchor w) (S.stoppingLength w) with hosc
  have hpt : ∀ᵐ omega ∂P, tubeArea r (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
      ≤ Real.pi * (r + osc omega) ^ (2:ℝ) := by
    filter_upwards [hW.ae_continuous] with omega homega
    have hsub := hK.brownianStoppingCylinder_subset_disc S hK.2.2.1 W w homega
    have h := tubeArea_le_pi_mul_sum_sq_of_subset_iUnion_closedBall (J := Unit)
      (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
      (fun _ => W (S.stoppingAnchor w) omega) (fun _ => osc omega) hr
      (fun _ => brownianIntervalOscillationRadius_nonneg _ _ _ _)
      (by rw [Set.iUnion_const]; exact hsub)
    rw [Real.rpow_two]
    simpa using h
  have hmeas : AEStronglyMeasurable
      (fun omega => tubeArea r (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)) P :=
    ((measurable_tubeArea r).comp_aemeasurable
      (hW.aemeasurable_brownianImage _)).aestronglyMeasurable
  have hint' : Integrable
      (fun omega => tubeArea r (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)) P := by
    refine (hint.const_mul Real.pi).mono' hmeas ?_
    filter_upwards [hpt] with omega h
    rw [Real.norm_of_nonneg (tubeArea_nonneg _ _)]
    exact h
  refine ⟨hint', ?_⟩
  calc (∫ omega, tubeArea r (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega) ∂P)
      ≤ ∫ omega, Real.pi * (r + osc omega) ^ (2:ℝ) ∂P :=
        integral_mono_ae hint' (hint.const_mul _) hpt
    _ = Real.pi * ∫ omega, (r + osc omega) ^ (2:ℝ) ∂P := integral_const_mul _ _
    _ ≤ Real.pi * (r ^ (2:ℝ) * ∫ omega, (1 + standardBrownianRadius W omega) ^ (2:ℝ) ∂P) :=
        mul_le_mul_of_nonneg_left hbound Real.pi_nonneg
    _ = (Real.pi * ∫ omega, (1 + standardBrownianRadius W omega) ^ (2:ℝ) ∂P) * r ^ 2 := by
        rw [Real.rpow_two]
        ring

/-! ### Two stopping cylinders -/

namespace System

omit [Nonempty iota] in
/-- The gap `dist(I_w, I_v)` between the time intervals of two stopping words, taken as a
signed quantity: it is the distance when the intervals are disjoint and non-positive
when they meet. -/
def wordGap (w v : StoppingWord iota) : ℝ :=
  max ((S.stoppingAnchor v : ℝ) - ((S.stoppingAnchor w : ℝ) + S.stoppingRatio w))
    ((S.stoppingAnchor w : ℝ) - ((S.stoppingAnchor v : ℝ) + S.stoppingRatio v))

omit [Nonempty iota] in
/-- The gap is symmetric. -/
theorem wordGap_comm (w v : StoppingWord iota) : S.wordGap w v = S.wordGap v w := by
  unfold wordGap
  exact max_comm _ _

omit [Nonempty iota] in
/-- The gap between two stopping intervals is at most one. -/
theorem wordGap_le_one (w v : StoppingWord iota) : S.wordGap w v ≤ 1 := by
  unfold wordGap
  have h1 : (S.stoppingAnchor v : ℝ) ≤ 1 := by
    rw [System.coe_stoppingAnchor]
    have := S.stoppingLeft_add_le_one v
    have : 0 < S.stoppingRatio v := S.generationRatio_pos v.1 v.2
    linarith
  have h2 : (S.stoppingAnchor w : ℝ) ≤ 1 := by
    rw [System.coe_stoppingAnchor]
    have := S.stoppingLeft_add_le_one w
    have : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
    linarith
  have h3 : (0:ℝ) ≤ S.stoppingAnchor w := NNReal.coe_nonneg _
  have h4 : (0:ℝ) ≤ S.stoppingAnchor v := NNReal.coe_nonneg _
  have h5 : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have h6 : 0 < S.stoppingRatio v := S.generationRatio_pos v.1 v.2
  exact max_le (by linarith) (by linarith)

omit [Nonempty iota] in
/-- Two points of the stopping intervals of two words are at distance at most the gap
plus the two lengths. -/
theorem abs_sub_le_wordGap_add {w v : StoppingWord iota} {x y : ℝ}
    (hx : x ∈ S.stoppingWordMap w '' Set.Icc (0:ℝ) 1)
    (hy : y ∈ S.stoppingWordMap v '' Set.Icc (0:ℝ) 1) :
    |x - y| ≤ S.wordGap w v + S.stoppingRatio w + S.stoppingRatio v := by
  rw [S.stoppingWordMap_image_unitInterval] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hw0 : S.stoppingLeft w = (S.stoppingAnchor w : ℝ) := rfl
  have hv0 : S.stoppingLeft v = (S.stoppingAnchor v : ℝ) := rfl
  rw [hw0] at hx1 hx2
  rw [hv0] at hy1 hy2
  have hgap1 := le_max_left ((S.stoppingAnchor v : ℝ) - ((S.stoppingAnchor w : ℝ) + S.stoppingRatio w))
    ((S.stoppingAnchor w : ℝ) - ((S.stoppingAnchor v : ℝ) + S.stoppingRatio v))
  have hgap2 := le_max_right ((S.stoppingAnchor v : ℝ) - ((S.stoppingAnchor w : ℝ) + S.stoppingRatio w))
    ((S.stoppingAnchor w : ℝ) - ((S.stoppingAnchor v : ℝ) + S.stoppingRatio v))
  unfold wordGap
  rw [abs_le]
  constructor <;> linarith

end System

omit [Nonempty iota] in
/-- **`eq:stopping-brownian-overlap`.**  For two stopping cylinders of temporal length at
most `ρ = r²`, the expected overlap of their Brownian `r`-neighbourhoods is at most
`C ρ² / max(ρ, d)`, where `d` is the gap between their time intervals.  For `d ≤ ρ`
this is the area of one neighbourhood; for `d > ρ` the two centred images are
independent of the increment across the gap, whose planar Gaussian density is at most
`(2π d)⁻¹`. -/
theorem IsPlanarBrownian.integrable_and_integral_tubeOverlapArea_stoppingCylinders_le
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P) {K : Set ℝ} (hK : S.IsAttractor K)
    (w v : StoppingWord iota) {r : ℝ} (hr : 0 < r) (hlen : S.stoppingRatio w ≤ r ^ 2)
    (hlen' : S.stoppingRatio v ≤ r ^ 2)
    (hunit : Integrable (fun omega => (1 + standardBrownianRadius W omega) ^ (2:ℝ)) P) :
    Integrable (fun omega => tubeOverlapArea r
      (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
      (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega)) P ∧
    (∫ omega, tubeOverlapArea r
      (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
      (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega) ∂P)
      ≤ max (Real.pi * ∫ omega, (1 + standardBrownianRadius W omega) ^ (2:ℝ) ∂P)
          ((Real.pi * ∫ omega, (1 + standardBrownianRadius W omega) ^ (2:ℝ) ∂P) ^ 2 /
            (2 * Real.pi)) *
        (r ^ 2) ^ 2 / max (r ^ 2) (S.wordGap w v) := by
  set A : ℝ := Real.pi * ∫ omega, (1 + standardBrownianRadius W omega) ^ (2:ℝ) ∂P with hA
  set Cov : ℝ := max A (A ^ 2 / (2 * Real.pi)) with hCov
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg Real.pi_nonneg (integral_nonneg fun _ => Real.rpow_nonneg
      (add_nonneg zero_le_one (compactRadius_nonneg _)) _)
  have hACov : A ≤ Cov := le_max_left _ _
  have hA2Cov : A ^ 2 / (2 * Real.pi) ≤ Cov := le_max_right _ _
  have hCov0 : 0 ≤ Cov := hA0.trans hACov
  have hρ : 0 < r ^ 2 := by positivity
  obtain ⟨hintw, hboundw⟩ :=
    hW.integrable_and_integral_tubeArea_stoppingCylinder_le S hK w hr hlen hunit
  obtain ⟨hintv, hboundv⟩ :=
    hW.integrable_and_integral_tubeArea_stoppingCylinder_le S hK v hr hlen' hunit
  have hmeas : AEStronglyMeasurable (fun omega => tubeOverlapArea r
      (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
      (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega)) P :=
    ((measurable_tubeOverlapArea_pair hr).comp_aemeasurable
      ((hW.aemeasurable_brownianImage _).prodMk (hW.aemeasurable_brownianImage _))).aestronglyMeasurable
  -- the overlap is always dominated by the area of the first neighbourhood
  have hint : Integrable (fun omega => tubeOverlapArea r
      (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
      (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega)) P := by
    refine hintw.mono' hmeas (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_of_nonneg (tubeOverlapArea_nonneg _ _ _)]
    exact tubeOverlapArea_le_tubeArea_left _ _ _
  refine ⟨hint, ?_⟩
  by_cases hgap : S.wordGap w v ≤ r ^ 2
  · -- no gap: one neighbourhood
    rw [max_eq_left hgap]
    calc (∫ omega, tubeOverlapArea r
          (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
          (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega) ∂P)
        ≤ ∫ omega, tubeArea r (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega) ∂P :=
          integral_mono hint hintw fun omega => tubeOverlapArea_le_tubeArea_left _ _ _
      _ ≤ A * r ^ 2 := hboundw
      _ = A * (r ^ 2) ^ 2 / r ^ 2 := by field_simp
      _ ≤ Cov * (r ^ 2) ^ 2 / r ^ 2 := by gcongr
  · -- a positive gap: the Gaussian-gap estimate
    rw [not_le] at hgap
    have hgap0 : 0 < S.wordGap w v := hρ.trans hgap
    rw [max_eq_right hgap.le]
    -- the two orderings of the intervals
    have hkey : ∀ (w v : StoppingWord iota), S.stoppingRatio w ≤ r ^ 2 →
        S.stoppingRatio v ≤ r ^ 2 → 0 < S.wordGap w v →
        (S.stoppingAnchor v : ℝ) - ((S.stoppingAnchor w : ℝ) + S.stoppingRatio w)
          = S.wordGap w v →
        (∫ omega, tubeOverlapArea r
          (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
          (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega) ∂P)
          ≤ A ^ 2 / (2 * Real.pi) * (r ^ 2) ^ 2 / S.wordGap w v := by
      intro w v hlen hlen' hpos hord
      obtain ⟨hintw, hboundw⟩ :=
        hW.integrable_and_integral_tubeArea_stoppingCylinder_le S hK w hr hlen hunit
      obtain ⟨hintv, hboundv⟩ :=
        hW.integrable_and_integral_tubeArea_stoppingCylinder_le S hK v hr hlen' hunit
      rw [← hA] at hboundw hboundv
      set q : NNReal := ⟨S.wordGap w v, hpos.le⟩ with hqdef
      have hqcoe : (q : ℝ) = S.wordGap w v := rfl
      have hq : q ≠ 0 := by
        intro h
        have : (q : ℝ) = 0 := by rw [h]; rfl
        rw [hqcoe] at this
        exact hpos.ne' this
      have haqb : S.stoppingAnchor w + S.stoppingLength w + q = S.stoppingAnchor v := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, NNReal.coe_add, System.coe_stoppingLength, hqcoe]
        linarith
      have hpiecew : hK.stoppingCylinder S w.1 w.2 =
          affineTimeCompact (S.stoppingAnchor w) (S.stoppingLength w)
            (orientCompact (S.stoppingSign w) hK.toNonemptyCompacts) :=
        hK.stoppingCylinder_eq_affineTimeCompact S w
      have hpiecev : hK.stoppingCylinder S v.1 v.2 =
          affineTimeCompact (S.stoppingAnchor w + S.stoppingLength w + q) (S.stoppingLength v)
            (orientCompact (S.stoppingSign v) hK.toNonemptyCompacts) := by
        rw [haqb]
        exact hK.stoppingCylinder_eq_affineTimeCompact S v
      have hr2 : r ^ (2:ℝ) = r ^ 2 := Real.rpow_two r
      have hpair := hW.integrable_and_integral_tubeOverlapArea_affineCompactPieces_gap_le_rpow
        (S.stoppingAnchor w) (S.stoppingLength_ne_zero w) hq (S.stoppingLength_ne_zero v)
        (orientCompact (S.stoppingSign w) hK.toNonemptyCompacts)
        (orientCompact (S.stoppingSign v) hK.toNonemptyCompacts)
        (orientCompact_subset_Icc (S.stoppingSign_eq w) hK.2.2.1)
        (orientCompact_subset_Icc (S.stoppingSign_eq v) hK.2.2.1) (alpha := 2) (CA := A)
        (CB := A) hr
        (by simpa [affineBrownianCompactPiece, ← hpiecew] using hintw)
        (by simpa [affineBrownianCompactPiece, ← hpiecev] using hintv)
        (by rw [hr2]; simpa [affineBrownianCompactPiece, ← hpiecew] using hboundw)
        (by rw [hr2]; simpa [affineBrownianCompactPiece, ← hpiecev] using hboundv)
      have hconc := hpair.2
      simp only [affineBrownianCompactPiece, ← hpiecew, ← hpiecev] at hconc
      have hr4 : r ^ (2 * (2:ℝ)) = (r ^ 2) ^ 2 := by
        rw [show (2:ℝ) * 2 = ((4:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [hr4, hqcoe] at hconc
      refine hconc.trans (le_of_eq ?_)
      field_simp
    -- reduce to the ordered case
    have hmax : (S.stoppingAnchor v : ℝ) - ((S.stoppingAnchor w : ℝ) + S.stoppingRatio w)
        = S.wordGap w v ∨
        (S.stoppingAnchor w : ℝ) - ((S.stoppingAnchor v : ℝ) + S.stoppingRatio v)
          = S.wordGap w v := by
      unfold System.wordGap
      rcases le_total ((S.stoppingAnchor w : ℝ) - ((S.stoppingAnchor v : ℝ) + S.stoppingRatio v))
        ((S.stoppingAnchor v : ℝ) - ((S.stoppingAnchor w : ℝ) + S.stoppingRatio w)) with h | h
      · exact Or.inl (max_eq_left h).symm
      · exact Or.inr (max_eq_right h).symm
    have hfinal : (∫ omega, tubeOverlapArea r
        (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
        (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega) ∂P)
        ≤ A ^ 2 / (2 * Real.pi) * (r ^ 2) ^ 2 / S.wordGap w v := by
      rcases hmax with hord | hord
      · exact hkey w v hlen hlen' hgap0 hord
      · have hcomm : (∫ omega, tubeOverlapArea r
            (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega)
            (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega) ∂P)
            = ∫ omega, tubeOverlapArea r
              (brownianImage W (hK.stoppingCylinder S v.1 v.2) omega)
              (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun omega => tubeOverlapArea_comm _ _ _)
        rw [hcomm, S.wordGap_comm w v]
        rw [S.wordGap_comm w v] at hgap0 hord
        exact hkey v w hlen' hlen hgap0 hord
    refine hfinal.trans ?_
    have hr4 : 0 ≤ (r ^ 2) ^ 2 := by positivity
    gcongr

/-! ### Counting close pairs -/

namespace System

omit [Nonempty iota] in
/-- The Fubini form of the pair-distance mass of a product of two push-forwards. -/
theorem IsNatural.prod_map_apply_eq' {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {f g : ℝ → ℝ} (hf : Measurable f) (_hg : Measurable g) (h : ℝ) :
    ((μ.map f).prod (μ.map g)) {p : ℝ × ℝ | |p.1 - p.2| ≤ h}
      = ∫⁻ x, (μ.map g) (Metric.closedBall (f x) h) ∂μ := by
  have := hμ.isProbabilityMeasure
  rw [Measure.prod_apply (measurableSet_phiSet h)]
  simp only [mk_preimage_phiSet]
  exact lintegral_map (measurable_measure_closedBall _ h) hf

omit [Nonempty iota] in
/-- **The stopping words partition address space**, in the form the pair count uses:
below a node `w`, the weighted product of the two children `w·i` and `w·j` is the
double sum of the weighted products of the stopping cylinders below them, on the
pair-distance set. -/
theorem IsNatural.prod_map_pieces_eq_sum_leaves {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (w : StoppingWord iota) (i j : iota) (delta : ℝ) (n : ℕ)
    (h : ℝ) :
    ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
        ENNReal.ofReal (S.stoppingWeight s (stoppingChild w j)) *
        ((μ.map (S.stoppingWordMap (stoppingChild w i))).prod
          (μ.map (S.stoppingWordMap (stoppingChild w j)))) {p : ℝ × ℝ | |p.1 - p.2| ≤ h}
      = ∑ L : S.StoppingLeaves delta n (stoppingChild w i),
          ∑ L' : S.StoppingLeaves delta n (stoppingChild w j),
            ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta L)) *
              ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta L')) *
              ((μ.map (S.stoppingWordMap (S.stoppingLeafWord delta L))).prod
                (μ.map (S.stoppingWordMap (S.stoppingLeafWord delta L'))))
                  {p : ℝ × ℝ | |p.1 - p.2| ≤ h} := by
  have := hμ.isProbabilityMeasure
  -- the inner decomposition below the child `w·j`
  have hnode : ∀ y : ℝ, ENNReal.ofReal (S.stoppingWeight s (stoppingChild w j)) *
      (μ.map (S.stoppingWordMap (stoppingChild w j))) (Metric.closedBall y h)
      = ∑ L' : S.StoppingLeaves delta n (stoppingChild w j),
          ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta L')) *
            (μ.map (S.stoppingWordMap (S.stoppingLeafWord delta L'))) (Metric.closedBall y h) := by
    intro y
    have := hμ.measure_preimage_eq_sum_leaves S delta (A := Metric.closedBall y h)
      measurableSet_closedBall n (stoppingChild w j)
    rw [Measure.map_apply (S.measurable_stoppingWordMap _) measurableSet_closedBall, this]
    refine Finset.sum_congr rfl fun L' _ => ?_
    rw [Measure.map_apply (S.measurable_stoppingWordMap _) measurableSet_closedBall]
  set F : ℝ → ℝ≥0∞ := fun y => ∑ L' : S.StoppingLeaves delta n (stoppingChild w j),
    ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta L')) *
      (μ.map (S.stoppingWordMap (S.stoppingLeafWord delta L'))) (Metric.closedBall y h) with hF
  have hFmeas : Measurable F := by
    rw [hF]
    exact Finset.measurable_sum _ fun L' _ =>
      (measurable_measure_closedBall (μ.map _) h).const_mul _
  have hmeasL : ∀ (L : S.StoppingLeaves delta n (stoppingChild w i))
      (L' : S.StoppingLeaves delta n (stoppingChild w j)),
      Measurable fun x => (μ.map (S.stoppingWordMap (S.stoppingLeafWord delta L')))
        (Metric.closedBall (S.stoppingWordMap (S.stoppingLeafWord delta L) x) h) := fun L L' =>
    (measurable_measure_closedBall _ h).comp (S.measurable_stoppingWordMap _)
  have hmi : Measurable fun x => (μ.map (S.stoppingWordMap (stoppingChild w j)))
      (Metric.closedBall (S.stoppingWordMap (stoppingChild w i) x) h) :=
    (measurable_measure_closedBall _ h).comp (S.measurable_stoppingWordMap _)
  calc ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
        ENNReal.ofReal (S.stoppingWeight s (stoppingChild w j)) *
        ((μ.map (S.stoppingWordMap (stoppingChild w i))).prod
          (μ.map (S.stoppingWordMap (stoppingChild w j)))) {p : ℝ × ℝ | |p.1 - p.2| ≤ h}
      = ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
          ∫⁻ x, ENNReal.ofReal (S.stoppingWeight s (stoppingChild w j)) *
            (μ.map (S.stoppingWordMap (stoppingChild w j)))
              (Metric.closedBall (S.stoppingWordMap (stoppingChild w i) x) h) ∂μ := by
        rw [hμ.prod_map_apply_eq' S (S.measurable_stoppingWordMap _) (S.measurable_stoppingWordMap _),
          lintegral_const_mul _ hmi, mul_assoc]
    _ = ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
          ∫⁻ x, F (S.stoppingWordMap (stoppingChild w i) x) ∂μ := by
        congr 1
        exact lintegral_congr fun x => hnode _
    _ = ∑ L : S.StoppingLeaves delta n (stoppingChild w i),
          ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord delta L)) *
            ∫⁻ x, F (S.stoppingWordMap (S.stoppingLeafWord delta L) x) ∂μ :=
        hμ.lintegral_comp_eq_sum_leaves S delta hFmeas n (stoppingChild w i)
    _ = _ := by
        refine Finset.sum_congr rfl fun L _ => ?_
        rw [hF]
        dsimp only
        rw [lintegral_finsetSum _ fun L' _ => (hmeasL L L').const_mul _, Finset.mul_sum]
        refine Finset.sum_congr rfl fun L' _ => ?_
        rw [lintegral_const_mul _ (hmeasL L L'),
          hμ.prod_map_apply_eq' S (S.measurable_stoppingWordMap _) (S.measurable_stoppingWordMap _)]
        ring

omit [Nonempty iota] in
/-- The push-forward of the natural measure under the map of a word is carried by the
cylinder `S_w K`, and gives it full mass. -/
theorem IsNatural.map_apply_image_eq_one {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (w : StoppingWord iota) :
    (μ.map (S.stoppingWordMap w)) (S.stoppingWordMap w '' K) = 1 := by
  have := hμ.isProbabilityMeasure
  have hK : MeasurableSet (S.stoppingWordMap w '' K) :=
    (hμ.attractor.1.image (S.continuous_stoppingWordMap w)).isClosed.measurableSet
  refine le_antisymm prob_le_one ?_
  rw [Measure.map_apply (S.measurable_stoppingWordMap w) hK]
  calc (1 : ℝ≥0∞) = μ K := ((prob_compl_eq_zero_iff hμ.attractor.1.isClosed.measurableSet).mp
        hμ.support).symm
    _ ≤ μ (S.stoppingWordMap w ⁻¹' (S.stoppingWordMap w '' K)) :=
        measure_mono (Set.subset_preimage_image _ _)

omit [Nonempty iota] in
/-- **Close pairs have full product mass.**  If two stopping words of ratio at most
`ρ ≤ h` have gap at most `h`, every pair of points of their cylinders is at distance
at most `3h`, so the product of their push-forwards gives the pair-distance set full
mass. -/
theorem IsNatural.prod_map_close_eq_one {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {w v : StoppingWord iota} {ρ h : ℝ} (hρh : ρ ≤ h)
    (hw : S.stoppingRatio w ≤ ρ) (hv : S.stoppingRatio v ≤ ρ) (hgap : S.wordGap w v ≤ h) :
    ((μ.map (S.stoppingWordMap w)).prod (μ.map (S.stoppingWordMap v)))
      {p : ℝ × ℝ | |p.1 - p.2| ≤ 3 * h} = 1 := by
  have := hμ.isProbabilityMeasure
  refine le_antisymm prob_le_one ?_
  have hsub : (S.stoppingWordMap w '' K) ×ˢ (S.stoppingWordMap v '' K)
      ⊆ {p : ℝ × ℝ | |p.1 - p.2| ≤ 3 * h} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Set.mem_ofPred_eq]
    have hx' : x ∈ S.stoppingWordMap w '' Set.Icc (0:ℝ) 1 :=
      Set.image_mono hμ.attractor.2.2.1 hx
    have hy' : y ∈ S.stoppingWordMap v '' Set.Icc (0:ℝ) 1 :=
      Set.image_mono hμ.attractor.2.2.1 hy
    have := S.abs_sub_le_wordGap_add hx' hy'
    linarith
  calc (1 : ℝ≥0∞) = (μ.map (S.stoppingWordMap w)) (S.stoppingWordMap w '' K) *
        (μ.map (S.stoppingWordMap v)) (S.stoppingWordMap v '' K) := by
        rw [hμ.map_apply_image_eq_one, hμ.map_apply_image_eq_one, one_mul]
    _ = ((μ.map (S.stoppingWordMap w)).prod (μ.map (S.stoppingWordMap v)))
          ((S.stoppingWordMap w '' K) ×ˢ (S.stoppingWordMap v '' K)) :=
        (Measure.prod_prod _ _).symm
    _ ≤ _ := measure_mono hsub

/-- The leaves of the stopping tree below the child `w·i` of a node `w` with
`r_w ≥ δ`, at threshold `δ ≤ 1` and past the stopping depth, have ratios between
`r_min δ` and `δ`. -/
theorem stoppingLeafRatio_bounds_child {delta : ℝ} (hdelta0 : 0 < delta)
    {n : ℕ} (hn : Hutchinson.maxRatio S ^ n ≤ delta) {w : StoppingWord iota}
    (hw : delta ≤ S.stoppingRatio w) (i : iota)
    (leaf : S.StoppingLeaves delta n (stoppingChild w i)) :
    S.minRatio * delta ≤ S.stoppingRatio (S.stoppingLeafWord delta leaf) ∧
      S.stoppingRatio (S.stoppingLeafWord delta leaf) ≤ delta := by
  have hrw1 : S.stoppingRatio w ≤ 1 := by
    have h := S.generationRatio_le_maxRatio_pow w.1 w.2
    exact h.trans (pow_le_one₀ (Hutchinson.maxRatio_pos S).le (Hutchinson.maxRatio_lt_one S).le)
  constructor
  · have h := S.min_stoppingRatio_mul_delta_le_leafRatio S.minRatio_pos.le S.minRatio_le_one
      hdelta0.le S.minRatio_le leaf
    refine le_trans ?_ h
    rw [stoppingRatio_child]
    refine le_min ?_ le_rfl
    calc S.minRatio * delta ≤ S.ratio i * S.stoppingRatio w :=
          mul_le_mul (S.minRatio_le i) hw hdelta0.le (S.ratio_pos i).le
      _ = S.stoppingRatio w * S.ratio i := mul_comm _ _
  · refine S.stoppingLeafRatio_le_of_mul_maxRatio_pow_le delta n _ ?_ leaf
    rw [stoppingRatio_child]
    calc S.stoppingRatio w * S.ratio i * Hutchinson.maxRatio S ^ n ≤ 1 * 1 * delta :=
          mul_le_mul (mul_le_mul hrw1 (S.ratio_lt_one i).le (S.ratio_pos i).le zero_le_one) hn
            (pow_nonneg (Hutchinson.maxRatio_pos S).le _) (by norm_num)
      _ = delta := by ring

omit [Nonempty iota] in
/-- The pull-back of a ball centred in the image of a stopping word through the same
word is a ball of the rescaled radius. -/
theorem stoppingWordMap_preimage_closedBall_self (w : StoppingWord iota) (x h : ℝ) :
    S.stoppingWordMap w ⁻¹' Metric.closedBall (S.stoppingWordMap w x) h
      = Metric.closedBall x (h / S.stoppingRatio w) := by
  have hr : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  rw [preimage_closedBall_of_affine (S.stoppingWordMap_sub w)
    (S.stoppingSign_mul_stoppingRatio_ne_zero w), abs_mul, S.abs_stoppingSign, one_mul,
    abs_of_pos hr]

omit [Nonempty iota] in
/-- Composing two first-level pieces with the map of a word `w` rescales the
pair-distance set by `r_w`. -/
theorem IsNatural.prod_map_comp_apply {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (w : StoppingWord iota) (i j : iota) (h : ℝ) :
    ((μ.map (S.stoppingWordMap w ∘ S.map i)).prod (μ.map (S.stoppingWordMap w ∘ S.map j)))
        {p : ℝ × ℝ | |p.1 - p.2| ≤ h}
      = ((μ.map (S.map i)).prod (μ.map (S.map j)))
          {p : ℝ × ℝ | |p.1 - p.2| ≤ h / S.stoppingRatio w} := by
  have := hμ.isProbabilityMeasure
  rw [hμ.prod_map_apply_eq' S ((S.measurable_stoppingWordMap w).comp (S.measurable_map i))
    ((S.measurable_stoppingWordMap w).comp (S.measurable_map j)),
    hμ.prod_map_apply_eq' S (S.measurable_map i) (S.measurable_map j)]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply ((S.measurable_stoppingWordMap w).comp (S.measurable_map j))
    measurableSet_closedBall, Measure.map_apply (S.measurable_map j) measurableSet_closedBall,
    Set.preimage_comp, Function.comp_apply, S.stoppingWordMap_preimage_closedBall_self]

/-- **`eq:stopping-close-pairs`**, below a node `w` with `r_w ≥ ρ`.  Under the
cross-piece bound with exponent `η`, the number of pairs of stopping words below `w·i`
and below `w·j`, at threshold `ρ`, whose intervals are within distance `h ≥ ρ` of each
other satisfies `N (r_min ρ)^{2s} ≤ C 3^β r_w^{2s-β} h^β` with `β = s + η`: the pair
count is dominated by `p_{wi} p_{wj} (μ_{wi} × μ_{wj}){|x-y| ≤ 3h}`, and composing with
`S_w` rescales the distance by `r_w`. -/
theorem IsNatural.card_closePairs_le {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (hs0 : 0 < s) {i j : iota} (_hij : i ≠ j)
    {Cc η : ℝ} (_hCc : 0 < Cc) (hη : 0 ≤ η)
    (hcross : ∀ h' : ℝ, 0 < h' → h' ≤ 1 →
      ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ h'}
        ≤ ENNReal.ofReal (Cc * h' ^ (s + η)))
    {ρ : ℝ} (hρ0 : 0 < ρ) {n : ℕ} (hn : Hutchinson.maxRatio S ^ n ≤ ρ)
    {w : StoppingWord iota} (hw : ρ ≤ S.stoppingRatio w) {h : ℝ} (hρh : ρ ≤ h) :
    ((Finset.univ.filter fun p : S.StoppingLeaves ρ n (stoppingChild w i) ×
        S.StoppingLeaves ρ n (stoppingChild w j) =>
      S.wordGap (S.stoppingLeafWord ρ p.1) (S.stoppingLeafWord ρ p.2) ≤ h).card : ℝ) *
      (S.minRatio * ρ) ^ (2 * s)
      ≤ max Cc 1 * 3 ^ (s + η) * S.stoppingRatio w ^ (2 * s - (s + η)) * h ^ (s + η) := by
  classical
  have := hμ.isProbabilityMeasure
  have hh0 : 0 < h := hρ0.trans_le hρh
  have hrw : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have hrw1 : S.stoppingRatio w ≤ 1 := by
    have h := S.generationRatio_le_maxRatio_pow w.1 w.2
    exact h.trans (pow_le_one₀ (Hutchinson.maxRatio_pos S).le (Hutchinson.maxRatio_lt_one S).le)
  set T := Finset.univ.filter fun p : S.StoppingLeaves ρ n (stoppingChild w i) ×
      S.StoppingLeaves ρ n (stoppingChild w j) =>
    S.wordGap (S.stoppingLeafWord ρ p.1) (S.stoppingLeafWord ρ p.2) ≤ h with hT
  have hmr : 0 < S.minRatio * ρ := mul_pos S.minRatio_pos hρ0
  set q : ℝ := (S.minRatio * ρ) ^ s with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hmr.le s
  -- the weight of every leaf is at least `q`
  have hweight : ∀ (k : iota) (L : S.StoppingLeaves ρ n (stoppingChild w k)),
      q ≤ S.stoppingWeight s (S.stoppingLeafWord ρ L) := by
    intro k L
    rw [S.stoppingWeight_eq_ratio_rpow, hq]
    exact Real.rpow_le_rpow hmr.le (S.stoppingLeafRatio_bounds_child hρ0 hn hw k L).1 hs0.le
  -- the total, bounded by the rescaled cross-piece estimate
  set pw : ℝ := S.stoppingWeight s w with hpw
  have hpw0 : 0 ≤ pw := S.generationWeight_nonneg s w.1 w.2
  have hpwr : pw = S.stoppingRatio w ^ s := S.stoppingWeight_eq_ratio_rpow s w
  have htotal : ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
      ENNReal.ofReal (S.stoppingWeight s (stoppingChild w j)) *
      ((μ.map (S.stoppingWordMap (stoppingChild w i))).prod
        (μ.map (S.stoppingWordMap (stoppingChild w j)))) {p : ℝ × ℝ | |p.1 - p.2| ≤ 3 * h}
      ≤ ENNReal.ofReal (max Cc 1 * 3 ^ (s + η) * S.stoppingRatio w ^ (2 * s - (s + η)) *
          h ^ (s + η)) := by
    have hpi : ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) ≤ ENNReal.ofReal pw := by
      rw [stoppingWeight_child]
      refine ENNReal.ofReal_le_ofReal ?_
      exact mul_le_of_le_one_right hpw0 (S.tubeWeight_lt_one hs0 i).le
    have hpj : ENNReal.ofReal (S.stoppingWeight s (stoppingChild w j)) ≤ ENNReal.ofReal pw := by
      rw [stoppingWeight_child]
      refine ENNReal.ofReal_le_ofReal ?_
      exact mul_le_of_le_one_right hpw0 (S.tubeWeight_lt_one hs0 j).le
    have hmass : ((μ.map (S.stoppingWordMap (stoppingChild w i))).prod
        (μ.map (S.stoppingWordMap (stoppingChild w j)))) {p : ℝ × ℝ | |p.1 - p.2| ≤ 3 * h}
        ≤ ENNReal.ofReal (max Cc 1 * (3 * h / S.stoppingRatio w) ^ (s + η)) := by
      rw [stoppingWordMap_child, stoppingWordMap_child, hμ.prod_map_comp_apply S w i j (3 * h)]
      have h3pos : 0 < 3 * h / S.stoppingRatio w := by positivity
      by_cases h3 : 3 * h / S.stoppingRatio w ≤ 1
      · refine (hcross _ h3pos h3).trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h3pos.le _)
      · rw [not_le] at h3
        calc ((μ.map (S.map i)).prod (μ.map (S.map j)))
              {p : ℝ × ℝ | |p.1 - p.2| ≤ 3 * h / S.stoppingRatio w} ≤ 1 := prob_le_one
          _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal (max Cc 1 * (3 * h / S.stoppingRatio w) ^ (s + η)) := by
              refine ENNReal.ofReal_le_ofReal ?_
              calc (1:ℝ) = 1 * 1 := (mul_one 1).symm
                _ ≤ max Cc 1 * (3 * h / S.stoppingRatio w) ^ (s + η) :=
                    mul_le_mul (le_max_right _ _) (Real.one_le_rpow h3.le (by linarith))
                      zero_le_one (le_trans zero_le_one (le_max_right _ _))
    calc ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
          ENNReal.ofReal (S.stoppingWeight s (stoppingChild w j)) *
          ((μ.map (S.stoppingWordMap (stoppingChild w i))).prod
            (μ.map (S.stoppingWordMap (stoppingChild w j)))) {p : ℝ × ℝ | |p.1 - p.2| ≤ 3 * h}
        ≤ ENNReal.ofReal pw * ENNReal.ofReal pw *
          ENNReal.ofReal (max Cc 1 * (3 * h / S.stoppingRatio w) ^ (s + η)) := by gcongr
      _ = ENNReal.ofReal (pw * pw * (max Cc 1 * (3 * h / S.stoppingRatio w) ^ (s + η))) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hpw0 hpw0), ENNReal.ofReal_mul hpw0]
      _ = ENNReal.ofReal (max Cc 1 * 3 ^ (s + η) * S.stoppingRatio w ^ (2 * s - (s + η)) *
            h ^ (s + η)) := by
          congr 1
          rw [hpwr, ← Real.rpow_add hrw, Real.div_rpow (by positivity) hrw.le,
            Real.mul_rpow (by norm_num) hh0.le, Real.rpow_sub hrw, ← two_mul]
          field_simp
  -- the close pairs contribute at least `q²` each
  set f : S.StoppingLeaves ρ n (stoppingChild w i) ×
      S.StoppingLeaves ρ n (stoppingChild w j) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord ρ p.1)) *
      ENNReal.ofReal (S.stoppingWeight s (S.stoppingLeafWord ρ p.2)) *
      ((μ.map (S.stoppingWordMap (S.stoppingLeafWord ρ p.1))).prod
        (μ.map (S.stoppingWordMap (S.stoppingLeafWord ρ p.2))))
          {x : ℝ × ℝ | |x.1 - x.2| ≤ 3 * h} with hf
  have hterm : ∀ p ∈ T, ENNReal.ofReal q * ENNReal.ofReal q ≤ f p := by
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    rw [hf]
    dsimp only
    rw [hμ.prod_map_close_eq_one S hρh (S.stoppingLeafRatio_bounds_child hρ0 hn hw i p.1).2
      (S.stoppingLeafRatio_bounds_child hρ0 hn hw j p.2).2 hp.2, mul_one]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hweight i p.1))
      (ENNReal.ofReal_le_ofReal (hweight j p.2))
  have hsum : ∑ p, f p = ENNReal.ofReal (S.stoppingWeight s (stoppingChild w i)) *
      ENNReal.ofReal (S.stoppingWeight s (stoppingChild w j)) *
      ((μ.map (S.stoppingWordMap (stoppingChild w i))).prod
        (μ.map (S.stoppingWordMap (stoppingChild w j)))) {p : ℝ × ℝ | |p.1 - p.2| ≤ 3 * h} := by
    rw [hμ.prod_map_pieces_eq_sum_leaves S w i j ρ n (3 * h), Fintype.sum_prod_type]
  have hclose : (T.card : ℝ≥0∞) * (ENNReal.ofReal q * ENNReal.ofReal q) ≤ ∑ p, f p := by
    calc (T.card : ℝ≥0∞) * (ENNReal.ofReal q * ENNReal.ofReal q)
        = ∑ _p ∈ T, ENNReal.ofReal q * ENNReal.ofReal q := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ T, f p := Finset.sum_le_sum hterm
      _ ≤ ∑ p, f p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) fun _ _ _ => zero_le
  have hfinal : (T.card : ℝ≥0∞) * (ENNReal.ofReal q * ENNReal.ofReal q)
      ≤ ENNReal.ofReal (max Cc 1 * 3 ^ (s + η) * S.stoppingRatio w ^ (2 * s - (s + η)) *
          h ^ (s + η)) := hclose.trans (hsum ▸ htotal)
  have hcast : (T.card : ℝ≥0∞) * (ENNReal.ofReal q * ENNReal.ofReal q)
      = ENNReal.ofReal ((T.card : ℝ) * (q * q)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_mul hq0]
  rw [hcast] at hfinal
  have hrhs : 0 ≤ max Cc 1 * 3 ^ (s + η) * S.stoppingRatio w ^ (2 * s - (s + η)) * h ^ (s + η) := by
    have h1 : 0 ≤ max Cc 1 := le_trans zero_le_one (le_max_right _ _)
    have h2 : (0:ℝ) ≤ 3 ^ (s + η) := Real.rpow_nonneg (by norm_num) _
    have h3 : 0 ≤ S.stoppingRatio w ^ (2 * s - (s + η)) := Real.rpow_nonneg hrw.le _
    have h4 : 0 ≤ h ^ (s + η) := Real.rpow_nonneg hh0.le _
    positivity
  have hreal : (T.card : ℝ) * (q * q)
      ≤ max Cc 1 * 3 ^ (s + η) * S.stoppingRatio w ^ (2 * s - (s + η)) * h ^ (s + η) :=
    (ENNReal.ofReal_le_ofReal_iff hrhs).mp hfinal
  have hqq : q * q = (S.minRatio * ρ) ^ (2 * s) := by
    rw [hq, ← Real.rpow_add hmr, two_mul]
  rw [hqq] at hreal
  exact hreal

/-! ### `thm:neighbourhood-overlap` -/

omit [MeasurableSpace Omega] in
omit [Nonempty iota] in
/-- On a continuous path, the Brownian image of a stopping cylinder is covered by the
Brownian images of the stopping cylinders below it. -/
theorem IsAttractor.brownianImage_stoppingCylinder_subset_iUnion {K : Set ℝ}
    (hK : S.IsAttractor K) (delta : ℝ) (n : ℕ) (w : StoppingWord iota) {omega : Omega}
    (homega : Continuous fun t => W t omega) :
    (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega : Set Plane) ⊆
      ⋃ L : S.StoppingLeaves delta n w,
        (brownianImage W (hK.stoppingCylinder S (S.stoppingLeafWord delta L).1
          (S.stoppingLeafWord delta L).2) omega : Set Plane) := by
  rw [coe_brownianImage_of_continuous _ homega]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨L, hL⟩ := hK.exists_stoppingLeaf_mem S delta n w ht
  refine Set.mem_iUnion.mpr ⟨L, ?_⟩
  rw [coe_brownianImage_of_continuous _ homega]
  exact ⟨t, hL, rfl⟩

omit [Nonempty iota] in
/-- The cylinder of a first-level child of the root is the first-level piece. -/
theorem IsNatural.stoppingCylinder_child_root {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (i : iota) :
    hμ.attractor.stoppingCylinder S (stoppingChild stoppingRoot i).1
      (stoppingChild stoppingRoot i).2 = hμ.compactPiece S i := by
  apply NonemptyCompacts.ext
  rw [IsAttractor.coe_stoppingCylinder, IsNatural.coe_compactPiece]
  rfl

omit [Nonempty iota] in
/-- A set invariant under every map of the system is invariant under every prefix map. -/
theorem mapsTo_stoppingMap {V : Set ℝ} (hV : ∀ i, Set.MapsTo (S.map i) V V) :
    ∀ (k : ℕ) (w : GenerationWord iota k), Set.MapsTo (S.stoppingMap k w) V V
  | 0, _ => Set.mapsTo_id V
  | Nat.succ k, w => (mapsTo_stoppingMap hV k w.1).comp (hV w.2)

omit [Nonempty iota] in
/-- Every stopping cylinder lies in the attractor. -/
theorem IsAttractor.stoppingCylinder_subset {K : Set ℝ} (hK : S.IsAttractor K)
    (w : StoppingWord iota) : (hK.stoppingCylinder S w.1 w.2 : Set ℝ) ⊆ K := by
  rw [IsAttractor.coe_stoppingCylinder]
  exact (S.mapsTo_stoppingMap (fun i => hK.mapsTo_map S i) w.1 w.2).image_subset

set_option maxHeartbeats 800000 in
/-- **`thm:neighbourhood-overlap` below a node.**  Under the strong open set condition
there are `C > 0` and `η > 0` such that, for every word `w`, every `0 < r ≤ 1` with
`r² ≤ r_w`, and all distinct `i, j`, the expected overlap of the Brownian
`r`-neighbourhoods of `S_w S_i K` and `S_w S_j K` is at most `C r_w^{s-η} r^{α+2η}`:
the overlap is summed over the stopping cylinders at temporal scale `r²` below the two
children, grouped dyadically by their gap. -/
theorem IsNatural.exists_pairwise_tubeOverlap_node_of_sosc [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hupper : ∃ A₁ : ℝ, 0 < A₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Integrable (fun omega => tubeArea ρ (brownianImage W hμ.compactAttractor omega)) P ∧
      (∫ omega, tubeArea ρ (brownianImage W hμ.compactAttractor omega) ∂P)
        ≤ A₁ * ρ ^ tubeExponent s) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 - s ∧ ∀ (w : StoppingWord iota) (r : ℝ), 0 < r → r ≤ 1 →
      r ^ 2 ≤ S.stoppingRatio w → ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r
        (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
          (stoppingChild w i).2) omega)
        (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w j).1
          (stoppingChild w j).2) omega)) P ∧
      (∫ omega, tubeOverlapArea r
        (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
          (stoppingChild w i).2) omega)
        (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w j).1
          (stoppingChild w j).2) omega) ∂P)
        ≤ C * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η) := by
  classical
  obtain ⟨Cc, η, hCc, hη, hηs, hcross⟩ := hsosc.exists_cross_piece_bound S hs0 hs1 hdim hμ
  obtain ⟨A₁, hA₁, hupper⟩ := hupper
  have hunit : Integrable (fun omega => (1 + standardBrownianRadius W omega) ^ (2:ℝ)) P :=
    hW.integrable_one_add_standardBrownianRadius_rpow (by norm_num)
  set A : ℝ := Real.pi * ∫ omega, (1 + standardBrownianRadius W omega) ^ (2:ℝ) ∂P with hA
  set Cov : ℝ := max A (A ^ 2 / (2 * Real.pi)) with hCov
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg Real.pi_nonneg (integral_nonneg fun _ => Real.rpow_nonneg
      (add_nonneg zero_le_one (compactRadius_nonneg _)) _)
  have hCov0 : 0 ≤ Cov := hA0.trans (le_max_left _ _)
  have hrmin := S.minRatio_pos
  set β : ℝ := s + η with hβ
  have hβ1 : β < 1 := by rw [hβ]; linarith
  have hβ0 : 0 < β := by rw [hβ]; linarith
  set q2 : ℝ := (2:ℝ) ^ (β - 1) with hq2
  have hq2lt : q2 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq2' : 0 < 1 - q2 := by linarith
  set C₁ : ℝ := 2 * Cov * (max Cc 1 * 3 ^ β * S.minRatio ^ (-(2 * s))) / (1 - q2) with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    have h1 : 0 ≤ max Cc 1 := le_trans zero_le_one (le_max_right _ _)
    have h2 : 0 ≤ (3:ℝ) ^ β := Real.rpow_nonneg (by norm_num) _
    have h3 : 0 ≤ S.minRatio ^ (-(2 * s)) := Real.rpow_nonneg hrmin.le _
    positivity
  refine ⟨C₁ + 1, η, by linarith, hη, hηs, fun w r hr hr1 hrw i j hij => ?_⟩
  have hrw0 : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have hexp : 0 ≤ S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η) :=
    mul_nonneg (Real.rpow_nonneg hrw0.le _) (Real.rpow_nonneg hr.le _)
  obtain ⟨hintK, -⟩ := hupper r hr hr1
  -- the overlap is dominated by the neighbourhood area of the whole image
  have hdom : ∀ᵐ omega ∂P, tubeOverlapArea r
      (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
        (stoppingChild w i).2) omega)
      (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w j).1
        (stoppingChild w j).2) omega)
      ≤ tubeArea r (brownianImage W hμ.compactAttractor omega) := by
    filter_upwards [hW.ae_continuous] with omega homega
    refine (tubeOverlapArea_le_tubeArea_left _ _ _).trans (tubeArea_mono ?_)
    rw [coe_brownianImage_of_continuous _ homega, coe_brownianImage_of_continuous _ homega]
    exact Set.image_mono (hμ.attractor.stoppingCylinder_subset S _)
  have hmeas : AEStronglyMeasurable (fun omega => tubeOverlapArea r
      (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
        (stoppingChild w i).2) omega)
      (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w j).1
        (stoppingChild w j).2) omega)) P :=
    ((measurable_tubeOverlapArea_pair hr).comp_aemeasurable
      ((hW.aemeasurable_brownianImage _).prodMk
        (hW.aemeasurable_brownianImage _))).aestronglyMeasurable
  have hint : Integrable (fun omega => tubeOverlapArea r
      (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
        (stoppingChild w i).2) omega)
      (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w j).1
        (stoppingChild w j).2) omega)) P := by
    refine hintK.mono' hmeas ?_
    filter_upwards [hdom] with omega h
    rw [Real.norm_of_nonneg (tubeOverlapArea_nonneg _ _ _)]
    exact h
  refine ⟨hint, ?_⟩
  -- the stopping cylinders at temporal scale `ρ = r²`
  set ρ : ℝ := r ^ 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ]; exact pow_le_one₀ hr.le hr1
  obtain ⟨n, hn⟩ := S.exists_stoppingDepth hρ0
  -- coverage by the cylinders
  have hcov : ∀ᵐ omega ∂P, tubeOverlapArea r
      (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
        (stoppingChild w i).2) omega)
      (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w j).1
        (stoppingChild w j).2) omega)
      ≤ ∑ L : S.StoppingLeaves ρ n (stoppingChild w i),
        ∑ L' : S.StoppingLeaves ρ n (stoppingChild w j),
          tubeOverlapArea r
            (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L).1
              (S.stoppingLeafWord ρ L).2) omega)
            (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L').1
              (S.stoppingLeafWord ρ L').2) omega) := by
    filter_upwards [hW.ae_continuous] with omega homega
    exact tubeOverlapArea_le_sum_of_subset_iUnion r _ _ _ _
      (hμ.attractor.brownianImage_stoppingCylinder_subset_iUnion S ρ n _ homega)
      (hμ.attractor.brownianImage_stoppingCylinder_subset_iUnion S ρ n _ homega)
  -- the pair bound
  have hpair : ∀ (L : S.StoppingLeaves ρ n (stoppingChild w i))
      (L' : S.StoppingLeaves ρ n (stoppingChild w j)),
      Integrable (fun omega => tubeOverlapArea r
        (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L).1
          (S.stoppingLeafWord ρ L).2) omega)
        (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L').1
          (S.stoppingLeafWord ρ L').2) omega)) P ∧
      (∫ omega, tubeOverlapArea r
        (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L).1
          (S.stoppingLeafWord ρ L).2) omega)
        (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L').1
          (S.stoppingLeafWord ρ L').2) omega) ∂P)
        ≤ Cov * ρ ^ 2 / max ρ (S.wordGap (S.stoppingLeafWord ρ L) (S.stoppingLeafWord ρ L')) :=
    fun L L' => hW.integrable_and_integral_tubeOverlapArea_stoppingCylinders_le S hμ.attractor
      _ _ hr (S.stoppingLeafRatio_bounds_child hρ0 hn hrw i L).2
      (S.stoppingLeafRatio_bounds_child hρ0 hn hrw j L').2 hunit
  -- the count of close pairs
  set d : S.StoppingLeaves ρ n (stoppingChild w i) ×
      S.StoppingLeaves ρ n (stoppingChild w j) → ℝ := fun p =>
    S.wordGap (S.stoppingLeafWord ρ p.1) (S.stoppingLeafWord ρ p.2) with hd
  set N₀ : ℝ := max Cc 1 * 3 ^ β * S.stoppingRatio w ^ (2 * s - β) *
    (S.minRatio * ρ) ^ (-(2 * s)) with hN₀
  have hN₀0 : 0 ≤ N₀ := by
    rw [hN₀]
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hrw0.le _))
      (Real.rpow_nonneg (by positivity) _)
  have hcount : ∀ h : ℝ, ρ ≤ h →
      ((Finset.univ.filter fun p => d p ≤ h).card : ℝ) ≤ N₀ * h ^ β := by
    intro h hρh
    have hc := hμ.card_closePairs_le S hs0 hij hCc hη.le (fun h' h'0 h'1 =>
      (hcross i j hij h' h'0 h'1).2) hρ0 hn hrw hρh
    have hpos : 0 < (S.minRatio * ρ) ^ (2 * s) := Real.rpow_pos_of_pos (by positivity) _
    calc ((Finset.univ.filter fun p => d p ≤ h).card : ℝ)
        = ((Finset.univ.filter fun p => d p ≤ h).card : ℝ) * (S.minRatio * ρ) ^ (2 * s) /
            (S.minRatio * ρ) ^ (2 * s) := by
          field_simp
      _ ≤ max Cc 1 * 3 ^ (s + η) * S.stoppingRatio w ^ (2 * s - (s + η)) * h ^ (s + η) /
            (S.minRatio * ρ) ^ (2 * s) :=
          div_le_div_of_nonneg_right hc hpos.le
      _ = N₀ * h ^ β := by
          rw [hN₀, Real.rpow_neg (by positivity : (0:ℝ) ≤ S.minRatio * ρ), hβ]
          field_simp
  have hd1 : ∀ p, d p ≤ 1 := fun p => S.wordGap_le_one _ _
  -- integrability of the cylinder sum
  have hintsum : Integrable (fun omega =>
      ∑ L : S.StoppingLeaves ρ n (stoppingChild w i),
        ∑ L' : S.StoppingLeaves ρ n (stoppingChild w j),
          tubeOverlapArea r
            (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L).1
              (S.stoppingLeafWord ρ L).2) omega)
            (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L').1
              (S.stoppingLeafWord ρ L').2) omega)) P :=
    integrable_finsetSum _ fun L _ => integrable_finsetSum _ fun L' _ => (hpair L L').1
  -- the power identity `ρ^{1+β-2s} = r^{α+2η}`
  have hpow : ρ ^ (1 + β - 2 * s) = r ^ (tubeExponent s + 2 * η) := by
    rw [hρ, ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, hβ, tubeExponent]
    congr 1
    push_cast
    ring
  calc (∫ omega, tubeOverlapArea r
        (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
          (stoppingChild w i).2) omega)
        (brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w j).1
          (stoppingChild w j).2) omega) ∂P)
      ≤ ∫ omega, ∑ L : S.StoppingLeaves ρ n (stoppingChild w i),
          ∑ L' : S.StoppingLeaves ρ n (stoppingChild w j),
            tubeOverlapArea r
              (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L).1
                (S.stoppingLeafWord ρ L).2) omega)
              (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L').1
                (S.stoppingLeafWord ρ L').2) omega) ∂P :=
        integral_mono_ae hint hintsum hcov
    _ = ∑ L : S.StoppingLeaves ρ n (stoppingChild w i),
          ∑ L' : S.StoppingLeaves ρ n (stoppingChild w j),
            ∫ omega, tubeOverlapArea r
              (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L).1
                (S.stoppingLeafWord ρ L).2) omega)
              (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord ρ L').1
                (S.stoppingLeafWord ρ L').2) omega) ∂P := by
        rw [integral_finsetSum _ fun L _ => integrable_finsetSum _ fun L' _ => (hpair L L').1]
        exact Finset.sum_congr rfl fun L _ =>
          integral_finsetSum _ fun L' _ => (hpair L L').1
    _ ≤ ∑ L : S.StoppingLeaves ρ n (stoppingChild w i),
          ∑ L' : S.StoppingLeaves ρ n (stoppingChild w j),
            Cov * ρ ^ 2 / max ρ (d (L, L')) :=
        Finset.sum_le_sum fun L _ => Finset.sum_le_sum fun L' _ => (hpair L L').2
    _ = ∑ p, Cov * ρ ^ 2 / max ρ (d p) :=
        (Fintype.sum_prod_type (fun p => Cov * ρ ^ 2 / max ρ (d p))).symm
    _ ≤ 2 * Cov * N₀ * ρ ^ (1 + β) / (1 - q2) :=
        sum_dyadic_le d hρ0 hCov0 hN₀0 hβ1 hd1 hcount
    _ = C₁ * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η) := by
        have hsplit : (S.minRatio * ρ) ^ (-(2 * s))
            = S.minRatio ^ (-(2 * s)) * ρ ^ (-(2 * s)) := Real.mul_rpow hrmin.le hρ0.le
        have hρpow : ρ ^ (-(2 * s)) * ρ ^ (1 + β) = ρ ^ (1 + β - 2 * s) := by
          rw [← Real.rpow_add hρ0]
          congr 1
          ring
        have hrwexp : S.stoppingRatio w ^ (2 * s - β) = S.stoppingRatio w ^ (s - η) := by
          congr 1
          rw [hβ]
          ring
        rw [← hpow, hC₁, hN₀, hsplit, hrwexp]
        calc 2 * Cov * (max Cc 1 * 3 ^ β * S.stoppingRatio w ^ (s - η) *
              (S.minRatio ^ (-(2 * s)) * ρ ^ (-(2 * s)))) * ρ ^ (1 + β) / (1 - q2)
            = 2 * Cov * (max Cc 1 * 3 ^ β * S.minRatio ^ (-(2 * s))) / (1 - q2) *
                S.stoppingRatio w ^ (s - η) * (ρ ^ (-(2 * s)) * ρ ^ (1 + β)) := by ring
          _ = _ := by rw [hρpow]
    _ ≤ (C₁ + 1) * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith) hexp

/-- **`eq:neighbourhood-defect-mean` below a node.**  Under the strong open set condition
there are `C > 0` and `η > 0` such that, for every word `w` and every `0 < r ≤ 1` with
`r² ≤ r_w`, the expected multiple-counting defect of the Brownian `r`-neighbourhoods of
the children `S_w S_i K` is at most `C r_w^{s-η} r^{α+2η}`. -/
theorem IsNatural.exists_tubeDefect_node_of_sosc [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hupper : ∃ A₁ : ℝ, 0 < A₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Integrable (fun omega => tubeArea ρ (brownianImage W hμ.compactAttractor omega)) P ∧
      (∫ omega, tubeArea ρ (brownianImage W hμ.compactAttractor omega) ∂P)
        ≤ A₁ * ρ ^ tubeExponent s) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 - s ∧ ∀ (w : StoppingWord iota) (r : ℝ), 0 < r → r ≤ 1 →
      r ^ 2 ≤ S.stoppingRatio w →
      Integrable (fun omega => tubeDefect r (fun i =>
        brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
          (stoppingChild w i).2) omega)) P ∧
      (∫ omega, tubeDefect r (fun i =>
        brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
          (stoppingChild w i).2) omega) ∂P)
        ≤ C * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η) := by
  obtain ⟨C₀, η, hC₀, hη, hηs, hnode⟩ :=
    hμ.exists_pairwise_tubeOverlap_node_of_sosc S hW hs0 hs1 hsosc hdim hupper
  have hcard : (0:ℝ) < (Fintype.card iota : ℝ) ^ 2 / 2 := by
    have : (1:ℝ) ≤ Fintype.card iota := by exact_mod_cast Fintype.card_pos
    positivity
  refine ⟨(Fintype.card iota : ℝ) ^ 2 / 2 * C₀, η, mul_pos hcard hC₀, hη, hηs,
    fun w r hr hr1 hrw => ?_⟩
  have hF : ∀ i, AEMeasurable (fun omega => brownianImage W
      (hμ.attractor.stoppingCylinder S (stoppingChild w i).1 (stoppingChild w i).2) omega) P :=
    fun i => hW.aemeasurable_brownianImage _
  have hoverlap := fun i j hij => (hnode w r hr hr1 hrw i j hij).1
  have hB : 0 ≤ C₀ * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η) :=
    mul_nonneg (mul_nonneg hC₀.le (Real.rpow_nonneg (S.generationRatio_pos w.1 w.2).le _))
      (Real.rpow_nonneg hr.le _)
  refine ⟨integrable_tubeDefect_of_pairwise_overlap hr hF hoverlap, ?_⟩
  calc _ ≤ (Fintype.card iota : ℝ) ^ 2 / 2 *
        (C₀ * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η)) :=
        integral_tubeDefect_le_card_sq_mul hr hB hF hoverlap
          fun i j hij => (hnode w r hr hr1 hrw i j hij).2
    _ = _ := by ring

/-- **`thm:neighbourhood-overlap`, the pairwise bound.**  Under the strong open set
condition there are `C > 0` and `η > 0` such that, for all distinct `i, j` and
`0 < r ≤ 1`, the expected overlap of the Brownian `r`-neighbourhoods of `S_i K` and
`S_j K` is at most `C r^{α+2η}`, where `α = 2 - 2s`. -/
theorem IsNatural.exists_pairwise_tubeOverlap_of_sosc [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hupper : ∃ A₁ : ℝ, 0 < A₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Integrable (fun omega => tubeArea ρ (brownianImage W hμ.compactAttractor omega)) P ∧
      (∫ omega, tubeArea ρ (brownianImage W hμ.compactAttractor omega) ∂P)
        ≤ A₁ * ρ ^ tubeExponent s) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r
        (brownianImage W (hμ.compactPiece S i) omega)
        (brownianImage W (hμ.compactPiece S j) omega)) P ∧
      (∫ omega, tubeOverlapArea r
        (brownianImage W (hμ.compactPiece S i) omega)
        (brownianImage W (hμ.compactPiece S j) omega) ∂P)
        ≤ C * r ^ (tubeExponent s + 2 * η) := by
  obtain ⟨C, η, hC, hη, -, hnode⟩ :=
    hμ.exists_pairwise_tubeOverlap_node_of_sosc S hW hs0 hs1 hsosc hdim hupper
  refine ⟨C, η, hC, hη, fun r hr hr1 i j hij => ?_⟩
  have h := hnode stoppingRoot r hr hr1 (by rw [stoppingRatio_root]; exact pow_le_one₀ hr.le hr1)
    i j hij
  rw [hμ.stoppingCylinder_child_root, hμ.stoppingCylinder_child_root, stoppingRatio_root,
    Real.one_rpow, mul_one] at h
  exact h

/-- **`thm:neighbourhood-overlap`**, under the strong open set condition: one constant
and one exponent `η > 0` control every distinct first-level pair and the resulting
multiple-counting defect, with the bound `C r^{α+2η}`. -/
theorem IsNatural.tubeOverlap_of_sosc [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hupper : ∃ A₁ : ℝ, 0 < A₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Integrable (fun omega => tubeArea ρ (brownianImage W hμ.compactAttractor omega)) P ∧
      (∫ omega, tubeArea ρ (brownianImage W hμ.compactAttractor omega) ∂P)
        ≤ A₁ * ρ ^ tubeExponent s) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r
          (brownianImage W (hμ.compactPiece S i) omega)
          (brownianImage W (hμ.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea r
          (brownianImage W (hμ.compactPiece S i) omega)
          (brownianImage W (hμ.compactPiece S j) omega) ∂P)
          ≤ C * r ^ (tubeExponent s + 2 * η)) ∧
      Integrable (fun omega => tubeDefect r
        (fun i => brownianImage W (hμ.compactPiece S i) omega)) P ∧
      (∫ omega, tubeDefect r
        (fun i => brownianImage W (hμ.compactPiece S i) omega) ∂P)
        ≤ C * r ^ (tubeExponent s + 2 * η) := by
  obtain ⟨C₀, η, hC₀, hη, hpair⟩ :=
    hμ.exists_pairwise_tubeOverlap_of_sosc S hW hs0 hs1 hsosc hdim hupper
  obtain ⟨C, hC, hall⟩ := exists_pairwise_overlap_and_defect_bound
    (F := fun i omega => brownianImage W (hμ.compactPiece S i) omega)
    (fun i => hW.aemeasurable_brownianImage _)
    (scale := fun r => r ^ (tubeExponent s + 2 * η))
    (fun r hr _ => Real.rpow_nonneg hr.le _)
    ⟨C₀, hC₀, fun r hr hr1 i j hij => hpair r hr hr1 i j hij⟩
  exact ⟨C, η, hC, hη, hall⟩

omit [Nonempty iota] in
/-- The `q = 1` case of `thm:neighbourhood-moments`, in the shape the overlap bound
consumes: the expected area of the `ρ`-neighbourhood of `BM(K)` is `O(ρ^α)`. -/
theorem IsNatural.exists_tubeArea_mean_bound_of_tubeMoments {K : Set ℝ} {s : ℝ}
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hmom : ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable (fun omega => (brownianTubeArea W hμ.compactAttractor r omega) ^ q) P ∧
      Integrable (fun omega => (tubeMass r (brownianImage W hμ.compactAttractor omega)) ^ q) P ∧
      (∫ omega, (brownianTubeArea W hμ.compactAttractor r omega) ^ q ∂P) +
        (∫ omega, (tubeMass r (brownianImage W hμ.compactAttractor omega)) ^ q ∂P)
          ≤ Cq * r ^ (q * tubeExponent s)) :
    ∃ A₁ : ℝ, 0 < A₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Integrable (fun omega => tubeArea ρ (brownianImage W hμ.compactAttractor omega)) P ∧
      (∫ omega, tubeArea ρ (brownianImage W hμ.compactAttractor omega) ∂P)
        ≤ A₁ * ρ ^ tubeExponent s := by
  obtain ⟨A₁, hA₁, h1⟩ := hmom 1 le_rfl
  refine ⟨A₁, hA₁, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨harea, -, hsum⟩ := h1 ρ hρ hρ1
  simp only [Real.rpow_one, one_mul, brownianTubeArea] at harea hsum
  exact ⟨harea, le_trans (le_add_of_nonneg_right (integral_nonneg fun _ =>
    tubeMass_nonneg _ _)) hsum⟩

/-- **`thm:neighbourhood-overlap`** under the strong open set condition, from the
moment bounds of `thm:neighbourhood-moments`. -/
theorem IsNatural.tubeOverlap_of_sosc_of_tubeMoments [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hmom : ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable (fun omega => (brownianTubeArea W hμ.compactAttractor r omega) ^ q) P ∧
      Integrable (fun omega => (tubeMass r (brownianImage W hμ.compactAttractor omega)) ^ q) P ∧
      (∫ omega, (brownianTubeArea W hμ.compactAttractor r omega) ^ q ∂P) +
        (∫ omega, (tubeMass r (brownianImage W hμ.compactAttractor omega)) ^ q ∂P)
          ≤ Cq * r ^ (q * tubeExponent s)) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r
          (brownianImage W (hμ.compactPiece S i) omega)
          (brownianImage W (hμ.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea r
          (brownianImage W (hμ.compactPiece S i) omega)
          (brownianImage W (hμ.compactPiece S j) omega) ∂P)
          ≤ C * r ^ (tubeExponent s + 2 * η)) ∧
      Integrable (fun omega => tubeDefect r
        (fun i => brownianImage W (hμ.compactPiece S i) omega)) P ∧
      (∫ omega, tubeDefect r
        (fun i => brownianImage W (hμ.compactPiece S i) omega) ∂P)
        ≤ C * r ^ (tubeExponent s + 2 * η) :=
  hμ.tubeOverlap_of_sosc S hW hs0 hs1 hsosc hdim
    (hμ.exists_tubeArea_mean_bound_of_tubeMoments S hmom)

end System

end

end BrownianImages
