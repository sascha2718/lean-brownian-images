/-
`sec:variance` of `BrownianImagesComplete.tex`: the dyadic block of ordered quadruples.

`thm:endpoint-block-mass` has two halves.  The mass half is
`endpoint_block_mass_le` of `GaussianFourPoint.lean`, three applications of `eq:frostman`.
The return half is the four-point bound `eq:joint-return-bound`
evaluated on the block: on `E_{β,η}` the determinant of either overlapping pairing is at
least `βη/4` and the longer of the two intervals has length at least `(β+η)/4`, so the
three terms of `eq:joint-return-bound` are dominated by the three terms of
the return bound with constant `2`.

`eq:joint-return-bound` itself is not proved here; it enters as the hypothesis `hfour`,
whose text is that of the endpoint `audit_gaussian_four_point`.

* `BlockMass.min_le_block`: the arithmetic of the three terms.
* `BlockMass.overlap_crossing`, `BlockMass.overlap_nested`: the overlap of the two
  pairings of `eq:crossing-determinant` and `eq:nested-determinant` is `x₃ - x₂`.
* `BlockMass.crossing_le`, `BlockMass.nested_le`: the return bound for one
  pairing.
* `endpoint_block_mass_of_four_point`, `endpoint_block_mass_dyadic_of_four_point`:
  `thm:endpoint-block-mass`, general and dyadic, conditional on `hfour`.
-/
import BrownianImages.FourPoint
import BrownianImages.GaussianFourPoint

namespace BrownianImages

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

namespace BlockMass

/-! ### The arithmetic of the return bound -/

/-- The three terms of `eq:joint-return-bound` against the three terms of
the return bound: a determinant at least `βη/4` and a longer interval at least
`(β+η)/4` cost a factor `2`. -/
theorem min_le_block {r β η D Δ z : ℝ} (hr : 0 < r) (hβ : 0 < β) (hη : 0 < η)
    (hdet : β * η / 4 ≤ Δ) (hlen : (β + η) / 4 ≤ D)
    (hz : z ≤ min 1 (min (r ^ 2 / (2 * D)) (r ^ 4 / (4 * Δ)))) :
    z ≤ 2 * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) := by
  have hβη : (0:ℝ) < β + η := by linarith
  have hΔ : (0:ℝ) < Δ := lt_of_lt_of_le (by positivity) hdet
  have hD : (0:ℝ) < D := lt_of_lt_of_le (by positivity) hlen
  have h1 : z ≤ 1 := le_trans hz (min_le_left _ _)
  have h2 : z ≤ r ^ 2 / (2 * D) := le_trans hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : z ≤ r ^ 4 / (4 * Δ) := le_trans hz (le_trans (min_le_right _ _) (min_le_right _ _))
  have hA : r ^ 2 / (2 * D) ≤ 2 * (r ^ 2 / (β + η)) := by
    have hrw : 2 * (r ^ 2 / (β + η)) = r ^ 2 / ((β + η) / 2) := by
      field_simp
    rw [hrw]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hB : r ^ 4 / (4 * Δ) ≤ 2 * (r ^ 4 / (β * η)) := by
    have hb1 : r ^ 4 / (4 * Δ) ≤ r ^ 4 / (β * η) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have hb2 : (0:ℝ) ≤ r ^ 4 / (β * η) := by positivity
    linarith
  rcases le_total (1:ℝ) (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]
    rcases le_total (r ^ 2 / (β + η)) (r ^ 4 / (β * η)) with h' | h'
    · rw [min_eq_left h']; linarith
    · rw [min_eq_right h']; linarith

/-! ### The two overlapping pairings on the block -/

/-- The crossing pairing `[x₁,x₃]`, `[x₂,x₄]` of `eq:crossing-determinant` overlaps in
`[x₂,x₃]`. -/
theorem overlap_crossing {x₁ x₂ x₃ x₄ : ℝ} (h12 : x₁ < x₂) (h23 : x₂ < x₃) (h34 : x₃ < x₄) :
    overlap x₁ x₃ x₂ x₄ = x₃ - x₂ := by
  have h13 : x₁ ≤ x₃ := by linarith
  have h24 : x₂ ≤ x₄ := by linarith
  simp only [overlap, max_eq_right h13, min_eq_left h13, max_eq_right h24, min_eq_left h24,
    min_eq_left h34.le, max_eq_right h12.le]
  exact max_eq_right (by linarith)

/-- The nested pairing `[x₁,x₄]`, `[x₂,x₃]` of `eq:nested-determinant` overlaps in
`[x₂,x₃]`. -/
theorem overlap_nested {x₁ x₂ x₃ x₄ : ℝ} (h12 : x₁ < x₂) (h23 : x₂ < x₃) (h34 : x₃ < x₄) :
    overlap x₁ x₄ x₂ x₃ = x₃ - x₂ := by
  have h14 : x₁ ≤ x₄ := by linarith
  have h23' : x₂ ≤ x₃ := h23.le
  simp only [overlap, max_eq_right h14, min_eq_left h14, max_eq_right h23', min_eq_left h23',
    min_eq_right h34.le, max_eq_right h12.le]
  exact max_eq_right (by linarith)

variable {P : Measure Ω} {W : ℝ≥0 → Ω → Plane}

/-- The return bound of `thm:endpoint-block-mass` for the crossing pairing `[x₁,x₃]`, `[x₂,x₄]`: the
determinant `eq:crossing-determinant` is at least `bh ≥ βη/4` and the longer interval is
at least `(b+h)/2 ≥ (β+η)/4`. -/
theorem crossing_le
    (hfour : ∀ {r : ℝ} {t u t' u' : ℝ≥0} (_hr : 0 < r)
      (_hΔ : 0 < |(u:ℝ) - t| * |(u':ℝ) - t'| - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2),
      (jointReturn W P r t u t' u').toReal
        ≤ min 1 (min (r ^ 2 / (2 * max |(u:ℝ) - t| |(u':ℝ) - t'|))
            (r ^ 4 / (4 * (|(u:ℝ) - t| * |(u':ℝ) - t'|
              - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2)))))
    {r β η : ℝ} (hr : 0 < r) (hβ : 0 < β) (hη : 0 < η) {x₁ x₂ x₃ x₄ : ℝ} (hx₁ : 0 ≤ x₁)
    (h12 : x₁ < x₂) (h23 : x₂ < x₃) (h34 : x₃ < x₄)
    (hb : β / 2 < x₃ - x₂) (hh : η / 2 < (x₂ - x₁) + (x₄ - x₃)) :
    (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
      ≤ 2 * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) := by
  have e1 : ((x₁.toNNReal : ℝ≥0) : ℝ) = x₁ := Real.coe_toNNReal x₁ hx₁
  have e2 : ((x₂.toNNReal : ℝ≥0) : ℝ) = x₂ := Real.coe_toNNReal x₂ (by linarith)
  have e3 : ((x₃.toNNReal : ℝ≥0) : ℝ) = x₃ := Real.coe_toNNReal x₃ (by linarith)
  have e4 : ((x₄.toNNReal : ℝ≥0) : ℝ) = x₄ := Real.coe_toNNReal x₄ (by linarith)
  have hdet : β * η / 4
      ≤ |((x₃.toNNReal : ℝ≥0) : ℝ) - ((x₁.toNNReal : ℝ≥0) : ℝ)|
          * |((x₄.toNNReal : ℝ≥0) : ℝ) - ((x₂.toNNReal : ℝ≥0) : ℝ)|
        - overlap ((x₁.toNNReal : ℝ≥0) : ℝ) ((x₃.toNNReal : ℝ≥0) : ℝ)
            ((x₂.toNNReal : ℝ≥0) : ℝ) ((x₄.toNNReal : ℝ≥0) : ℝ) ^ 2 := by
    rw [e1, e2, e3, e4, overlap_crossing h12 h23 h34,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x₃ - x₁),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x₄ - x₂)]
    have hcd := crossing_det_ge (a := x₂ - x₁) (b := x₃ - x₂) (c := x₄ - x₃)
      (by linarith) (by linarith)
    linarith [det_ge_block hβ hη hb hh, hcd]
  have hlen : (β + η) / 4
      ≤ max |((x₃.toNNReal : ℝ≥0) : ℝ) - ((x₁.toNNReal : ℝ≥0) : ℝ)|
          |((x₄.toNNReal : ℝ≥0) : ℝ) - ((x₂.toNNReal : ℝ≥0) : ℝ)| := by
    rw [e1, e2, e3, e4, abs_of_nonneg (by linarith : (0:ℝ) ≤ x₃ - x₁),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x₄ - x₂)]
    have hm1 : x₃ - x₁ ≤ max (x₃ - x₁) (x₄ - x₂) := le_max_left _ _
    have hm2 : x₄ - x₂ ≤ max (x₃ - x₁) (x₄ - x₂) := le_max_right _ _
    linarith [length_ge_block hb hh]
  exact min_le_block hr hβ hη hdet hlen
    (hfour hr (lt_of_lt_of_le (by positivity) hdet))

/-- The return bound of `thm:endpoint-block-mass` for the nested pairing `[x₁,x₄]`, `[x₂,x₃]`: the determinant
`eq:nested-determinant` is exactly `bh ≥ βη/4` and the longer interval has length
`b + h ≥ (β+η)/4`. -/
theorem nested_le
    (hfour : ∀ {r : ℝ} {t u t' u' : ℝ≥0} (_hr : 0 < r)
      (_hΔ : 0 < |(u:ℝ) - t| * |(u':ℝ) - t'| - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2),
      (jointReturn W P r t u t' u').toReal
        ≤ min 1 (min (r ^ 2 / (2 * max |(u:ℝ) - t| |(u':ℝ) - t'|))
            (r ^ 4 / (4 * (|(u:ℝ) - t| * |(u':ℝ) - t'|
              - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2)))))
    {r β η : ℝ} (hr : 0 < r) (hβ : 0 < β) (hη : 0 < η) {x₁ x₂ x₃ x₄ : ℝ} (hx₁ : 0 ≤ x₁)
    (h12 : x₁ < x₂) (h23 : x₂ < x₃) (h34 : x₃ < x₄)
    (hb : β / 2 < x₃ - x₂) (hh : η / 2 < (x₂ - x₁) + (x₄ - x₃)) :
    (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
      ≤ 2 * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) := by
  have e1 : ((x₁.toNNReal : ℝ≥0) : ℝ) = x₁ := Real.coe_toNNReal x₁ hx₁
  have e2 : ((x₂.toNNReal : ℝ≥0) : ℝ) = x₂ := Real.coe_toNNReal x₂ (by linarith)
  have e3 : ((x₃.toNNReal : ℝ≥0) : ℝ) = x₃ := Real.coe_toNNReal x₃ (by linarith)
  have e4 : ((x₄.toNNReal : ℝ≥0) : ℝ) = x₄ := Real.coe_toNNReal x₄ (by linarith)
  have hdet : β * η / 4
      ≤ |((x₄.toNNReal : ℝ≥0) : ℝ) - ((x₁.toNNReal : ℝ≥0) : ℝ)|
          * |((x₃.toNNReal : ℝ≥0) : ℝ) - ((x₂.toNNReal : ℝ≥0) : ℝ)|
        - overlap ((x₁.toNNReal : ℝ≥0) : ℝ) ((x₄.toNNReal : ℝ≥0) : ℝ)
            ((x₂.toNNReal : ℝ≥0) : ℝ) ((x₃.toNNReal : ℝ≥0) : ℝ) ^ 2 := by
    rw [e1, e2, e3, e4, overlap_nested h12 h23 h34,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x₄ - x₁),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x₃ - x₂)]
    have hnd := nested_det (x₂ - x₁) (x₃ - x₂) (x₄ - x₃)
    linarith [det_ge_block hβ hη hb hh, hnd]
  have hlen : (β + η) / 4
      ≤ max |((x₄.toNNReal : ℝ≥0) : ℝ) - ((x₁.toNNReal : ℝ≥0) : ℝ)|
          |((x₃.toNNReal : ℝ≥0) : ℝ) - ((x₂.toNNReal : ℝ≥0) : ℝ)| := by
    rw [e1, e2, e3, e4, abs_of_nonneg (by linarith : (0:ℝ) ≤ x₄ - x₁),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x₃ - x₂)]
    have hm1 : x₄ - x₁ ≤ max (x₄ - x₁) (x₃ - x₂) := le_max_left _ _
    linarith [length_ge_block hb hh]
  exact min_le_block hr hβ hη hdet hlen
    (hfour hr (lt_of_lt_of_le (by positivity) hdet))

end BlockMass

/-! ### `thm:endpoint-block-mass` -/

-- the statement text is frozen against `Challenge.lean`, so unused binders stay
/-- `thm:endpoint-block-mass`, both halves,
conditional on `eq:joint-return-bound`, which enters as the hypothesis `hfour` in the
text of the endpoint `audit_gaussian_four_point`.  The constant is `max (A³) 2`: the mass
half costs `A³`, three applications of `eq:frostman`, and the return half costs `2`. -/
theorem endpoint_block_mass_of_four_point {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (_hW : IsPlanarBrownian W P) {s A : ℝ} (_hs : 0 < s)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hfour : ∀ {r : ℝ} {t u t' u' : ℝ≥0} (_hr : 0 < r)
      (_hΔ : 0 < |(u:ℝ) - t| * |(u':ℝ) - t'| - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2),
      (jointReturn W P r t u t' u').toReal
        ≤ min 1 (min (r ^ 2 / (2 * max |(u:ℝ) - t| |(u':ℝ) - t'|))
            (r ^ 4 / (4 * (|(u:ℝ) - t| * |(u':ℝ) - t'|
              - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2))))) :
    ∃ C > 0, ∀ β η : ℝ, 0 < β → β ≤ 1 → 0 < η → η ≤ 1 →
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          β / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ β ∧
          η / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ η}
        ≤ ENNReal.ofReal (C * β ^ s * η ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        β / 2 < x₃ - x₂ → x₃ - x₂ ≤ β →
        η / 2 < (x₂ - x₁) + (x₄ - x₃) → (x₂ - x₁) + (x₄ - x₃) ≤ η →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) := by
  obtain ⟨C₀, hC₀, hmass⟩ := endpoint_block_mass_le hμ
  refine ⟨max C₀ 2, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro β η hβ0 hβ1 hη0 hη1
  have hβs : (0:ℝ) ≤ β ^ s := (Real.rpow_pos_of_pos hβ0 s).le
  have hηs : (0:ℝ) ≤ η ^ (2 * s) := (Real.rpow_pos_of_pos hη0 (2 * s)).le
  constructor
  · refine le_trans (hmass β η hβ0 hβ1 hη0 hη1) (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left _ _
  · intro r hr x₁ x₂ x₃ x₄ hx₁ h12 h23 h34 hb _ hh _
    have hmin : (0:ℝ) ≤ min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) := by
      have hβη : (0:ℝ) < β + η := by linarith
      refine le_min zero_le_one (le_min ?_ ?_) <;> positivity
    have hcoef : (2:ℝ) * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η)))
        ≤ max C₀ 2 * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hmin
    exact ⟨le_trans (BlockMass.crossing_le hfour hr hβ0 hη0 hx₁ h12 h23 h34 hb hh) hcoef,
      le_trans (BlockMass.nested_le hfour hr hβ0 hη0 hx₁ h12 h23 h34 hb hh) hcoef⟩

-- the statement text is frozen against `Challenge.lean`, so unused binders stay
/-- `thm:endpoint-block-mass` at the dyadic values `β, η ∈ 𝒟` the paper uses, with both
halves of the lemma, conditional on `eq:joint-return-bound` as above.  Every `(1/2)^j`
lies in `(0,1]`, so this is the general statement read at those values. -/
theorem endpoint_block_mass_dyadic_of_four_point {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs : 0 < s)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hfour : ∀ {r : ℝ} {t u t' u' : ℝ≥0} (_hr : 0 < r)
      (_hΔ : 0 < |(u:ℝ) - t| * |(u':ℝ) - t'| - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2),
      (jointReturn W P r t u t' u').toReal
        ≤ min 1 (min (r ^ 2 / (2 * max |(u:ℝ) - t| |(u':ℝ) - t'|))
            (r ^ 4 / (4 * (|(u:ℝ) - t| * |(u':ℝ) - t'|
              - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2))))) :
    ∃ C > 0, ∀ j l : ℕ,
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          ((1:ℝ)/2) ^ j / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ ((1:ℝ)/2) ^ j ∧
          ((1:ℝ)/2) ^ l / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ ((1:ℝ)/2) ^ l}
        ≤ ENNReal.ofReal (C * (((1:ℝ)/2) ^ j) ^ s * (((1:ℝ)/2) ^ l) ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        ((1:ℝ)/2) ^ j / 2 < x₃ - x₂ → x₃ - x₂ ≤ ((1:ℝ)/2) ^ j →
        ((1:ℝ)/2) ^ l / 2 < (x₂ - x₁) + (x₄ - x₃) →
        (x₂ - x₁) + (x₄ - x₃) ≤ ((1:ℝ)/2) ^ l →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) := by
  obtain ⟨C, hC, hblock⟩ := endpoint_block_mass_of_four_point hW hs hμ hfour
  refine ⟨C, hC, fun j l => hblock (((1:ℝ)/2) ^ j) (((1:ℝ)/2) ^ l) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))⟩

end BrownianImages
