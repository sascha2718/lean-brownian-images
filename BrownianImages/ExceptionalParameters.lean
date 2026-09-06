/-
The countable exceptional set in `thm:cantor-application`.

The logarithmic ratio determines the similarity dimension on `(0,1)`: with
`x = 2^{-s}` it satisfies `x^q + x = 1`, whose left side is strictly increasing in
`x`.  Rational ratios therefore give an injection into `ℚ`.  The map
`λ ↦ log 2 / log (1/λ)` is injective on `(0,1/2)`, so the corresponding parameter set
is countable as well.
-/
import BrownianImages.SelfSimilar

namespace BrownianImages

open Set Real

/-- The ratio `log(1/c) / log 2` of `eq:non-lattice` as a function of the dimension `s`,
with `c = c(s)` the ratio of `eq:c-definition`. -/
noncomputable def nonArithmeticRatio (s : ℝ) : ℝ :=
  Real.log (pairRatio s)⁻¹ / Real.log 2

/-- A positive real is `2` raised to minus its base-two logarithm of the inverse: `c =
2^{-(log c⁻¹ / log 2)}`. -/
lemma pos_eq_two_rpow_neg_log_inv_div_log_two {c : ℝ} (hc : 0 < c) :
    c = (2 : ℝ) ^ (-(Real.log c⁻¹ / Real.log 2)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  have hlog2 : Real.log 2 ≠ 0 := log_two_pos.ne'
  have he : Real.log 2 * (-(Real.log c⁻¹ / Real.log 2)) = Real.log c := by
    rw [div_eq_mul_inv]
    calc
      Real.log 2 * (-(Real.log c⁻¹ * (Real.log 2)⁻¹))
          = -Real.log c⁻¹ * (Real.log 2 * (Real.log 2)⁻¹) := by ring
      _ = -Real.log c⁻¹ := by rw [mul_inv_cancel₀ hlog2, mul_one]
      _ = Real.log c := by rw [Real.log_inv]; ring
  rw [he, Real.exp_log hc]

/-- `eq:c-definition` in terms of the logarithmic ratio: `c(s) = 2^{-q(s)}` with `q =
nonArithmeticRatio`. -/
lemma pairRatio_eq_two_rpow_neg_nonArithmeticRatio {s : ℝ} (hs : 0 < s) :
    pairRatio s = (2 : ℝ) ^ (-nonArithmeticRatio s) := by
  exact pos_eq_two_rpow_neg_log_inv_div_log_two (pairRatio_pos hs)

/-- With `x = 2^{-s}`, `eq:c-definition` reads `x^q + x = 1` for `q = nonArithmeticRatio
s`. -/
lemma pairRatio_equation_in_x {s : ℝ} (hs0 : 0 < s) (_hs1 : s < 1) :
    let x := (2 : ℝ) ^ (-s)
    x ^ nonArithmeticRatio s + x = 1 := by
  dsimp
  have hbase : (0 : ℝ) ≤ 2 := by norm_num
  have hc := pairRatio_rpow hs0
  rw [pairRatio_eq_two_rpow_neg_nonArithmeticRatio hs0] at hc
  have hpow : ((2 : ℝ) ^ (-nonArithmeticRatio s)) ^ s
      = ((2 : ℝ) ^ (-s)) ^ nonArithmeticRatio s := by
    rw [← Real.rpow_mul hbase, ← Real.rpow_mul hbase]
    congr 1
    ring
  rw [hpow] at hc
  linarith

/-- The logarithmic ratio is positive on `0 < s < 1`. -/
lemma nonArithmeticRatio_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    0 < nonArithmeticRatio s := by
  unfold nonArithmeticRatio
  exact div_pos (Real.log_pos (by
    rw [one_lt_inv₀ (pairRatio_pos hs0)]
    exact lt_trans (pairRatio_lt_half hs0 hs1) (by norm_num))) log_two_pos

/-- The logarithmic ratio determines the dimension on `(0,1)`: the left side of `x^q + x
= 1` is strictly monotone in `x`. -/
lemma nonArithmeticRatio_injective_on {s₁ s₂ : ℝ}
    (h₁0 : 0 < s₁) (h₁1 : s₁ < 1) (h₂0 : 0 < s₂) (h₂1 : s₂ < 1)
    (hq : nonArithmeticRatio s₁ = nonArithmeticRatio s₂) : s₁ = s₂ := by
  let x₁ : ℝ := (2 : ℝ) ^ (-s₁)
  let x₂ : ℝ := (2 : ℝ) ^ (-s₂)
  have hx₁0 : 0 < x₁ := Real.rpow_pos_of_pos (by norm_num) _
  have hx₂0 : 0 < x₂ := Real.rpow_pos_of_pos (by norm_num) _
  have heq₁ := pairRatio_equation_in_x h₁0 h₁1
  have heq₂ := pairRatio_equation_in_x h₂0 h₂1
  dsimp only at heq₁ heq₂
  rw [hq] at heq₁
  have hq0 := nonArithmeticRatio_pos h₂0 h₂1
  have hx : x₁ = x₂ := by
    rcases lt_trichotomy x₁ x₂ with hlt | heq | hgt
    · have hp : x₁ ^ nonArithmeticRatio s₂ < x₂ ^ nonArithmeticRatio s₂ :=
        (Real.rpow_lt_rpow_iff hx₁0.le hx₂0.le hq0).2 hlt
      linarith
    · exact heq
    · have hp : x₂ ^ nonArithmeticRatio s₂ < x₁ ^ nonArithmeticRatio s₂ :=
        (Real.rpow_lt_rpow_iff hx₂0.le hx₁0.le hq0).2 hgt
      linarith
  have hexp : -s₁ = -s₂ :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1:ℝ) < 2)).injective hx
  linarith

/-- The dimensions `s ∈ (0,1)` at which `eq:non-lattice` fails, that is at which the
logarithmic ratio is rational. -/
def exceptionalDimensions : Set ℝ :=
  {s | 0 < s ∧ s < 1 ∧ ¬ Irrational (nonArithmeticRatio s)}

/-- The rational value of the logarithmic ratio at an exceptional dimension. -/
noncomputable def exceptionalRational (s : exceptionalDimensions) : ℚ :=
  Classical.choose (exists_rat_of_not_irrational s.2.2.2)

/-- `exceptionalRational` is the logarithmic ratio at its argument. -/
lemma exceptionalRational_spec (s : exceptionalDimensions) :
  nonArithmeticRatio s.1 = (exceptionalRational s : ℝ) :=
  Classical.choose_spec (exists_rat_of_not_irrational s.2.2.2)

/-- Distinct exceptional dimensions have distinct rational ratios, by
`nonArithmeticRatio_injective_on`. -/
lemma exceptionalRational_injective : Function.Injective exceptionalRational := by
  intro s₁ s₂ h
  apply SetCoe.ext
  apply nonArithmeticRatio_injective_on s₁.2.1 s₁.2.2.1 s₂.2.1 s₂.2.2.1
  rw [exceptionalRational_spec, exceptionalRational_spec, h]

/-- The exceptional dimensions form a countable set: they inject into `ℚ`. -/
theorem exceptionalDimensions_countable : exceptionalDimensions.Countable := by
  rw [Set.countable_iff_exists_injective]
  exact ⟨fun s => Encodable.encode (exceptionalRational s),
    Encodable.encode_injective.comp exceptionalRational_injective⟩

/-- The parameters `λ ∈ (0, 1/2)` whose homogeneous dimension `log 2 / log(1/λ)` is
exceptional, the countable exceptional set of `thm:cantor-application`. -/
def exceptionalParameters : Set ℝ :=
  {lam | 0 < lam ∧ lam < 1/2 ∧
    ¬ Irrational (nonArithmeticRatio (homogeneousDim lam))}

/-- The homogeneous dimension `log 2 / log(1/λ)` is injective on `(0, 1/2)`. -/
lemma homogeneousDim_injective_on {lam₁ lam₂ : ℝ}
    (h₁0 : 0 < lam₁) (h₁ : lam₁ < 1/2) (h₂0 : 0 < lam₂) (h₂ : lam₂ < 1/2)
    (hdim : homogeneousDim lam₁ = homogeneousDim lam₂) : lam₁ = lam₂ := by
  have hs0 := homogeneousDim_pos h₁0 h₁
  apply (Real.rpow_left_inj h₁0.le h₂0.le hs0.ne').mp
  calc
    lam₁ ^ homogeneousDim lam₁ = 1/2 := rpow_homogeneousDim h₁0 h₁
    _ = lam₂ ^ homogeneousDim lam₂ := (rpow_homogeneousDim h₂0 h₂).symm
    _ = lam₂ ^ homogeneousDim lam₁ := by rw [hdim]

/-- An exceptional parameter, read as its exceptional dimension. -/
noncomputable def exceptionalParameterToDimension (lam : exceptionalParameters) :
    exceptionalDimensions :=
  ⟨homogeneousDim lam.1,
    homogeneousDim_pos lam.2.1 lam.2.2.1,
    homogeneousDim_lt_one lam.2.1 lam.2.2.1,
    lam.2.2.2⟩

/-- The passage from exceptional parameters to exceptional dimensions is injective, by
`homogeneousDim_injective_on`. -/
lemma exceptionalParameterToDimension_injective :
    Function.Injective exceptionalParameterToDimension := by
  intro lam₁ lam₂ h
  apply SetCoe.ext
  apply homogeneousDim_injective_on lam₁.2.1 lam₁.2.2.1 lam₂.2.1 lam₂.2.2.1
  exact congrArg Subtype.val h

/-- `thm:cantor-application`, final sentence: the exceptional parameter set is
countable.  The endpoint `audit_exceptional_parameters_countable`. -/
theorem exceptionalParameters_countable : exceptionalParameters.Countable := by
  rw [Set.countable_iff_exists_injective]
  letI := exceptionalDimensions_countable.toEncodable
  exact ⟨fun lam => Encodable.encode (exceptionalParameterToDimension lam),
    Encodable.encode_injective.comp exceptionalParameterToDimension_injective⟩

end BrownianImages
