/-
`thm:main-term-derivative`: the main term `Σ(p) = ∑_{n≥0} p qⁿ (1 - b^{n+1})^{-s}` of
`eq:main-term` equals `(e^{sT} - 1) S(T)` with `S(T) = ∑_{m≥1} f(mT)` and `T = log(1/b)`,
and its derivative satisfies `|Σ'(p)| ≤ 6 p^{-s}` for `0 < s ≤ 1/2` and `0 < p ≤ 1/50`.

* `mainS`, `mainS'`, `mainTermT`, `fixedT`, `mainTerm`: the objects.
* `hasDerivAt_mainS`: termwise differentiation of `S`.
* `abs_deriv_mainTermT_le`: `|dΣ/dT| ≤ s e^{sT} (sJ/2 + 3 f(T) + |g(T)|)`, by the
  Riemann-sum bounds.
* `mainTerm_eq`, `hasDerivAt_mainTerm`: the change of variables `T = T(p)`.
* `exists_hasDerivAt_mainTerm`: the derivative bound of `thm:main-term-derivative`.
-/
import BrownianImages.FixedDimension.MainTermIntegrals
import BrownianImages.FixedDimension.Entropy

namespace BrownianImages

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

/-- `S(T) = ∑_{m≥1} f(mT)`. -/
def mainS (s T : ℝ) : ℝ := ∑' m : ℕ, mainF s (((m:ℝ) + 1) * T)

/-- `S'(T) = ∑_{m≥1} m f'(mT)`. -/
def mainS' (s T : ℝ) : ℝ := ∑' m : ℕ, ((m:ℝ) + 1) * mainF' s (((m:ℝ) + 1) * T)

/-- `Σ(T) = (e^{sT} - 1) S(T)`. -/
def mainTermT (s T : ℝ) : ℝ := (Real.exp (s * T) - 1) * mainS s T

/-- `T(p) = log(1/b) = s⁻¹ log(1/(1-p))`. -/
def fixedT (s p : ℝ) : ℝ := s⁻¹ * Real.log (1 - p)⁻¹

/-- The main term `Σ(p) = ∑_{n≥0} p qⁿ (1 - b^{n+1})^{-s}` of `eq:main-term`. -/
def mainTerm (s p : ℝ) : ℝ :=
  ∑' n : ℕ, p * (1 - p) ^ n * (1 - fixedB s p ^ (n + 1)) ^ (-s)

/-! ### Summability and the Riemann-sum bounds -/

theorem mem_Ici_of_cell {T : ℝ} (hT : 0 < T) (m : ℕ) : ((m:ℝ) + 1) * T ∈ Ici T := by
  show T ≤ _; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

/-- The Riemann-sum bounds for `f`: `J ≤ T S(T) ≤ J + T f(T)`. -/
theorem mainS_bounds {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    Summable (fun m : ℕ => mainF s (((m:ℝ) + 1) * T)) ∧
    (∫ x in Ioi T, mainF s x) ≤ T * mainS s T ∧
    T * mainS s T ≤ (∫ x in Ioi T, mainF s x) + T * mainF s T := by
  obtain ⟨hsum, h1, h2⟩ := tsum_le_integral_add hT ((mainF_antitoneOn hs.le).mono
    (Ici_subset_Ioi.2 hT)) (fun x hx => (mainF_pos (hT.trans_le hx)).le)
    (integrableOn_mainF hs hs2 hT)
  have hsum' : Summable (fun m : ℕ => mainF s (((m:ℝ) + 1) * T)) := by
    have := hsum.mul_left T⁻¹
    refine this.congr fun m => ?_
    field_simp
  refine ⟨hsum', ?_, ?_⟩
  · rw [mainS, ← tsum_mul_left]; exact h1
  · rw [mainS, ← tsum_mul_left]; exact h2

/-- The Riemann-sum bound for `g`. -/
theorem mainG_sum_bound {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    Summable (fun m : ℕ => T * mainG s (((m:ℝ) + 1) * T)) ∧
    |∑' m : ℕ, T * mainG s (((m:ℝ) + 1) * T) - ∫ x in Ioi T, mainG s x|
      ≤ T * (2 * mainF s T + |mainG s T|) := by
  obtain ⟨hsum, h⟩ := abs_tsum_sub_integral_le hT
    (fun x hx => hasDerivAt_mainG s (hT.trans_le hx)) (integrableOn_mainG hs hs2 hT)
    (integrableOn_mainG' hs hs2 hT)
  exact ⟨hsum, h.trans (mul_le_mul_of_nonneg_left (integral_abs_mainG'_le hs hs2 hT) hT.le)⟩

/-- `S'(T) = T⁻² ∑_{m≥1} T g(mT)`. -/
theorem mainS'_eq (s T : ℝ) (hT : 0 < T) :
    mainS' s T = (∑' m : ℕ, T * mainG s (((m:ℝ) + 1) * T)) / T ^ 2 := by
  unfold mainS'
  rw [← tsum_div_const]
  congr 1
  funext m
  unfold mainG
  field_simp

/-! ### Termwise differentiation of `S` -/

/-- The term `m ↦ f((m+1)y)` and its derivative in `y`. -/
theorem hasDerivAt_mainF_term (s : ℝ) (m : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z => mainF s (((m:ℝ) + 1) * z))
      (((m:ℝ) + 1) * mainF' s (((m:ℝ) + 1) * y)) y := by
  have hpos : 0 < ((m:ℝ) + 1) * y := by positivity
  have h := (hasDerivAt_mainF s hpos).comp y ((hasDerivAt_id y).const_mul ((m:ℝ) + 1))
  exact h.congr_deriv (by simp only [mul_one]; ring)

/-- A summable majorant of the term derivatives on `(T/2, 2T)`. -/
theorem summable_mainF'_majorant {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    Summable fun m : ℕ => s * (2 / T + 1) * (1 - Real.exp (-(T / 2))) ^ (-s) *
      (((m:ℝ) + 1) * Real.exp (-(s * (T / 2))) ^ (m + 1)) := by
  have hr : ‖Real.exp (-(s * (T / 2)))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (by nlinarith)
  have h := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h' : Summable fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 1 * Real.exp (-(s * (T / 2))) ^ (m + 1) :=
    (summable_nat_add_iff 1).2 h
  refine (h'.mul_left (s * (2 / T + 1) * (1 - Real.exp (-(T / 2))) ^ (-s))).congr fun m => ?_
  push_cast
  ring

theorem hasDerivAt_mainS {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    HasDerivAt (mainS s) (mainS' s T) T := by
  set t : Set ℝ := Ioo (T / 2) (2 * T) with ht
  have hopen : IsOpen t := isOpen_Ioo
  have hconn : IsPreconnected t := isPreconnected_Ioo
  have hTt : T ∈ t := ⟨by linarith, by linarith⟩
  have hterm : ∀ (m : ℕ) (y : ℝ), y ∈ t →
      HasDerivAt (fun z => mainF s (((m:ℝ) + 1) * z))
        (((m:ℝ) + 1) * mainF' s (((m:ℝ) + 1) * y)) y :=
    fun m y hy => hasDerivAt_mainF_term s m (by linarith [hy.1])
  -- the majorant
  have hmaj : ∀ (m : ℕ) (y : ℝ), y ∈ t →
      ‖((m:ℝ) + 1) * mainF' s (((m:ℝ) + 1) * y)‖
        ≤ s * (2 / T + 1) * (1 - Real.exp (-(T / 2))) ^ (-s) *
          (((m:ℝ) + 1) * Real.exp (-(s * (T / 2))) ^ (m + 1)) := by
    intro m y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hx0 : 0 < ((m:ℝ) + 1) * y := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (m:ℝ) + 1)]
    -- `|f'(x)| = |g(x)|/x ≤ s (1 + x) f(x) / x`
    have hg := abs_mainG_le hs hx0
    have hg' : |mainG s (((m:ℝ) + 1) * y)| = ((m:ℝ) + 1) * y * |mainF' s (((m:ℝ) + 1) * y)| := by
      unfold mainG; rw [abs_mul, abs_of_pos hx0]
    rw [hg'] at hg
    have hF := mainF_pos (s := s) hx0
    -- `f((m+1)y) ≤ f((m+1)T/2) ≤ (1 - e^{-T/2})^{-s} e^{-s(m+1)T/2}`
    have hmono : mainF s (((m:ℝ) + 1) * y) ≤ mainF s (((m:ℝ) + 1) * (T / 2)) :=
      mainF_antitoneOn hs.le (by positivity : (0:ℝ) < ((m:ℝ) + 1) * (T / 2)) hx0
        (mul_le_mul_of_nonneg_left hy.1.le (by positivity))
    have hexp : mainF s (((m:ℝ) + 1) * (T / 2))
        ≤ (1 - Real.exp (-(T / 2))) ^ (-s) * Real.exp (-(s * (T / 2))) ^ (m + 1) := by
      have := mainF_le_exp hs.le (half_pos hT) (show T / 2 ≤ ((m:ℝ) + 1) * (T / 2) by
        nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
      have e : Real.exp (-(s * (T / 2))) ^ (m + 1)
          = Real.exp (-(s * (((m:ℝ) + 1) * (T / 2)))) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [e]
      exact this
    -- `(1 + x)/y ≤ (2/T + 1)(m + 1)` for `x = (m+1) y`, `y > T/2`
    have hratio : ((m:ℝ) + 1) * (1 + ((m:ℝ) + 1) * y) / (((m:ℝ) + 1) * y)
        ≤ (2 / T + 1) * ((m:ℝ) + 1) := by
      rw [div_le_iff₀ hx0]
      have h1 : 1 ≤ 2 / T * y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hT]; linarith [hy.1]
      have hm : (0:ℝ) ≤ (m:ℝ) + 1 := by positivity
      nlinarith [mul_nonneg hm hm, mul_nonneg hm hy0.le]
    calc ((m:ℝ) + 1) * |mainF' s (((m:ℝ) + 1) * y)|
        ≤ ((m:ℝ) + 1) * (s * (1 + ((m:ℝ) + 1) * y) * mainF s (((m:ℝ) + 1) * y)
            / (((m:ℝ) + 1) * y)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [le_div_iff₀ hx0]; linarith
      _ = s * (((m:ℝ) + 1) * (1 + ((m:ℝ) + 1) * y) / (((m:ℝ) + 1) * y))
            * mainF s (((m:ℝ) + 1) * y) := by field_simp
      _ ≤ s * ((2 / T + 1) * ((m:ℝ) + 1)) * mainF s (((m:ℝ) + 1) * y) := by
          apply mul_le_mul_of_nonneg_right _ hF.le
          exact mul_le_mul_of_nonneg_left hratio hs.le
      _ ≤ s * ((2 / T + 1) * ((m:ℝ) + 1)) *
            ((1 - Real.exp (-(T / 2))) ^ (-s) * Real.exp (-(s * (T / 2))) ^ (m + 1)) := by
          apply mul_le_mul_of_nonneg_left (hmono.trans hexp)
          positivity
      _ = _ := by ring
  have h := hasDerivAt_tsum_of_isPreconnected (summable_mainF'_majorant hs hT) hopen hconn
    hterm hmaj hTt (mainS_bounds hs hs2 hT).1 hTt
  exact h

/-! ### The derivative of `Σ(T)` and its bound -/

theorem hasDerivAt_mainTermT {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    HasDerivAt (mainTermT s)
      (s * Real.exp (s * T) * mainS s T + (Real.exp (s * T) - 1) * mainS' s T) T := by
  have h1 : HasDerivAt (fun y => Real.exp (s * y) - 1) (Real.exp (s * T) * s) T := by
    have := ((Real.hasDerivAt_exp (s * T)).comp T ((hasDerivAt_id T).const_mul s)).sub_const 1
    simpa using this
  have h := h1.mul (hasDerivAt_mainS hs hs2 hT)
  exact h.congr_deriv (by ring)

/-- `0 ≤ x eˣ - eˣ + 1 ≤ x² eˣ / 2` for `x ≥ 0`. -/
theorem mul_exp_sub_exp_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * Real.exp x - Real.exp x + 1 ∧
      x * Real.exp x - Real.exp x + 1 ≤ x ^ 2 * Real.exp x / 2 := by
  constructor
  · have := Real.add_one_le_exp (-x)
    have hpos := Real.exp_pos x
    have h2 : (-x + 1) * Real.exp x ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right this hpos.le
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    nlinarith
  · -- `ψ(x) = x² eˣ/2 - x eˣ + eˣ - 1` is monotone on `[0, ∞)` with `ψ(0) = 0`
    set ψ : ℝ → ℝ := fun y => y ^ 2 * Real.exp y / 2 - y * Real.exp y + Real.exp y - 1 with hψ
    have hd : ∀ y, HasDerivAt ψ (y ^ 2 * Real.exp y / 2) y := by
      intro y
      have h1 := ((hasDerivAt_pow 2 y).mul (Real.hasDerivAt_exp y)).div_const 2
      have h2 := (hasDerivAt_id y).mul (Real.hasDerivAt_exp y)
      have h := ((h1.sub h2).add (Real.hasDerivAt_exp y)).sub_const 1
      exact h.congr_deriv (by simp; ring)
    have hmono : MonotoneOn ψ (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _ => (hd y).continuousAt.continuousWithinAt)
        (fun y _ => (hd y).differentiableAt.differentiableWithinAt) fun y _ => ?_
      rw [(hd y).deriv]; positivity
    have h0 : ψ 0 = 0 := by simp [hψ]
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
    rw [h0] at this
    simp only [hψ] at this
    linarith

/-- `e^{x} - 1 ≤ x e^{x}` for `x ≥ 0`. -/
theorem exp_sub_one_le_mul_exp {x : ℝ} (hx : 0 ≤ x) : Real.exp x - 1 ≤ x * Real.exp x := by
  have := (mul_exp_sub_exp_bounds hx).1; linarith

/-- `|dΣ/dT| ≤ s e^{sT} (sJ/2 + 3 f(T) + |g(T)|)`, `J = ∫_T^∞ f`. -/
theorem abs_deriv_mainTermT_le {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    |s * Real.exp (s * T) * mainS s T + (Real.exp (s * T) - 1) * mainS' s T|
      ≤ s * Real.exp (s * T) *
        (s * (∫ x in Ioi T, mainF s x) / 2 + 3 * mainF s T + |mainG s T|) := by
  set J := ∫ x in Ioi T, mainF s x with hJ
  set fT := mainF s T with hfT
  set gT := |mainG s T| with hgT
  set E := Real.exp (s * T) with hE
  have hJ0 : 0 ≤ J :=
    setIntegral_nonneg measurableSet_Ioi fun x hx => (mainF_pos (hT.trans hx)).le
  have hfT0 : 0 < fT := mainF_pos hT
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  obtain ⟨-, hS1, hS2⟩ := mainS_bounds hs hs2 hT
  obtain ⟨-, hG⟩ := mainG_sum_bound hs hs2 hT
  rw [integral_mainG hs hs2 hT] at hG
  rw [mainS'_eq s T hT]
  -- write `T S = J + A`, `T ∑ g = -T f - J + B`
  set A := T * mainS s T - J with hA
  set B := (∑' m : ℕ, T * mainG s (((m:ℝ) + 1) * T)) - (-(T * fT) - J) with hB
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA1 : A ≤ T * fT := by rw [hA]; linarith
  have hBabs : |B| ≤ T * (2 * fT + gT) := hG
  have hSA : mainS s T = (J + A) / T := by rw [hA]; field_simp; ring
  have hGB : ∑' m : ℕ, T * mainG s (((m:ℝ) + 1) * T) = -(T * fT) - J + B := by rw [hB]; ring
  rw [hSA, hGB]
  -- the elementary bounds
  obtain ⟨hφ0, hφ1⟩ := mul_exp_sub_exp_bounds (show 0 ≤ s * T by positivity)
  have hE' : Real.exp (s * T) = E := rfl
  rw [hE'] at hφ0 hφ1
  have hem : E - 1 ≤ s * T * E := by have := exp_sub_one_le_mul_exp (show 0 ≤ s * T by positivity); rw [hE'] at this; linarith
  have hE0 : 0 ≤ E - 1 := by linarith
  -- decompose
  have hdec : s * E * ((J + A) / T) + (E - 1) * ((-(T * fT) - J + B) / T ^ 2)
      = J * ((s * T * E - E + 1) / T ^ 2) + (s * E * A / T - (E - 1) * fT / T)
        + (E - 1) * B / T ^ 2 := by
    field_simp
    ring
  rw [hdec]
  have hT2 : 0 < T ^ 2 := by positivity
  -- bound each piece
  have hp1 : |J * ((s * T * E - E + 1) / T ^ 2)| ≤ J * (s ^ 2 * E / 2) := by
    rw [abs_of_nonneg (mul_nonneg hJ0 (div_nonneg hφ0 hT2.le))]
    apply mul_le_mul_of_nonneg_left _ hJ0
    rw [div_le_iff₀ hT2]
    calc s * T * E - E + 1 ≤ (s * T) ^ 2 * E / 2 := hφ1
      _ = s ^ 2 * E / 2 * T ^ 2 := by ring
  have hp2 : |s * E * A / T - (E - 1) * fT / T| ≤ s * E * fT := by
    rw [abs_le]
    constructor
    · have h1 : (E - 1) * fT / T ≤ s * E * fT := by
        rw [div_le_iff₀ hT]
        calc (E - 1) * fT ≤ s * T * E * fT := mul_le_mul_of_nonneg_right hem hfT0.le
          _ = s * E * fT * T := by ring
      have h2 : 0 ≤ s * E * A / T := by positivity
      linarith
    · have h1 : s * E * A / T ≤ s * E * fT := by
        rw [div_le_iff₀ hT]
        calc s * E * A ≤ s * E * (T * fT) := by
              apply mul_le_mul_of_nonneg_left hA1; positivity
          _ = s * E * fT * T := by ring
      have h2 : 0 ≤ (E - 1) * fT / T := by positivity
      linarith
  have hp3 : |(E - 1) * B / T ^ 2| ≤ s * E * (2 * fT + gT) := by
    rw [abs_div, abs_mul, abs_of_nonneg hE0, abs_of_pos hT2, div_le_iff₀ hT2]
    calc (E - 1) * |B| ≤ (s * T * E) * (T * (2 * fT + gT)) :=
          mul_le_mul hem hBabs (abs_nonneg _) (by positivity)
      _ = s * E * (2 * fT + gT) * T ^ 2 := by ring
  calc |J * ((s * T * E - E + 1) / T ^ 2) + (s * E * A / T - (E - 1) * fT / T)
        + (E - 1) * B / T ^ 2|
      ≤ |J * ((s * T * E - E + 1) / T ^ 2)| + |s * E * A / T - (E - 1) * fT / T|
        + |(E - 1) * B / T ^ 2| := abs_add_three _ _ _
    _ ≤ J * (s ^ 2 * E / 2) + s * E * fT + s * E * (2 * fT + gT) :=
        add_le_add (add_le_add hp1 hp2) hp3
    _ = s * E * (s * J / 2 + 3 * fT + gT) := by ring

/-! ### The change of variables `T = T(p)` -/

theorem fixedT_pos {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : 0 < fixedT s p := by
  unfold fixedT
  have : 0 < Real.log (1 - p)⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨by linarith, by linarith⟩)
  positivity

/-- `e^{sT} = 1/q`. -/
theorem exp_mul_fixedT {s p : ℝ} (hs : 0 < s) (hp1 : p < 1) :
    Real.exp (s * fixedT s p) = (1 - p)⁻¹ := by
  unfold fixedT
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, Real.exp_log (by
    have : (0:ℝ) < 1 - p := by linarith
    positivity)]

/-- `e^{-T} = b`. -/
theorem exp_neg_fixedT {s p : ℝ} (hp1 : p < 1) :
    Real.exp (-fixedT s p) = fixedB s p := by
  unfold fixedT fixedB
  have hq : (0:ℝ) < 1 - p := by linarith
  rw [Real.log_inv, Real.rpow_def_of_pos hq]
  congr 1
  ring

/-- `b^{n+1} = e^{-(n+1)T}`. -/
theorem fixedB_pow {s p : ℝ} (hp1 : p < 1) (n : ℕ) :
    fixedB s p ^ (n + 1) = Real.exp (-(((n:ℝ) + 1) * fixedT s p)) := by
  rw [← exp_neg_fixedT hp1, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Each term of `eq:main-term` is `(e^{sT} - 1) f((n+1)T)`. -/
theorem mainTerm_term_eq {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    p * (1 - p) ^ n * (1 - fixedB s p ^ (n + 1)) ^ (-s)
      = (Real.exp (s * fixedT s p) - 1) * mainF s (((n:ℝ) + 1) * fixedT s p) := by
  have hq : (0:ℝ) < 1 - p := by linarith
  have hT := fixedT_pos hs hp0 hp1
  set T := fixedT s p with hTdef
  have hx : 0 < ((n:ℝ) + 1) * T := by positivity
  rw [exp_mul_fixedT hs hp1, fixedB_pow hp1]
  unfold mainF
  -- `eˣ - 1 = eˣ (1 - e^{-x})`
  have e1 : Real.exp (((n:ℝ) + 1) * T) - 1
      = Real.exp (((n:ℝ) + 1) * T) * (1 - Real.exp (-(((n:ℝ) + 1) * T))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; simp
  have hpos1 : 0 < 1 - Real.exp (-(((n:ℝ) + 1) * T)) := by
    have := Real.exp_lt_one_iff.2 (neg_lt_zero.2 hx); linarith
  rw [e1, Real.mul_rpow (Real.exp_pos _).le hpos1.le, ← Real.exp_mul]
  -- `e^{-s(n+1)T} = q^{n+1}`
  have e2 : Real.exp (((n:ℝ) + 1) * T * -s) = (1 - p) ^ (n + 1) := by
    have : Real.exp (((n:ℝ) + 1) * T * -s) = Real.exp (-(s * T)) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this, Real.exp_neg, exp_mul_fixedT hs hp1, inv_inv]
  rw [e2]
  field_simp
  ring

theorem summable_mainTerm_terms {s p : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hp0 : 0 < p) (hp1 : p < 1) :
    Summable fun n : ℕ => p * (1 - p) ^ n * (1 - fixedB s p ^ (n + 1)) ^ (-s) := by
  have h := ((mainS_bounds hs hs2 (fixedT_pos hs hp0 hp1)).1).mul_left
    (Real.exp (s * fixedT s p) - 1)
  exact h.congr fun n => (mainTerm_term_eq hs hp0 hp1 n).symm

/-- `Σ(p) = Σ(T(p))`. -/
theorem mainTerm_eq {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    mainTerm s p = mainTermT s (fixedT s p) := by
  unfold mainTerm mainTermT mainS
  rw [← tsum_mul_left]
  exact tsum_congr fun n => mainTerm_term_eq hs hp0 hp1 n

theorem hasDerivAt_fixedT {s p : ℝ} (hp1 : p < 1) :
    HasDerivAt (fixedT s) (s⁻¹ * (1 - p)⁻¹) p := by
  have hq : (0:ℝ) < 1 - p := by linarith
  have h1 : HasDerivAt (fun x : ℝ => Real.log (1 - x)⁻¹) ((1 - p)⁻¹) p := by
    have hinv := ((hasDerivAt_id p).const_sub 1).inv (show (1:ℝ) - id p ≠ 0 from hq.ne')
    have := (Real.hasDerivAt_log (inv_pos.2 hq).ne').comp p hinv
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  exact h1.const_mul s⁻¹

theorem hasDerivAt_mainTerm {s p : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (mainTerm s)
      ((s * Real.exp (s * fixedT s p) * mainS s (fixedT s p)
        + (Real.exp (s * fixedT s p) - 1) * mainS' s (fixedT s p)) * (s⁻¹ * (1 - p)⁻¹)) p := by
  have h := (hasDerivAt_mainTermT hs hs2 (fixedT_pos hs hp0 hp1)).comp p (hasDerivAt_fixedT hp1)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hp0 hp1] with x hx
  exact mainTerm_eq hs hx.1 hx.2

/-! ### `thm:main-term-derivative` -/

/-- `T ≥ p`, since `log(1/(1-p)) ≥ p` and `s ≤ 1`. -/
theorem le_fixedT {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    p ≤ fixedT s p := by
  unfold fixedT
  have h := log_one_sub_inv_ge hp1
  have hs' : 1 ≤ s⁻¹ := one_le_inv_iff₀.2 ⟨hs, hs1⟩
  calc p = 1 * p := (one_mul p).symm
    _ ≤ s⁻¹ * Real.log (1 - p)⁻¹ := mul_le_mul hs' h hp0.le (by linarith)

/-- `s T ≤ p/q`. -/
theorem mul_fixedT_le {s p : ℝ} (hs : 0 < s) (hp1 : p < 1) :
    s * fixedT s p ≤ p / (1 - p) := by
  unfold fixedT
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hq : (0:ℝ) < 1 - p := by linarith
  have := Real.log_le_sub_one_of_pos (inv_pos.2 hq)
  calc Real.log (1 - p)⁻¹ ≤ (1 - p)⁻¹ - 1 := this
    _ = p / (1 - p) := by field_simp; ring

/-- **`thm:main-term-derivative`.**  For `0 < s ≤ 1/2` and `0 < p ≤ 1/50` the main term is
differentiable at `p` with `|Σ'(p)| ≤ 6 p^{-s}`. -/
theorem exists_hasDerivAt_mainTerm {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) : ∃ D, HasDerivAt (mainTerm s) D p ∧ |D| ≤ 6 * p ^ (-s) := by
  have hs2 : s ≤ 2 := by linarith
  have hp1 : p < 1 := by linarith
  have hq : (0:ℝ) < 1 - p := by linarith
  have hT := fixedT_pos hs hp0 hp1
  set T := fixedT s p with hTdef
  refine ⟨_, hasDerivAt_mainTerm hs hs2 hp0 hp1, ?_⟩
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < s⁻¹ * (1 - p)⁻¹)]
  have hD := abs_deriv_mainTermT_le hs hs2 hT
  rw [exp_mul_fixedT hs hp1] at hD ⊢
  -- the pieces
  have hJ := mul_integral_mainF_le hs hs1 hT
  have hfT : mainF s T ≤ p ^ (-s) :=
    (mainF_le_rpow hs.le hT).trans (rpow_neg_antitone hp0 (le_fixedT hs (by linarith) hp0 hp1) hs.le)
  have hgT : |mainG s T| ≤ p ^ (-s) := by
    have h1 := abs_mainG_le hs hT
    have h2 : s * (1 + T) ≤ 1 := by
      have := mul_fixedT_le hs hp1
      have : p / (1 - p) ≤ 1 / 49 := by
        rw [div_le_div_iff₀ hq (by norm_num)]; linarith
      linarith
    calc |mainG s T| ≤ s * (1 + T) * mainF s T := h1
      _ ≤ 1 * p ^ (-s) := mul_le_mul h2 hfT (mainF_pos hT).le (by norm_num)
      _ = p ^ (-s) := one_mul _
  have hp1' : 1 ≤ p ^ (-s) := by
    calc (1:ℝ) = 1 ^ (-s) := (Real.one_rpow _).symm
      _ ≤ p ^ (-s) := rpow_neg_antitone hp0 hp1.le hs.le
  have hq2 : (1 - p)⁻¹ ^ 2 ≤ 2500 / 2401 := by
    have : (1 - p)⁻¹ ≤ 50 / 49 := by
      rw [inv_le_comm₀ hq (by norm_num)]; linarith
    calc (1 - p)⁻¹ ^ 2 ≤ (50 / 49) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) this
      _ = 2500 / 2401 := by norm_num
  calc |s * (1 - p)⁻¹ * mainS s T + ((1 - p)⁻¹ - 1) * mainS' s T| * (s⁻¹ * (1 - p)⁻¹)
      ≤ s * (1 - p)⁻¹ * (s * (∫ x in Ioi T, mainF s x) / 2 + 3 * mainF s T + |mainG s T|)
          * (s⁻¹ * (1 - p)⁻¹) := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = (1 - p)⁻¹ ^ 2 * (s * (∫ x in Ioi T, mainF s x) / 2 + 3 * mainF s T + |mainG s T|) := by
        field_simp
    _ ≤ 2500 / 2401 * (2.3 / 2 + 3 * p ^ (-s) + p ^ (-s)) := by
        have hJ0 : 0 ≤ ∫ x in Ioi T, mainF s x :=
          setIntegral_nonneg measurableSet_Ioi fun x hx => (mainF_pos (hT.trans hx)).le
        apply mul_le_mul hq2 _ (add_nonneg (add_nonneg (div_nonneg (mul_nonneg hs.le hJ0)
          (by norm_num)) (mul_nonneg (by norm_num) (mainF_pos hT).le)) (abs_nonneg _))
          (by norm_num)
        linarith
    _ ≤ 6 * p ^ (-s) := by nlinarith

end

end BrownianImages
