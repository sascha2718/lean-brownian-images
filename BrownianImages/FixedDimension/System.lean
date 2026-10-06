/-
`sec:fixed-dimension-family`: the two-contraction family of fixed dimension `s`, with
contractions `a = p^{1/s}` and `b = q^{1/s}`, `q = 1 - p`, so that `a^s + b^s = 1`, and the
objects of `sec:small-dimension` built on it.

* `fixedA`, `fixedB`: the contractions `a` and `b`.
* `fixedSystem`: the system `x ↦ ax`, `x ↦ bx + 1 - b`, on `0 < p < 1` and `0 < s`.
* `fixedCode`: its coding map, `0` outside the parameter range.
* `fixedCross`: the cross-distance `Z_p = 1 - b + bY - aX`.
* `fixedMoment`: `M_p(s) = 𝔼 Z_p^{-s}` over two independent Bernoulli codings with letter
  weights `p` and `q`.
* `entropy`, `fixedMean`: `E(p) = -p log p - q log q` and the right-hand side of
  `eq:fixed-dimension-mean`.
* `kappa`: the logarithmic derivative of the entropy factor, `eq:log-derivative-mean`.
-/
import BrownianImages.TwoContraction.Moment

namespace BrownianImages

open MeasureTheory Filter Set Hutchinson
open scoped Topology ENNReal

noncomputable section

/-! ### The contractions -/

/-- The first contraction `a = p^{1/s}`. -/
def fixedA (s p : ℝ) : ℝ := p ^ s⁻¹

/-- The second contraction `b = (1 - p)^{1/s}`. -/
def fixedB (s p : ℝ) : ℝ := (1 - p) ^ s⁻¹

theorem fixedA_pos {s p : ℝ} (hp0 : 0 < p) : 0 < fixedA s p :=
  Real.rpow_pos_of_pos hp0 _

theorem fixedB_pos {s p : ℝ} (hp1 : p < 1) : 0 < fixedB s p :=
  Real.rpow_pos_of_pos (by linarith) _

theorem fixedA_lt_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : fixedA s p < 1 :=
  Real.rpow_lt_one hp0.le hp1 (inv_pos.2 hs)

theorem fixedB_lt_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : fixedB s p < 1 :=
  Real.rpow_lt_one (by linarith) (by linarith) (inv_pos.2 hs)

theorem fixedA_le_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : fixedA s p ≤ 1 :=
  (fixedA_lt_one hs hp0 hp1).le

theorem fixedB_le_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : fixedB s p ≤ 1 :=
  (fixedB_lt_one hs hp0 hp1).le

/-- `x ↦ x^{-s}` is antitone on `(0, ∞)` for `0 ≤ s`. -/
theorem rpow_neg_antitone {x y s : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hs : 0 ≤ s) :
    y ^ (-s) ≤ x ^ (-s) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.trans_le hxy).le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy hs)

/-- `a^s = p`. -/
theorem fixedA_rpow {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) : fixedA s p ^ s = p :=
  Real.rpow_inv_rpow hp0.le hs.ne'

/-- `b^s = 1 - p`. -/
theorem fixedB_rpow {s p : ℝ} (hs : 0 < s) (hp1 : p < 1) : fixedB s p ^ s = 1 - p :=
  Real.rpow_inv_rpow (by linarith) hs.ne'

/-- For `s < 1`, `a < p`. -/
theorem fixedA_lt {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    fixedA s p < p := by
  have h1 : (1:ℝ) < s⁻¹ := one_lt_inv_iff₀.2 ⟨hs, hs1⟩
  have := Real.rpow_lt_rpow_of_exponent_gt hp0 hp1 h1
  simpa [fixedA] using this

/-- For `s < 1`, `b < 1 - p`. -/
theorem fixedB_lt {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    fixedB s p < 1 - p := by
  have h1 : (1:ℝ) < s⁻¹ := one_lt_inv_iff₀.2 ⟨hs, hs1⟩
  have := Real.rpow_lt_rpow_of_exponent_gt (by linarith : (0:ℝ) < 1 - p) (by linarith) h1
  simpa [fixedB] using this

/-- For `s < 1` the first-level intervals are disjoint: `a + b < 1`. -/
theorem fixedA_add_fixedB_lt_one {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) : fixedA s p + fixedB s p < 1 := by
  have := fixedA_lt hs hs1 hp0 hp1
  have := fixedB_lt hs hs1 hp0 hp1
  linarith

/-! ### The system and its coding map -/

/-- The system `x ↦ ax`, `x ↦ bx + 1 - b` of `sec:fixed-dimension-family`. -/
def fixedSystem (s p : ℝ) (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : System (Fin 2) where
  ratio i := if i = 0 then fixedA s p else fixedB s p
  sign _ := 1
  shift i := if i = 0 then 0 else 1 - fixedB s p
  ratio_pos i := by
    fin_cases i
    · simpa using fixedA_pos (s := s) hp0
    · simpa using fixedB_pos (s := s) hp1
  ratio_lt_one i := by
    fin_cases i
    · simpa using fixedA_lt_one hs hp0 hp1
    · simpa using fixedB_lt_one hs hp0 hp1
  sign_eq _ := Or.inl rfl
  mapsTo i x hx := by
    obtain ⟨h0, h1⟩ := hx
    have ha0 := fixedA_pos (s := s) hp0
    have ha1 := fixedA_lt_one hs hp0 hp1
    have hb0 := fixedB_pos (s := s) hp1
    have hb1 := fixedB_lt_one hs hp0 hp1
    fin_cases i <;> constructor <;> simp <;> nlinarith

@[simp] theorem fixedSystem_ratio_zero {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    (fixedSystem s p hs hp0 hp1).ratio 0 = fixedA s p := rfl

@[simp] theorem fixedSystem_ratio_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    (fixedSystem s p hs hp0 hp1).ratio 1 = fixedB s p := rfl

theorem fixedSystem_map_zero {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    (fixedSystem s p hs hp0 hp1).map 0 x = fixedA s p * x := by
  simp [System.map, fixedSystem]

theorem fixedSystem_map_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    (fixedSystem s p hs hp0 hp1).map 1 x = fixedB s p * x + (1 - fixedB s p) := by
  simp [System.map, fixedSystem]

/-- The weights `a^s = p` and `b^s = q` make `s` the similarity dimension. -/
theorem fixedSystem_isDimension {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    (fixedSystem s p hs hp0 hp1).IsDimension s := by
  simp only [System.IsDimension, Fin.sum_univ_two, fixedSystem_ratio_zero, fixedSystem_ratio_one,
    fixedA_rpow hs hp0, fixedB_rpow hs hp1]
  ring

/-- The coding map of the system on words `ℕ → Fin 2`, and `0` outside the parameter
range. -/
def fixedCode (s p : ℝ) (ω : ℕ → Fin 2) : ℝ :=
  if h : 0 < s ∧ 0 < p ∧ p < 1 then code (fixedSystem s p h.1 h.2.1 h.2.2) ω else 0

theorem fixedCode_eq {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (ω : ℕ → Fin 2) :
    fixedCode s p ω = code (fixedSystem s p hs hp0 hp1) ω := dite_eq_left ⟨hs, hp0, hp1⟩

theorem measurable_fixedCode (s p : ℝ) : Measurable (fixedCode s p) := by
  unfold fixedCode
  split_ifs with h
  · exact measurable_code _
  · exact measurable_const

theorem fixedCode_mem_Icc {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (ω : ℕ → Fin 2) :
    fixedCode s p ω ∈ Icc (0:ℝ) 1 := by
  rw [fixedCode_eq hs hp0 hp1]; exact code_mem_Icc _ ω

theorem fixedCode_cons_zero {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (ω : ℕ → Fin 2) :
    fixedCode s p (cons 0 ω) = fixedA s p * fixedCode s p ω := by
  rw [fixedCode_eq hs hp0 hp1, fixedCode_eq hs hp0 hp1, code_cons, fixedSystem_map_zero]

theorem fixedCode_cons_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (ω : ℕ → Fin 2) :
    fixedCode s p (cons 1 ω) = fixedB s p * fixedCode s p ω + (1 - fixedB s p) := by
  rw [fixedCode_eq hs hp0 hp1, fixedCode_eq hs hp0 hp1, code_cons, fixedSystem_map_one]

/-! ### The cross-distance and its moment -/

/-- The cross-distance `Z_p = 1 - b + bY - aX` at `X = x`, `Y = y`. -/
def fixedCross (s p x y : ℝ) : ℝ := 1 - fixedB s p + fixedB s p * y - fixedA s p * x

/-- At two points of the unit interval the cross-distance lies in `[1 - a - b, 1]`. -/
theorem fixedCross_mem {s p x y : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    1 - fixedA s p - fixedB s p ≤ fixedCross s p x y ∧ fixedCross s p x y ≤ 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have ha0 := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  have ha1 := fixedA_le_one hs hp0 hp1
  unfold fixedCross
  constructor <;> nlinarith

theorem fixedCross_pos {s p x y : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) : 0 < fixedCross s p x y :=
  lt_of_lt_of_le (by linarith [fixedA_add_fixedB_lt_one hs hs1 hp0 hp1])
    (fixedCross_mem hs hp0 hp1 hx hy).1

theorem continuous_fixedCross (s p : ℝ) :
    Continuous fun q : ℝ × ℝ => fixedCross s p q.1 q.2 := by
  unfold fixedCross; fun_prop

/-- The kernel `Z_p^{-s}` at two words. -/
def fixedKernel (s p : ℝ) (ω ω' : ℕ → Fin 2) : ℝ :=
  fixedCross s p (fixedCode s p ω) (fixedCode s p ω') ^ (-s)

theorem measurable_fixedKernel (s p : ℝ) :
    Measurable (Function.uncurry (fixedKernel s p)) := by
  have h1 : Measurable fun q : (ℕ → Fin 2) × (ℕ → Fin 2) => fixedCode s p q.1 :=
    (measurable_fixedCode s p).comp measurable_fst
  have h2 : Measurable fun q : (ℕ → Fin 2) × (ℕ → Fin 2) => fixedCode s p q.2 :=
    (measurable_fixedCode s p).comp measurable_snd
  have h3 : Measurable fun q : (ℕ → Fin 2) × (ℕ → Fin 2) =>
      fixedCross s p (fixedCode s p q.1) (fixedCode s p q.2) :=
    (continuous_fixedCross s p).measurable.comp (h1.prodMk h2)
  exact h3.pow_const _

/-- The kernel lies in `[1, (1 - a - b)^{-s}]`. -/
theorem fixedKernel_mem {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ω ω' : ℕ → Fin 2) :
    1 ≤ fixedKernel s p ω ω' ∧
      fixedKernel s p ω ω' ≤ (1 - fixedA s p - fixedB s p) ^ (-s) := by
  have hmem := fixedCross_mem hs hp0 hp1 (fixedCode_mem_Icc hs hp0 hp1 ω)
    (fixedCode_mem_Icc hs hp0 hp1 ω')
  have hg : 0 < 1 - fixedA s p - fixedB s p := by
    linarith [fixedA_add_fixedB_lt_one hs hs1 hp0 hp1]
  have hz : 0 < fixedCross s p (fixedCode s p ω) (fixedCode s p ω') := lt_of_lt_of_le hg hmem.1
  unfold fixedKernel
  constructor
  · calc (1:ℝ) = 1 ^ (-s) := (Real.one_rpow _).symm
      _ ≤ _ := rpow_neg_antitone hz hmem.2 hs.le
  · exact rpow_neg_antitone hg hmem.1 hs.le

theorem abs_fixedKernel_le {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ω ω' : ℕ → Fin 2) : |fixedKernel s p ω ω'| ≤ (1 - fixedA s p - fixedB s p) ^ (-s) := by
  obtain ⟨h1, h2⟩ := fixedKernel_mem hs hs1 hp0 hp1 ω ω'
  rw [abs_of_nonneg (by linarith)]
  exact h2

/-- `M_p(s) = 𝔼 Z_p^{-s}`: `X` and `Y` are the coded points of two independent Bernoulli
words with letter weights `p` (letter `0`, the map `x ↦ ax`) and `q = 1 - p` (letter `1`,
the map `x ↦ bx + 1 - b`). -/
def fixedMoment (s p : ℝ) : ℝ :=
  ∫ ω', ∫ ω, fixedKernel s p ω ω' ∂twoBern (1 - p) ∂twoBern (1 - p)

theorem isProbabilityMeasure_twoBern_fixed {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    IsProbabilityMeasure (twoBern (1 - p)) :=
  isProbabilityMeasure_twoBern (by linarith) (by linarith)

/-- `M_p(s) ≥ 1`, since `Z_p ≤ 1`. -/
theorem one_le_fixedMoment {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    1 ≤ fixedMoment s p := by
  have := isProbabilityMeasure_twoBern_fixed hp0 hp1
  have hg : 0 < 1 - fixedA s p - fixedB s p := by
    linarith [fixedA_add_fixedB_lt_one hs hs1 hp0 hp1]
  have hone : ∀ ω ω' : ℕ → Fin 2, |(1:ℝ)| ≤ (1 - fixedA s p - fixedB s p) ^ (-s) := by
    intro _ _
    rw [abs_one]
    calc (1:ℝ) = 1 ^ (-s) := (Real.one_rpow _).symm
      _ ≤ _ := rpow_neg_antitone hg (by
          linarith [fixedA_pos (s := s) hp0, fixedB_pos (s := s) hp1]) hs.le
  have h := iterated_integral_mono (P := twoBern (1 - p)) (F := fun _ _ => (1:ℝ))
    (G := fixedKernel s p) measurable_const (measurable_fixedKernel s p)
    (C := (1 - fixedA s p - fixedB s p) ^ (-s)) hone
    (fun ω ω' => abs_fixedKernel_le hs hs1 hp0 hp1 ω ω')
    (fun ω ω' => (fixedKernel_mem hs hs1 hp0 hp1 ω ω').1)
  unfold fixedMoment
  simpa using h

/-! ### The entropy and the mean -/

/-- `E(p) = -p log p - q log q`. -/
def entropy (p : ℝ) : ℝ := -(p * Real.log p) - (1 - p) * Real.log (1 - p)

/-- The right-hand side of `eq:fixed-dimension-mean`,
`H̄_s(p) = 2^{1-s} Γ(1-s) pq M_p(s) / E(p)`. -/
def fixedMean (s p : ℝ) : ℝ :=
  (2:ℝ) ^ (1 - s) * Real.Gamma (1 - s) * (p * (1 - p) / entropy p) * fixedMoment s p

/-- `κ(p) = (q² log(1/q) - p² log(1/p)) / (pq E(p))`, the logarithmic derivative of the
entropy factor `pq/E(p)` in `eq:log-derivative-mean`. -/
def kappa (p : ℝ) : ℝ :=
  ((1 - p) ^ 2 * Real.log (1 - p)⁻¹ - p ^ 2 * Real.log p⁻¹) / (p * (1 - p) * entropy p)

end

end BrownianImages
