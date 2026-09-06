/-
`thm:homometric-example` of `sec:obstruction`: two distinct strongly separated
self-similar measures with identical pair-distance distributions.

The whole content of the example is finite and is proved here: the two digit sets
have the same signed difference multiset, the two systems are strongly separated, and
the common dimension `t = log 6 / log 30` lies in `(1/2, 1)` and solves
`6·(1/30)^t = 1`.  What the multiset equality buys probabilistically, namely that the
level differences `D_n - D'_n` are equidistributed, is `diffCount_eq`.

* `digitsA`, `digitsB`: the digit sets `{0,1,4,10,12,17}` and `{0,1,8,11,13,17}`.
* `diffMultiset_eq`, `diffCount_eq`: the homometry of the two digit sets.
* `strong_separation`: distinct first-level cylinders stay `1/45` apart.
* `tHom`, `tHom_mem_Ioo`, `six_mul_rpow_tHom`: the common dimension.
-/
import BrownianImages.SelfSimilar

namespace BrownianImages

open Real MeasureTheory
open scoped ENNReal

/-! ### The two digit sets -/

/-- The digit set `𝒜 = {0,1,4,10,12,17}`. -/
def digitsA : Finset ℤ := {0, 1, 4, 10, 12, 17}

/-- The digit set `ℬ = {0,1,8,11,13,17}`. -/
def digitsB : Finset ℤ := {0, 1, 8, 11, 13, 17}

/-- The digit set `𝒜` has six elements. -/
theorem card_digitsA : digitsA.card = 6 := by decide

/-- The digit set `ℬ` has six elements. -/
theorem card_digitsB : digitsB.card = 6 := by decide

/-- The two digit sets differ, so the two first-level supports differ and the two
measures are distinct. -/
theorem digitsA_ne_digitsB : digitsA ≠ digitsB := by decide

/-- The signed difference multisets of the two digit sets agree.  This is the
homometry of `thm:homometric-example`. -/
theorem diffMultiset_eq :
    ((digitsA ×ˢ digitsA).val.map fun p => p.1 - p.2)
      = ((digitsB ×ˢ digitsB).val.map fun p => p.1 - p.2) := by
  decide

/-- Every value is taken equally often as a difference of digits: the law of
`D - D'` is the same for the two digit sets. -/
theorem diffCount_eq (k : ℤ) :
    Multiset.count k ((digitsA ×ˢ digitsA).val.map fun p => p.1 - p.2)
      = Multiset.count k ((digitsB ×ˢ digitsB).val.map fun p => p.1 - p.2) := by
  rw [diffMultiset_eq]

/-! ### Strong separation -/

/-- The similarity attached to a digit, `S_d(x) = x/30 + d/18`. -/
noncomputable def hommap (d : ℤ) (x : ℝ) : ℝ := x / 30 + (d : ℝ) / 18

/-- Distinct digits give first-level cylinders at distance at least `1/45`: the
first-level intervals have length `1/30` while distinct left endpoints are separated by
at least `1/18`.  Hence the system satisfies the strong separation condition. -/
theorem strong_separation {d d' : ℤ} (hne : d ≠ d') {x y : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    1/45 ≤ |hommap d x - hommap d' y| := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hd : (1:ℤ) ≤ |d - d'| := Int.one_le_abs (sub_ne_zero.mpr hne)
  have hcast : (1:ℝ) ≤ |(d : ℝ) - (d' : ℝ)| := by
    have : ((1 : ℤ) : ℝ) ≤ ((|d - d'| : ℤ) : ℝ) := Int.cast_le.mpr hd
    rwa [Int.cast_abs, Int.cast_sub, Int.cast_one] at this
  rcases le_abs.mp hcast with h | h
  · exact le_abs.mpr (Or.inl (by unfold hommap; linarith))
  · exact le_abs.mpr (Or.inr (by unfold hommap; linarith))

/-! ### The common dimension -/

/-- The common dimension `t = log 6 / log 30` of the two attractors. -/
noncomputable def tHom : ℝ := Real.log 6 / Real.log 30

/-- `log 6 > 0`. -/
theorem log_six_pos : 0 < Real.log 6 := Real.log_pos (by norm_num)

/-- `log 30 > 0`. -/
theorem log_thirty_pos : 0 < Real.log 30 := Real.log_pos (by norm_num)

/-- `t ∈ (1/2, 1)`.  The lower bound is `30 < 36`, the upper bound is `6 < 30`. -/
theorem tHom_mem_Ioo : tHom ∈ Set.Ioo (1/2 : ℝ) 1 := by
  have h36 : Real.log 36 = 2 * Real.log 6 := by
    rw [show (36:ℝ) = 6 ^ (2:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlow : Real.log 30 < Real.log 36 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [h36] at hlow
  have hupp : Real.log 6 < Real.log 30 := Real.log_lt_log (by norm_num) (by norm_num)
  constructor
  · rw [tHom, lt_div_iff₀ log_thirty_pos]; linarith
  · rw [tHom, div_lt_one log_thirty_pos]; exact hupp

/-- `t` is the similarity dimension: `6·(1/30)^t = 1`. -/
theorem six_mul_rpow_tHom : 6 * ((1:ℝ)/30) ^ tHom = 1 := by
  have h30 : (30:ℝ) ^ tHom = 6 := by
    rw [tHom, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 30), mul_div_assoc', mul_comm,
      mul_div_assoc, div_self log_thirty_pos.ne', mul_one, Real.exp_log (by norm_num)]
  rw [one_div, Real.inv_rpow (by norm_num), h30]
  norm_num


/-! ### The two systems -/

/-- The digits of `𝒜`, enumerated. -/
def digitFunA : Fin 6 → ℤ := ![0, 1, 4, 10, 12, 17]

/-- The digits of `ℬ`, enumerated. -/
def digitFunB : Fin 6 → ℤ := ![0, 1, 8, 11, 13, 17]

/-- The digits of `𝒜` are non-negative. -/
theorem digitFunA_nonneg : ∀ i, 0 ≤ digitFunA i := by decide

/-- The digits of `𝒜` are at most `17`. -/
theorem digitFunA_le : ∀ i, digitFunA i ≤ 17 := by decide

/-- The digits of `ℬ` are non-negative. -/
theorem digitFunB_nonneg : ∀ i, 0 ≤ digitFunB i := by decide

/-- The digits of `ℬ` are at most `17`. -/
theorem digitFunB_le : ∀ i, digitFunB i ≤ 17 := by decide

/-- The enumeration of `𝒜` is injective. -/
theorem digitFunA_injective : Function.Injective digitFunA := by decide

/-- The enumeration of `ℬ` is injective. -/
theorem digitFunB_injective : Function.Injective digitFunB := by decide

/-- The enumeration of `𝒜` has the digit set as its range. -/
theorem range_digitFunA : Finset.image digitFunA Finset.univ = digitsA := by decide

/-- The enumeration of `ℬ` has the digit set as its range. -/
theorem range_digitFunB : Finset.image digitFunB Finset.univ = digitsB := by decide

/-- The self-similar system of `thm:homometric-example` attached to a digit set:
`S_d(x) = x/30 + d/18`, at six digits in `{0,…,17}`. -/
noncomputable def homSystem (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i) (h17 : ∀ i, d i ≤ 17) :
    System (Fin 6) where
  ratio _ := 1/30
  shift i := (d i : ℝ) / 18
  ratio_pos _ := by norm_num
  ratio_lt_one _ := by norm_num
  mapsTo i x hx := by
    obtain ⟨hx0, hx1⟩ := hx
    have hd0 : (0:ℝ) ≤ (d i : ℝ) := by exact_mod_cast h0 i
    have hd17 : (d i : ℝ) ≤ 17 := by exact_mod_cast h17 i
    constructor
    · show (0:ℝ) ≤ 1/30 * x + (d i : ℝ)/18
      linarith
    · show 1/30 * x + (d i : ℝ)/18 ≤ 1
      linarith

/-- The maps of a homometric system are the affine maps `hommap` of its digits. -/
theorem homSystem_map (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i) (h17 : ∀ i, d i ≤ 17)
    (i : Fin 6) (x : ℝ) : (homSystem d h0 h17).map i x = hommap (d i) x := by
  simp only [System.map, homSystem, hommap]
  ring

/-- The system is strongly separated on any subset of `[0,1]`, with the gap `1/45` of
`strong_separation`.  In particular it is strongly separated on its attractor. -/
theorem homSystem_stronglySeparated (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i)
    (h17 : ∀ i, d i ≤ 17) (hinj : Function.Injective d) {K : Set ℝ}
    (hK : K ⊆ Set.Icc 0 1) : (homSystem d h0 h17).StronglySeparated K (1/45) := by
  refine ⟨by norm_num, fun i j hij x hx y hy => ?_⟩
  rw [homSystem_map, homSystem_map]
  exact strong_separation (fun h => hij (hinj h)) (hK hx) (hK hy)


/-! ### The signed convolution -/

/-- The reflection `σ̃`, the image of `σ` under `x ↦ -x`. -/
noncomputable def reflect (σ : Measure ℝ) : Measure ℝ := σ.map (fun x : ℝ => -x)

/-- `σ * σ̃` is the law of the difference of two independent samples: the bridge between
the convolution `sec:obstruction` writes and the difference law the endpoint uses. -/
theorem conv_reflect_eq_map_sub (σ : Measure ℝ) [SFinite σ] :
    σ.conv (reflect σ) = (σ.prod σ).map (fun p : ℝ × ℝ => p.1 - p.2) := by
  have hneg : Measurable (fun x : ℝ => -x) := measurable_neg
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_add
  have hprod : σ.prod (reflect σ) = (σ.prod σ).map (Prod.map id (fun x : ℝ => -x)) := by
    rw [reflect]
    have h := Measure.map_prod_map σ σ measurable_id hneg
    rwa [Measure.map_id] at h
  rw [Measure.conv, hprod, Measure.map_map hadd (measurable_id.prodMap hneg)]
  rfl

end BrownianImages
