/-
`sec:renewal` of `BrownianImagesComplete.tex`: `thm:non-lattice-limit` and
`eq:g-non-lattice-limit`, by the Fourier route.

The vendored key renewal theorem
`AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real` asks for
`Nonlattice`, which `not_nonlattice_renewalLaw` refutes for the renewal law
`ϑ = ∑ p_i δ_{a_i}` of a self-similar system.  Tracing that hypothesis through the
vendored proof shows it is consumed at exactly three declarations, and in only two
forms: `charFun μ t ≠ 1` off the origin, which keeps the resolvent `(1 - charFun μ)⁻¹`
bounded on a compact annulus, and `‖charFun μ t‖ < 1` inside a dominated convergence
step, where an almost everywhere statement suffices.  `FellerNonlattice` is exactly
those two, and `ϑ` satisfies it under `eq:non-lattice` even though it satisfies neither
`Nonlattice` nor the pointwise `‖charFun F t‖ < 1`.

`FellerNonlattice` is defined in `BrownianImages/Renewal/Basic.lean` and the vendored
chain carries it directly, so this module states no vendored declaration a second time.
`Renewal/*.lean` records the change; `PLAN.md` records what it costs.

* `fellerNonlattice_of_nonlattice`: `FellerNonlattice`, the hypothesis the vendored
  chain now carries, is weaker than the `Nonlattice` it replaced.
* `System.charFun_renewalLaw`, `System.charFun_renewalLaw_eq_one_iff`: the
  characteristic function of `ϑ` and the exact description of where it takes the value
  `1`.
* `System.nonArithmetic_iff_charFun_ne_one`: `eq:non-lattice` **is** Feller's condition.
* `System.countable_norm_charFun_renewalLaw_eq_one`: the frequencies where the modulus
  returns to one form a countable set.
* `System.exists_norm_charFun_renewalLaw_eq_one`: the refutation at the analytic level,
  sharpening `not_nonlattice_renewalLaw`: for two distinct log-ratios the modulus
  returns to one off the origin, so no route asking for `‖charFun F t‖ < 1` everywhere
  can reach `thm:non-lattice-limit`.
* `KeyRenewalFourier.tendsto_integral_comp_sub_convPow_zero_of_bounded` and
  `KeyRenewalFourier.eq_tsum_integral_comp_sub_of_bounded`: the terminal term of the
  iterated renewal equation vanishes for a solution that is merely bounded at `+∞`,
  which is the case of `G` and not the case the vendored reduction covers.
* `System.tendsto_of_renewalEquation`: `eq:g-non-lattice-limit` in the vocabulary of
  `sec:renewal`.
* `phi_recursion_le`, `renewalDefect_nonneg`, `renewalDefect_pos_of_nonpos`,
  `driNorm_renewalDefect_ne_top`, `integral_renewalDefect_pos`: the two analytic facts
  `sec:renewal` proves about the renewal defect `z = G - F * G`, that it is directly
  Riemann integrable and that `∫ z > 0`.  The first rests on `z = 0` above `log(1/ρ)`
  together with `|z| ≤ e^{sw}` below it, the second on the off-diagonal blocks of the
  self-similar decomposition being non-negative, which is `phi_recursion_le`:
  `eq:phi-recursion` with those blocks kept rather than killed, hence with no separation
  hypothesis and at every scale.
* `non_lattice_limit`: `thm:non-lattice-limit`, the endpoint
  `audit_non_lattice_limit`.  `non_lattice_limit_of_driNorm` and
  `non_lattice_limit_of_integral_pos` are the intermediate forms, which isolate what the
  conclusion rests on.
-/
import BrownianImages.RenewalBridge
import BrownianImages.Recursion
import BrownianImages.Profile
import BrownianImages.AhlforsRegular

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The characteristic function of the renewal law `ϑ = ∑ p_i δ_{a_i}` of
`thm:non-lattice-limit`, in closed form. -/
theorem charFun_renewalLaw (s t : ℝ) :
    charFun (S.renewalLaw s) t
      = ∑ i, ((S.ratio i ^ s : ℝ) : ℂ) * Complex.exp (t * S.logRatio i * Complex.I) := by
  have hint : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I))
        (ENNReal.ofReal (S.ratio i ^ s) • Measure.dirac (S.logRatio i)) := by
    intro i _
    refine (integrable_smul_measure ?_ (by simp)).mpr (integrable_dirac enorm_lt_top)
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (S.ratio_pos i) s
  rw [charFun_apply_real, renewalLaw, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le, Complex.real_smul]

end System


namespace KeyRenewalFourier

/-- **The equality case of the triangle inequality for a convex combination of unit
vectors.**  If `∑ p_i z_i` has modulus one and the weights are strictly positive, then
every `z_i` equals the sum.  This is what turns a statement about the modulus of
`charFun F` into a statement about the atom phases. -/
theorem eq_sum_of_norm_sum_eq_one {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1)
    (h : ‖∑ i, (p i : ℂ) * z i‖ = 1) (i : ι) :
    z i = ∑ j, (p j : ℂ) * z j := by
  set w : ℂ := ∑ j, (p j : ℂ) * z j with hw
  set c : ℂ := (starRingEnd ℂ) w with hc
  have hcw : c * w = 1 := by
    rw [hc, Complex.conj_mul']
    norm_cast
    rw [h]; norm_num
  have hcnorm : ‖c‖ = 1 := by rw [hc, RCLike.norm_conj, h]
  have hre : ∀ j, (c * z j).re ≤ 1 := fun j => by
    calc (c * z j).re ≤ ‖c * z j‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_mul, hcnorm, hz j, one_mul]
  have hkey : ∑ j, p j * (1 - (c * z j).re) = 0 := by
    have hexp : ∑ j, p j * (c * z j).re = 1 := by
      have h1 : (c * w).re = 1 := by rw [hcw]; simp
      rw [hw, Finset.mul_sum] at h1
      rw [← h1, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : c * ((p j : ℂ) * z j) = (p j : ℂ) * (c * z j) := by ring
      rw [this]
      simp
    have : ∑ j, p j * (1 - (c * z j).re) = (∑ j, p j) - ∑ j, p j * (c * z j).re := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [this, hsum, hexp, sub_self]
  have hzero : ∀ j, (c * z j).re = 1 := by
    intro j
    have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ p j * (1 - (c * z j).re) := fun j _ =>
      mul_nonneg (hp j).le (by linarith [hre j])
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hkey j (Finset.mem_univ j)
    have hpj := (hp j).ne'
    have : (1 - (c * z j).re) = 0 := by
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hpj
      · exact h'
    linarith
  have hone : ∀ j, c * z j = 1 := by
    intro j
    have hn : ‖c * z j‖ = 1 := by rw [norm_mul, hcnorm, hz j, one_mul]
    have hsq : (c * z j).re ^ 2 + (c * z j).im ^ 2 = 1 := by
      have h2 := Complex.normSq_eq_norm_sq (c * z j)
      rw [Complex.normSq_apply, hn] at h2
      nlinarith [h2]
    have him : (c * z j).im = 0 := by nlinarith [hzero j, hsq]
    exact Complex.ext (by rw [hzero j]; simp) (by rw [him]; simp)
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcw
    exact zero_ne_one hcw
  have := (hone i).trans hcw.symm
  exact mul_left_cancel₀ hcne this



/-- The lattice `{x : t x ∈ 2πℤ}` of periods of the character `x ↦ e^{itx}`, as an
additive subgroup of the line. -/
def periodSubgroup (t : ℝ) : AddSubgroup ℝ where
  carrier := {x : ℝ | ∃ k : ℤ, t * x = k * (2 * Real.pi)}
  add_mem' := by
    rintro x y ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by push_cast; rw [mul_add, hk, hl]; ring⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨k, hk⟩
    exact ⟨-k, by push_cast; rw [mul_neg, hk]; ring⟩

/-- Membership in `periodSubgroup t`, unfolded. -/
theorem mem_periodSubgroup_iff {t x : ℝ} :
    x ∈ periodSubgroup t ↔ ∃ k : ℤ, t * x = k * (2 * Real.pi) := Iff.rfl

/-- The character `x ↦ e^{itx}` is trivial exactly on `periodSubgroup t`. -/
theorem exp_mul_I_eq_one_iff (t x : ℝ) :
    Complex.exp (t * x * Complex.I) = 1 ↔ x ∈ periodSubgroup t := by
  rw [mem_periodSubgroup_iff, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : ((t * x : ℝ) : ℂ) * Complex.I = ((n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      linear_combination hn
    have h2 := mul_right_cancel₀ Complex.I_ne_zero h
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h : ((t * x : ℝ) : ℂ) = ((k * (2 * Real.pi) : ℝ) : ℂ) := congrArg _ hk
    push_cast at h
    linear_combination h * Complex.I

/-- `periodSubgroup t` is not dense for `t ≠ 0`: its non-zero elements are at distance
at least `2π/|t|` from the origin. -/
theorem not_dense_periodSubgroup {t : ℝ} (ht : t ≠ 0) :
    ¬ Dense ((periodSubgroup t : AddSubgroup ℝ) : Set ℝ) := by
  intro hd
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hne : (Set.Ioo (0:ℝ) (2 * Real.pi / |t|)).Nonempty := by
    refine ⟨Real.pi / |t|, by positivity, ?_⟩
    rw [div_lt_div_iff₀ htpos htpos]
    nlinarith
  obtain ⟨x, hxmem, hx0, hx1⟩ := hd.exists_mem_open isOpen_Ioo hne
  obtain ⟨k, hk⟩ := hxmem
  have habs : |t * x| = |t| * x := by rw [abs_mul, abs_of_pos hx0]
  have hlt : |t| * x < 2 * Real.pi := by
    have := (lt_div_iff₀ htpos).mp hx1
    linarith
  have hkabs : |(k:ℝ)| * (2 * Real.pi) = |t| * x := by
    rw [← habs, hk, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * Real.pi)]
  have hkne : k ≠ 0 := by
    intro h0
    rw [h0] at hkabs
    simp only [Int.cast_zero, abs_zero, zero_mul] at hkabs
    nlinarith
  have h1 : (1:ℝ) ≤ |(k:ℝ)| := by
    have h2 : (1:ℤ) ≤ |k| := Int.one_le_abs hkne
    rw [← Int.cast_abs]
    exact_mod_cast h2
  nlinarith

end KeyRenewalFourier

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

open KeyRenewalFourier in
/-- If the characteristic function of `ϑ` has modulus one at `t` then all the atom
phases coincide: `e^{i t a_i} = e^{i t a_j}` for every pair. -/
theorem exp_logRatio_eq_of_norm_charFun_eq_one {s t : ℝ} (hdim : S.IsDimension s)
    (h : ‖charFun (S.renewalLaw s) t‖ = 1) (i j : ι) :
    Complex.exp (t * S.logRatio i * Complex.I)
      = Complex.exp (t * S.logRatio j * Complex.I) := by
  have hp : ∀ i, 0 < S.ratio i ^ s := fun i => Real.rpow_pos_of_pos (S.ratio_pos i) s
  have hz : ∀ i : ι, ‖Complex.exp ((t : ℂ) * (S.logRatio i : ℂ) * Complex.I)‖ = 1 := by
    intro i
    have hc : ((t : ℂ) * (S.logRatio i : ℂ) * Complex.I)
        = ((t * S.logRatio i : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hc, Complex.norm_exp_ofReal_mul_I]
  rw [S.charFun_renewalLaw] at h
  have hkey := eq_sum_of_norm_sum_eq_one hp hdim hz h
  rw [hkey i, hkey j]

open KeyRenewalFourier in
/-- `charFun F t = 1` exactly when every log-ratio is a period of the character
`x ↦ e^{itx}`.  This is Feller's arithmetic condition, in Fourier form. -/
theorem charFun_renewalLaw_eq_one_iff {s t : ℝ} (hdim : S.IsDimension s) :
    charFun (S.renewalLaw s) t = 1 ↔ ∀ i, S.logRatio i ∈ periodSubgroup t := by
  constructor
  · intro h i
    have hnorm : ‖charFun (S.renewalLaw s) t‖ = 1 := by rw [h, norm_one]
    have hp : ∀ i, 0 < S.ratio i ^ s := fun i => Real.rpow_pos_of_pos (S.ratio_pos i) s
    have hz : ∀ i : ι, ‖Complex.exp ((t : ℂ) * (S.logRatio i : ℂ) * Complex.I)‖ = 1 := by
      intro i
      have hc : ((t : ℂ) * (S.logRatio i : ℂ) * Complex.I)
          = ((t * S.logRatio i : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hc, Complex.norm_exp_ofReal_mul_I]
    rw [S.charFun_renewalLaw] at hnorm h
    have hkey := eq_sum_of_norm_sum_eq_one hp hdim hz hnorm i
    rw [← exp_mul_I_eq_one_iff]
    rw [hkey, h]
  · intro h
    rw [S.charFun_renewalLaw]
    have hone : ∀ i : ι, Complex.exp ((t : ℂ) * (S.logRatio i : ℂ) * Complex.I) = 1 :=
      fun i => (exp_mul_I_eq_one_iff t (S.logRatio i)).mpr (h i)
    simp only [hone, mul_one]
    have : ∑ i, ((S.ratio i ^ s : ℝ) : ℂ) = ((∑ i, S.ratio i ^ s : ℝ) : ℂ) := by push_cast; ring
    rw [this, hdim, Complex.ofReal_one]

open KeyRenewalFourier in
/-- `eq:non-lattice` in Fourier form: the system is non-arithmetic exactly when the
characteristic function of `ϑ` avoids the value `1` off the origin.  This is Feller's
hypothesis, and it is strictly weaker than the strongly non-lattice condition
`‖charFun ϑ t‖ < 1`, which `not_nonlattice_renewalLaw` refutes for `ϑ`. -/
theorem nonArithmetic_iff_charFun_ne_one [Nonempty ι] {s : ℝ} (hdim : S.IsDimension s) :
    S.NonArithmetic ↔ ∀ t : ℝ, t ≠ 0 → charFun (S.renewalLaw s) t ≠ 1 := by
  constructor
  · intro hna t ht hone
    have hsub : (AddSubgroup.closure (Set.range S.logRatio) : AddSubgroup ℝ)
        ≤ periodSubgroup t := by
      refine AddSubgroup.closure_le _ |>.mpr ?_
      rintro x ⟨i, rfl⟩
      exact (charFun_renewalLaw_eq_one_iff S hdim).mp hone i
    exact not_dense_periodSubgroup ht (hna.mono hsub)
  · intro hchar
    by_contra hna
    rcases AddSubgroup.dense_or_cyclic
      (AddSubgroup.closure (Set.range S.logRatio)) with hd | ⟨a, ha⟩
    · exact hna hd
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hmem : ∀ i, S.logRatio i ∈ AddSubgroup.closure ({a} : Set ℝ) := by
      intro i
      rw [← ha]
      exact AddSubgroup.subset_closure ⟨i, rfl⟩
    have hane : a ≠ 0 := by
      intro h0
      obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp (hmem i₀)
      rw [h0, smul_zero] at hn
      exact (S.logRatio_pos i₀).ne hn
    refine hchar (2 * Real.pi / a) (div_ne_zero (by positivity) hane) ?_
    refine (charFun_renewalLaw_eq_one_iff S hdim).mpr fun i => ?_
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp (hmem i)
    refine ⟨n, ?_⟩
    rw [← hn, zsmul_eq_mul]
    field_simp

/-- A non-arithmetic system has two distinct log-ratios: a single log-ratio generates a
cyclic group, which is not dense. -/
theorem exists_logRatio_ne [Nonempty ι] {s : ℝ} (hdim : S.IsDimension s)
    (hna : S.NonArithmetic) : ∃ i j, S.logRatio i ≠ S.logRatio j := by
  by_contra hcon
  have hcon' : ∀ i j, S.logRatio i = S.logRatio j := fun i j => by
    by_contra h
    exact hcon ⟨i, j, h⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have ha : 0 < S.logRatio i₀ := S.logRatio_pos i₀
  refine (nonArithmetic_iff_charFun_ne_one S hdim).mp hna (2 * Real.pi / S.logRatio i₀)
    (div_ne_zero (by positivity) ha.ne') ?_
  refine (charFun_renewalLaw_eq_one_iff S hdim).mpr fun i => ?_
  refine ⟨1, ?_⟩
  rw [hcon' i i₀]
  field_simp
  norm_num

open KeyRenewalFourier in
/-- **The frequencies at which `charFun F` has modulus one form a countable set.**
`‖charFun F t‖ = 1` forces every atom phase to coincide, hence `t (a_i - a_j) ∈ 2πℤ` for
a pair with `a_i ≠ a_j`, and that confines `t` to a lattice.  This is all that the
Fourier proof of Blackwell's theorem consumes of the strongly non-lattice condition: the
pointwise form `‖charFun ϑ t‖ < 1` for every `t ≠ 0` is false for `ϑ`, by
`exists_norm_charFun_renewalLaw_eq_one`. -/
theorem countable_norm_charFun_renewalLaw_eq_one [Nonempty ι] {s : ℝ}
    (hdim : S.IsDimension s) (hna : S.NonArithmetic) :
    {t : ℝ | ‖charFun (S.renewalLaw s) t‖ = 1}.Countable := by
  obtain ⟨i, j, hij⟩ := exists_logRatio_ne S hdim hna
  set c : ℝ := S.logRatio i - S.logRatio j with hc
  have hcne : c ≠ 0 := sub_ne_zero.mpr hij
  refine Set.Countable.mono ?_ (Set.countable_range (fun k : ℤ => (k : ℝ) * (2 * Real.pi) / c))
  intro t hnorm
  simp only [Set.mem_setOf_eq] at hnorm
  have heq := exp_logRatio_eq_of_norm_charFun_eq_one S hdim hnorm i j
  have hone : Complex.exp ((t : ℂ) * (c : ℂ) * Complex.I) = 1 := by
    have hrw : (t : ℂ) * (c : ℂ) * Complex.I
        = (t : ℂ) * (S.logRatio i : ℂ) * Complex.I
          - (t : ℂ) * (S.logRatio j : ℂ) * Complex.I := by
      rw [hc]; push_cast; ring
    rw [hrw, Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
  obtain ⟨k, hk⟩ := (exp_mul_I_eq_one_iff t c).mp hone
  exact ⟨k, by field_simp; linarith [hk]⟩

open KeyRenewalFourier in
/-- **The strongly non-lattice condition fails for `ϑ`, at the analytic level.**  If all
the log-ratios lie in one coset `a_{i₀} + dℤ` then the atom phases align at
`t = 2π/d` and `‖charFun F t‖ = 1`.  For two maps the hypothesis is automatic, so no
proof of the key renewal theorem that asks for `‖charFun F t‖ < 1` at every `t ≠ 0` can
reach `thm:non-lattice-limit`. -/
theorem norm_charFun_renewalLaw_eq_one_of_coset {s d : ℝ} (hdim : S.IsDimension s) (i₀ : ι)
    (hd : d ≠ 0) (h : ∀ i, ∃ k : ℤ, S.logRatio i = S.logRatio i₀ + k * d) :
    ‖charFun (S.renewalLaw s) (2 * Real.pi / d)‖ = 1 := by
  set t : ℝ := 2 * Real.pi / d with ht
  have hstep : ∀ i : ι, Complex.exp ((t : ℂ) * (S.logRatio i : ℂ) * Complex.I)
      = Complex.exp ((t : ℂ) * (S.logRatio i₀ : ℂ) * Complex.I) := by
    intro i
    obtain ⟨k, hk⟩ := h i
    have hmem : ((k : ℝ) * d) ∈ periodSubgroup t := by
      refine ⟨k, ?_⟩
      rw [ht]
      field_simp
    have hone := (exp_mul_I_eq_one_iff t ((k : ℝ) * d)).mpr hmem
    have hrw : (t : ℂ) * (S.logRatio i : ℂ) * Complex.I
        = (t : ℂ) * (S.logRatio i₀ : ℂ) * Complex.I
          + (t : ℂ) * (((k : ℝ) * d : ℝ) : ℂ) * Complex.I := by
      rw [hk]; push_cast; ring
    rw [hrw, Complex.exp_add, hone, mul_one]
  rw [S.charFun_renewalLaw]
  simp only [hstep]
  rw [← Finset.sum_mul]
  have hsum : ∑ i, ((S.ratio i ^ s : ℝ) : ℂ) = 1 := by
    have : ∑ i, ((S.ratio i ^ s : ℝ) : ℂ) = ((∑ i, S.ratio i ^ s : ℝ) : ℂ) := by push_cast; ring
    rw [this, hdim, Complex.ofReal_one]
  rw [hsum, one_mul]
  have hc : ((t : ℂ) * (S.logRatio i₀ : ℂ) * Complex.I)
      = ((t * S.logRatio i₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hc, Complex.norm_exp_ofReal_mul_I]

/-- The two-map case of `norm_charFun_renewalLaw_eq_one_of_coset`: for a system with two
distinct log-ratios the modulus of `charFun F` returns to `1` off the origin, whatever
the ratios.  This is the analytic form of `not_nonlattice_renewalLaw`. -/
theorem exists_norm_charFun_renewalLaw_eq_one (S : System (Fin 2)) {s : ℝ}
    (hdim : S.IsDimension s) (hne : S.logRatio 0 ≠ S.logRatio 1) :
    ∃ t : ℝ, t ≠ 0 ∧ ‖charFun (S.renewalLaw s) t‖ = 1 := by
  set d : ℝ := S.logRatio 1 - S.logRatio 0 with hd
  have hdne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  refine ⟨2 * Real.pi / d, div_ne_zero (by positivity) hdne, ?_⟩
  refine norm_charFun_renewalLaw_eq_one_of_coset S hdim 0 hdne fun i => ?_
  fin_cases i
  · exact ⟨0, by simp⟩
  · exact ⟨1, by rw [hd]; push_cast; ring⟩

end System

/-! ### Feller's non-lattice hypothesis -/

/-- `AbsorptionCutoff.Renewal.FellerNonlattice` is weaker than the vendored
`Nonlattice`, which `not_nonlattice_renewalLaw` refutes for the renewal law of a
self-similar system. -/
theorem fellerNonlattice_of_nonlattice {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : AbsorptionCutoff.Renewal.Nonlattice μ) :
    AbsorptionCutoff.Renewal.FellerNonlattice μ where
  charFun_ne_one t ht := AbsorptionCutoff.Renewal.charFun_ne_one_of_nonlattice hμ ht
  countable_norm_charFun_eq_one := by
    refine Set.Countable.mono ?_ (Set.countable_singleton (0 : ℝ))
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    by_contra h0
    exact absurd ht
      (AbsorptionCutoff.Renewal.norm_charFun_lt_one_of_nonlattice hμ h0).ne


namespace KeyRenewalFourier

section KeyRenewalTheorem

open _root_.AbsorptionCutoff.Renewal
open scoped Convolution FourierTransform

/-- **The terminal term of the iterated renewal equation vanishes**, for a solution that
is merely bounded at `+∞`.

The vendored `tendsto_integral_comp_sub_convPow_zero` asks that `h` decay at `+∞`
against an exponential tilt `β` with `∫ e^{-βz} dμ^{*n} = 1`; for a law carried by the
positive half-line that forces `β = 0`, hence `h → 0` at `+∞`, which the profile `G` does
not satisfy.  What the paper's argument uses instead is that `G` is bounded and vanishes
at `-∞`, while `μ^{*n}` escapes to `+∞`, so only two regions arise: the far left, where
`h` is small, and a left half-line whose mass dies geometrically by Chernoff. -/
theorem tendsto_integral_comp_sub_convPow_zero_of_bounded
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {θ : ℝ} (hθ : 0 < θ)
    (hlt : expTransform θ μ < 1) {h : ℝ → ℝ} {A : ℝ} (hA : ∀ u, |h u| ≤ A)
    (hbot : Filter.Tendsto h Filter.atBot (nhds 0)) (y : ℝ) :
    Filter.Tendsto (fun n => ∫ u, h (y - u) ∂convPow μ n) Filter.atTop (nhds 0) := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg (h 0)) (hA 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : (0:ℝ) < ε / 4 := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ u, u ≤ a → |h u| ≤ ε / 4 := by
    have h1 : ∀ᶠ u in Filter.atBot, |h u| ≤ ε / 4 := by
      filter_upwards [hbot (Metric.closedBall_mem_nhds (0:ℝ) hε4)] with u hu
      simpa [Real.dist_eq] using hu
    exact Filter.eventually_atBot.1 h1
  set q : ℝ≥0∞ := expTransform θ μ with hq
  have hchern : ∀ n : ℕ, ENNReal.ofReal A * convPow μ n (Set.Iic (y - a))
      ≤ ENNReal.ofReal A * ENNReal.ofReal (Real.exp (θ * (y - a))) * q ^ n := by
    intro n
    have hc := measure_le_expTransform hθ (convPow μ n) measurableSet_Iic
      (Set.Subset.refl (Set.Iic (y - a)))
    rw [expTransform_convPow] at hc
    calc ENNReal.ofReal A * convPow μ n (Set.Iic (y - a))
        ≤ ENNReal.ofReal A * (ENNReal.ofReal (Real.exp (θ * (y - a))) * q ^ n) :=
          mul_le_mul' le_rfl hc
      _ = ENNReal.ofReal A * ENNReal.ofReal (Real.exp (θ * (y - a))) * q ^ n := by ring
  have hmaj : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal A * ENNReal.ofReal (Real.exp (θ * (y - a))) * q ^ n)
      Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun n : ℕ => q ^ n) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
    simpa using ENNReal.Tendsto.const_mul hpow
      (Or.inr (by finiteness : ENNReal.ofReal A * ENNReal.ofReal (Real.exp (θ * (y - a))) ≠ ∞))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hmaj.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε4)))
  refine ⟨n₀, fun n hn => ?_⟩
  have hptwise : ∀ u : ℝ, ‖h (y - u)‖ₑ ≤ ENNReal.ofReal (ε / 4)
      + (Set.Iic (y - a)).indicator (fun _ => ENNReal.ofReal A) u := by
    intro u
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_or_gt u (y - a) with hu | hu
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hu)]
      exact le_add_left (ENNReal.ofReal_le_ofReal (hA (y - u)))
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic, not_le]; exact hu), add_zero]
      exact ENNReal.ofReal_le_ofReal (ha (y - u) (by linarith))
  have hsplit : ∫⁻ u, (ENNReal.ofReal (ε / 4)
        + (Set.Iic (y - a)).indicator (fun _ => ENNReal.ofReal A) u) ∂convPow μ n
      = ENNReal.ofReal (ε / 4) + ENNReal.ofReal A * convPow μ n (Set.Iic (y - a)) := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_indicator_const measurableSet_Iic]
  have hbound : ‖∫ u, h (y - u) ∂convPow μ n‖ₑ < ENNReal.ofReal ε := by
    calc ‖∫ u, h (y - u) ∂convPow μ n‖ₑ
        ≤ ∫⁻ u, ‖h (y - u)‖ₑ ∂convPow μ n := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ u, (ENNReal.ofReal (ε / 4)
            + (Set.Iic (y - a)).indicator (fun _ => ENNReal.ofReal A) u) ∂convPow μ n :=
          lintegral_mono hptwise
      _ = ENNReal.ofReal (ε / 4) + ENNReal.ofReal A * convPow μ n (Set.Iic (y - a)) := hsplit
      _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
          ENNReal.add_lt_add_left ENNReal.ofReal_ne_top
            (lt_of_le_of_lt (hchern n) (hn₀ n hn))
      _ = ENNReal.ofReal (ε / 4 + ε / 4) := (ENNReal.ofReal_add hε4.le hε4.le).symm
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  rw [Real.dist_eq, sub_zero]
  rw [Real.enorm_eq_ofReal_abs] at hbound
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hbound

/-- **The renewal equation is solved by the forcing's renewal series**, for a bounded
solution.  This is `eq_tsum_integral_comp_sub_of_renewalEquation` with the exponential
tilt removed: the terminal term is killed by
`tendsto_integral_comp_sub_convPow_zero_of_bounded` instead. -/
theorem eq_tsum_integral_comp_sub_of_bounded
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {θ : ℝ} (hθ : 0 < θ)
    (hlt : expTransform θ μ < 1) {h ψ : ℝ → ℝ} {A : ℝ} (hhc : Continuous h)
    (hA : ∀ u, |h u| ≤ A) (hbot : Filter.Tendsto h Filter.atBot (nhds 0))
    (hψ : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => ψ (y - s)) (convPow μ n))
    (hren : ∀ y : ℝ, h y = (∫ z, h (y - z) ∂μ) + ψ y)
    {y : ℝ} (hsum : Summable fun n => ∫ s, ψ (y - s) ∂convPow μ n) :
    h y = ∑' n, ∫ s, ψ (y - s) ∂convPow μ n := by
  have hh : ∀ (n : ℕ) (w : ℝ), Integrable (fun s => h (w - s)) (convPow μ n) := by
    intro n w
    refine Integrable.of_bound
      ((hhc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) A ?_
    exact Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hA (w - s)
  have hpart : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, ∫ s, ψ (y - s) ∂convPow μ k)
      Filter.atTop (nhds (h y)) := by
    have hAeq : ∀ n : ℕ, (∑ k ∈ Finset.range n, ∫ s, ψ (y - s) ∂convPow μ k)
        = h y - ∫ s, h (y - s) ∂convPow μ n := fun n => by
      have := eq_integral_convPow_add_sum_of_renewalEquation hh hψ hren y n
      linarith
    simp_rw [hAeq]
    simpa using (tendsto_const_nhds (x := h y) (f := Filter.atTop (α := ℕ))).sub
      (tendsto_integral_comp_sub_convPow_zero_of_bounded hθ hlt hA hbot y)
  exact (hsum.hasSum_iff_tendsto_nat.2 hpart).tsum_eq.symm

/-- **The scalar renewal limit under Feller's hypothesis, for a bounded solution.**  A
bounded continuous solution of the renewal equation `h = h ⋆ μ + ψ` that vanishes at
`-∞`, with directly Riemann integrable forcing, satisfies `h y → (∫ψ)/m`.  This is
`eq:g-non-lattice-limit` with the profile in place of `h` and the renewal defect in
place of `ψ`. -/
theorem tendsto_of_renewalEquation_of_bounded {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : FellerNonlattice μ) (hmem : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1) {h ψ : ℝ → ℝ} {A : ℝ}
    (hψc : Continuous ψ) (hψd : driNorm (fun x => ‖ψ x‖ₑ) ≠ ∞)
    (hhc : Continuous h) (hA : ∀ u, |h u| ≤ A)
    (hbot : Filter.Tendsto h Filter.atBot (nhds 0))
    (hren : ∀ y : ℝ, h y = (∫ z, h (y - z) ∂μ) + ψ y) :
    Filter.Tendsto h Filter.atTop (nhds ((∫ x : ℝ, ψ x) / (∫ x, x ∂μ))) := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_renewalMeasure_Icc_of_expTransform hμ hmem hm hθ hlt 1
  have hψd' : driNorm (fun x => ‖((ψ x : ℝ) : ℂ)‖ₑ) ≠ ∞ := by
    simpa [enorm_eq_nnnorm] using hψd
  have hψi : ∀ (n : ℕ) (w : ℝ), Integrable (fun s => ψ (w - s)) (convPow μ n) := by
    intro n w
    have := integrable_comp_sub_of_driNorm hC₀ ENNReal.ofReal_ne_top
      (Complex.continuous_ofReal.comp hψc) hψd' w n
    simpa using this.re
  have hsum : ∀ w : ℝ, Summable fun n => ∫ s, ψ (w - s) ∂convPow μ n := by
    intro w
    rw [← Complex.summable_ofReal]
    refine (summable_integral_comp_sub_of_driNorm hC₀ ENNReal.ofReal_ne_top hψd' w).congr
      fun n => ?_
    rw [integral_complex_ofReal]
  have hval : ∀ w : ℝ, h w = ∑' n, ∫ s, ψ (w - s) ∂convPow μ n := fun w =>
    eq_tsum_integral_comp_sub_of_bounded hθ hlt hhc hA hbot hψi hren (hsum w)
  exact (tendsto_tsum_integral_comp_sub_of_driNorm_real hμ hmem hm hθ hlt hψc hψd).congr
    fun w => (hval w).symm

end KeyRenewalTheorem

end KeyRenewalFourier

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- `id` is square-integrable for `ϑ`: the renewal law is carried by the finitely many
log-ratios, so it has bounded support.  This is the moment hypothesis the key renewal
theorem asks of the increment law. -/
theorem memLp_id_renewalLaw {s : ℝ} (hdim : S.IsDimension s) :
    MemLp id 2 (S.renewalLaw s) := by
  haveI := S.isProbabilityMeasure_renewalLaw hdim
  refine MemLp.of_bound (by fun_prop) (∑ j, |S.logRatio j|) ?_
  rw [ae_iff]
  set B : Set ℝ := {x : ℝ | ¬ ‖(id x : ℝ)‖ ≤ ∑ j, |S.logRatio j|} with hB
  have hmeas : MeasurableSet B := by
    rw [hB]
    simp only [id_eq, not_le]
    exact measurableSet_lt measurable_const measurable_norm
  rw [renewalLaw_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hnot : S.logRatio i ∉ B := by
    rw [hB]
    simp only [Set.mem_setOf_eq, not_not, id_eq, Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |S.logRatio j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem hnot, mul_zero]

/-- **`eq:non-lattice` gives Feller's hypothesis for `ϑ`.**  This is what
`thm:non-lattice-limit` needs of the renewal law, and what the vendored `Nonlattice`
provably is not. -/
theorem fellerNonlattice_renewalLaw [Nonempty ι] {s : ℝ} (hdim : S.IsDimension s)
    (hna : S.NonArithmetic) :
    AbsorptionCutoff.Renewal.FellerNonlattice (S.renewalLaw s) where
  charFun_ne_one := (nonArithmetic_iff_charFun_ne_one S hdim).mp hna
  countable_norm_charFun_eq_one := countable_norm_charFun_renewalLaw_eq_one S hdim hna

open _root_.AbsorptionCutoff.Renewal in
/-- **`eq:g-non-lattice-limit`, for the renewal law of a non-arithmetic system.**  The
renewal series of a continuous, directly Riemann integrable forcing `z` converges to
`m⁻¹ ∫ z`, with `m = ∑ p_i a_i` the renewal mean.  This is Feller's key renewal theorem
at the increment law `ϑ = ∑ p_i δ_{a_i}` of `thm:non-lattice-limit`: the vendored
theorem's `Nonlattice` hypothesis is false for `ϑ`, and what stands in its place is
`FellerNonlattice`, which `eq:non-lattice` supplies.

What separates this from `thm:non-lattice-limit` itself is the identification of `G`
with its own renewal series, `G = ∑_n ϑ^{*n} * z` for `z = G - ϑ * G`, which is the
first half of the proof in the tex. -/
theorem tendsto_tsum_integral_renewalLaw [Nonempty ι] {s : ℝ} (hdim : S.IsDimension s)
    (hna : S.NonArithmetic) {z : ℝ → ℝ} (hzc : Continuous z)
    (hzd : AbsorptionCutoff.Renewal.driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto
      (fun y : ℝ => ∑' n : ℕ,
        ∫ u, z (y - u) ∂(AbsorptionCutoff.Renewal.convPow (S.renewalLaw s) n))
      Filter.atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, z x)) := by
  haveI := S.isProbabilityMeasure_renewalLaw hdim
  obtain ⟨θ, hθ, hlt⟩ := S.exists_expTransform_lt_one hdim
  have hm : 0 < ∫ x, x ∂(S.renewalLaw s) := by
    rw [S.integral_id_renewalLaw]
    exact S.renewalMean_pos s
  have hval : ((∫ x : ℝ, z x) / ∫ x, x ∂(S.renewalLaw s))
      = (S.renewalMean s)⁻¹ * ∫ x : ℝ, z x := by
    rw [S.integral_id_renewalLaw, div_eq_inv_mul]
  rw [← hval]
  exact tendsto_tsum_integral_comp_sub_of_driNorm_real
    (S.fellerNonlattice_renewalLaw hdim hna) (S.memLp_id_renewalLaw hdim) hm hθ hlt hzc hzd

/-- The renewal convolution `ϑ * g` of `thm:non-lattice-limit` is the integral against
the renewal law: `(F * g)(y) = ∫ g(y - u) dF(u)`.  This is the bridge between the
paper's `∑ p_i g(w - a_i)` and the shape the key renewal theorem is stated in. -/
theorem integral_comp_sub_renewalLaw (s y : ℝ) (f : ℝ → ℝ) :
    ∫ u, f (y - u) ∂(S.renewalLaw s) = S.renewalConv s f y := by
  have hint : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun u : ℝ => f (y - u))
        (ENNReal.ofReal (S.ratio i ^ s) • Measure.dirac (S.logRatio i)) := by
    intro i _
    refine (integrable_smul_measure ?_ (by simp)).mpr (integrable_dirac enorm_lt_top)
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (S.ratio_pos i) s
  rw [renewalConv, renewalLaw, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le]

open KeyRenewalFourier in
/-- **`eq:g-non-lattice-limit` for a non-arithmetic system**, in the vocabulary of
`sec:renewal`: a bounded continuous solution of the renewal recursion `h = F * h + z`
that vanishes at `-∞`, with directly Riemann integrable forcing `z`, converges to
`m⁻¹ ∫ z`.  Instantiated at `h = G` and `z = G - F * G` this is
`thm:non-lattice-limit`. -/
theorem tendsto_of_renewalEquation [Nonempty ι] {s : ℝ} (hdim : S.IsDimension s)
    (hna : S.NonArithmetic) {h z : ℝ → ℝ} {A : ℝ} (hzc : Continuous z)
    (hzd : AbsorptionCutoff.Renewal.driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (hhc : Continuous h)
    (hA : ∀ u, |h u| ≤ A) (hbot : Filter.Tendsto h Filter.atBot (𝓝 0))
    (hren : ∀ y : ℝ, h y = S.renewalConv s h y + z y) :
    Filter.Tendsto h Filter.atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, z x)) := by
  haveI := S.isProbabilityMeasure_renewalLaw hdim
  obtain ⟨θ, hθ, hlt⟩ := S.exists_expTransform_lt_one hdim
  have hm : 0 < ∫ x, x ∂(S.renewalLaw s) := by
    rw [S.integral_id_renewalLaw]
    exact S.renewalMean_pos s
  have hval : ((∫ x : ℝ, z x) / ∫ x, x ∂(S.renewalLaw s))
      = (S.renewalMean s)⁻¹ * ∫ x : ℝ, z x := by
    rw [S.integral_id_renewalLaw, div_eq_inv_mul]
  rw [← hval]
  refine tendsto_of_renewalEquation_of_bounded (S.fellerNonlattice_renewalLaw hdim hna)
    (S.memLp_id_renewalLaw hdim) hm hθ hlt hzc hzd hhc hA hbot fun y => ?_
  rw [S.integral_comp_sub_renewalLaw]
  exact hren y

end System

section RenewalDefect

open _root_.AbsorptionCutoff.Renewal

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- `eq:g-recursion` says exactly that the renewal defect `z = G - F * G` vanishes above
`log(1/ρ)`. -/
theorem renewalDefect_eq_zero_of_lt {K : Set ℝ} {ρ s : ℝ} (hsep : S.StronglySeparated K ρ)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) {w : ℝ} (hw : Real.log ρ⁻¹ < w) :
    S.renewalDefect s μ w = 0 := by
  rw [System.renewalDefect, System.renewalConv, ← g_recursion S hsep hμ hw, sub_self]

/-- `|z(w)| ≤ e^{sw}`: the trivial bound `Φ ≤ 1` applied to both terms, the second one
through `∑ p_i = 1`. -/
theorem abs_renewalDefect_le {s : ℝ} (hs : 0 ≤ s) (hdim : S.IsDimension s) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (w : ℝ) : |S.renewalDefect s μ w| ≤ Real.exp (s * w) := by
  have hG : G s μ w ≤ Real.exp (s * w) := G_le_exp hs le_rfl
  have hGnn : 0 ≤ G s μ w := G_nonneg w
  have hconv_nn : 0 ≤ S.renewalConv s (G s μ) w :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (Real.rpow_pos_of_pos (S.ratio_pos i) s).le (G_nonneg _)
  have hconv : S.renewalConv s (G s μ) w ≤ Real.exp (s * w) := by
    have hterm : ∀ i ∈ (Finset.univ : Finset ι), S.ratio i ^ s * G s μ (w - S.logRatio i)
        ≤ S.ratio i ^ s * Real.exp (s * w) := by
      intro i _
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (S.ratio_pos i) s).le
      exact G_le_exp hs (by linarith [S.logRatio_pos i])
    calc S.renewalConv s (G s μ) w ≤ ∑ i, S.ratio i ^ s * Real.exp (s * w) :=
          Finset.sum_le_sum hterm
      _ = (∑ i, S.ratio i ^ s) * Real.exp (s * w) := by rw [Finset.sum_mul]
      _ = Real.exp (s * w) := by rw [hdim, one_mul]
  rw [System.renewalDefect, abs_sub_le_iff]
  constructor <;> linarith

/-- **The renewal defect is directly Riemann integrable.**  It vanishes above
`log(1/ρ)` by `eq:g-recursion` and is dominated by `e^{sw}` below it, so the cell
suprema of `eq:nd-dri-definition` form a geometric series.  This is the first of the two
analytic facts `sec:renewal` proves about `z`. -/
theorem driNorm_renewalDefect_ne_top {K : Set ℝ} {ρ s : ℝ} (hs : 0 < s)
    (hsep : S.StronglySeparated K ρ) (hdim : S.IsDimension s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) :
    driNorm (fun x => ‖S.renewalDefect s μ x‖ₑ) ≠ ∞ := by
  haveI := hμ.isProbabilityMeasure
  set L : ℝ := Real.log ρ⁻¹ with hL
  set N : ℤ := ⌈L⌉ + 1 with hN
  have hNL : L < (N : ℝ) := by
    rw [hN]; push_cast; linarith [Int.le_ceil L]
  set a : ℤ → ℝ := fun k => if k < N then Real.exp (s * ((k : ℝ) + 1)) else 0 with ha
  have hanonneg : ∀ k, 0 ≤ a k := by
    intro k
    rw [ha]
    dsimp only
    split
    · positivity
    · exact le_rfl
  have hcell : ∀ k : ℤ,
      cellSup (fun x => ‖S.renewalDefect s μ x‖ₑ) k ≤ ENNReal.ofReal (a k) := by
    intro k
    refine iSup₂_le fun x hx => ?_
    rw [Set.mem_Icc] at hx
    rw [ha]
    dsimp only
    by_cases hk : k < N
    · rw [if_pos hk, Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      calc |S.renewalDefect s μ x| ≤ Real.exp (s * x) := abs_renewalDefect_le S hs.le hdim x
        _ ≤ Real.exp (s * ((k : ℝ) + 1)) := Real.exp_le_exp.mpr (by nlinarith [hx.2])
    · rw [if_neg hk]
      have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast not_lt.mp hk
      have hxL : L < x := lt_of_lt_of_le hNL (le_trans hkN hx.1)
      rw [renewalDefect_eq_zero_of_lt S hsep hμ hxL]
      simp
  have hsummable : Summable a := by
    refine Summable.of_nat_of_neg ?_ ?_
    · refine summable_of_ne_finset_zero (s := Finset.range (N.toNat + 1)) fun n hn => ?_
      rw [ha]
      dsimp only
      refine if_neg fun hlt => hn ?_
      rw [Finset.mem_range]
      omega
    · have hgeo : Summable fun n : ℕ => Real.exp s * Real.exp (-s) ^ n := by
        refine Summable.mul_left _ (summable_geometric_of_lt_one (Real.exp_pos _).le ?_)
        exact Real.exp_lt_one_iff.mpr (by linarith)
      refine Summable.of_nonneg_of_le (fun n => hanonneg _) (fun n => ?_) hgeo
      rw [ha]
      dsimp only
      have hval : Real.exp s * Real.exp (-s) ^ n = Real.exp (s * ((-(n : ℤ) : ℝ) + 1)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hval]
      by_cases hk : (-(n : ℤ)) < N
      · rw [if_pos hk]
        refine le_of_eq (congrArg Real.exp ?_)
        push_cast
        ring
      · rw [if_neg hk]
        positivity
  rw [driNorm_def]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hcell)
  rw [← ENNReal.ofReal_tsum_of_nonneg hanonneg hsummable]
  exact ENNReal.ofReal_ne_top

/-- `Φ(δ) = 1` for `δ ≥ 1`: the measure sits on `[0,1]`, so every pair of points is at
distance at most one. -/
theorem phi_eq_one_of_one_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0) {δ : ℝ} (hδ : 1 ≤ δ) : Phi μ δ = 1 := by
  have hcompl : {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}ᶜ
      ⊆ ((Set.Icc (0:ℝ) 1)ᶜ ×ˢ (Set.univ : Set ℝ))
        ∪ ((Set.univ : Set ℝ) ×ˢ (Set.Icc (0:ℝ) 1)ᶜ) := by
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hp
    by_cases h1 : p.1 ∈ Set.Icc (0:ℝ) 1
    · by_cases h2 : p.2 ∈ Set.Icc (0:ℝ) 1
      · exfalso
        obtain ⟨ha, hb⟩ := h1
        obtain ⟨hc, hd⟩ := h2
        have : |p.1 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith
      · exact Or.inr (Set.mem_prod.mpr ⟨Set.mem_univ _, h2⟩)
    · exact Or.inl (Set.mem_prod.mpr ⟨h1, Set.mem_univ _⟩)
  have hnull : (μ.prod μ) ({p : ℝ × ℝ | |p.1 - p.2| ≤ δ}ᶜ) = 0 := by
    refine measure_mono_null hcompl (measure_union_null ?_ ?_)
    · rw [Measure.prod_prod, hsupp, zero_mul]
    · rw [Measure.prod_prod, hsupp, mul_zero]
  rw [Phi, (prob_compl_eq_zero_iff (measurableSet_phiSet δ)).mp hnull, ENNReal.toReal_one]

/-- **The self-similar decomposition dominates its diagonal blocks**, at every scale:
`∑ r_i^{2s} Φ(δ/r_i) ≤ Φ(δ)`.  This is `eq:phi-recursion` with the off-diagonal blocks
kept rather than killed, so no separation hypothesis and no restriction on `δ` are
needed. -/
theorem phi_recursion_le {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (δ : ℝ) : ∑ i, S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i) ≤ Phi μ δ := by
  haveI := hμ.isProbabilityMeasure
  have hphi : ∀ δ' : ℝ, Phi μ δ' = (∫⁻ x, μ (Metric.closedBall x δ') ∂μ).toReal := by
    intro δ'; rw [Phi, phi_prod_eq]
  have hfin : ∀ δ' : ℝ, (∫⁻ x, μ (Metric.closedBall x δ') ∂μ) ≠ ⊤ := by
    intro δ'
    rw [← phi_prod_eq]
    exact measure_ne_top _ _
  have hpt : ∀ (i : ι) (x : ℝ),
      ENNReal.ofReal (S.ratio i ^ s) * μ (Metric.closedBall x (δ / S.ratio i))
        ≤ μ (Metric.closedBall (S.map i x) δ) := by
    intro i x
    have hpre : S.map i ⁻¹' Metric.closedBall (S.map i x) δ
        = Metric.closedBall x (δ / S.ratio i) := by
      ext y
      simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq, System.map]
      rw [show S.ratio i * y + S.shift i - (S.ratio i * x + S.shift i)
            = (y - x) * S.ratio i from by ring,
        abs_mul, abs_of_pos (S.ratio_pos i), le_div_iff₀ (S.ratio_pos i)]
    calc ENNReal.ofReal (S.ratio i ^ s) * μ (Metric.closedBall x (δ / S.ratio i))
        = ENNReal.ofReal (S.ratio i ^ s)
            * μ (S.map i ⁻¹' Metric.closedBall (S.map i x) δ) := by rw [hpre]
      _ ≤ ∑ j, ENNReal.ofReal (S.ratio j ^ s)
            * μ (S.map j ⁻¹' Metric.closedBall (S.map i x) δ) :=
          Finset.single_le_sum
            (f := fun j => ENNReal.ofReal (S.ratio j ^ s)
              * μ (S.map j ⁻¹' Metric.closedBall (S.map i x) δ))
            (fun j _ => bot_le) (Finset.mem_univ i)
      _ = μ (Metric.closedBall (S.map i x) δ) :=
          (hμ.measure_eq_sum S measurableSet_closedBall).symm
  have hkey : (∑ i, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio i ^ s) *
      ∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ)
      ≤ ∫⁻ x, μ (Metric.closedBall x δ) ∂μ := by
    rw [hμ.lintegral_eq_sum S (measurable_measure_closedBall μ δ)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    rw [← lintegral_const_mul _ (measurable_measure_closedBall μ (δ / S.ratio i))]
    exact lintegral_mono fun x => hpt i x
  have hne : ∀ i : ι, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio i ^ s) *
      (∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ) ≠ ⊤ :=
    fun i => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hfin _)
  have hconv : ∑ i, S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i)
      = (∑ i, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio i ^ s) *
          ∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => hne i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hphi (δ / S.ratio i), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le]
    congr 1
    rw [← Real.rpow_add (S.ratio_pos i), two_mul]
  rw [hconv, hphi δ]
  exact ENNReal.toReal_mono (hfin δ) hkey

/-- The renewal defect in terms of `Φ`: `z(w) = e^{sw}(Φ(δ) - ∑ r_i^{2s} Φ(δ/r_i))` at
`δ = e^{-w}`.  This is the substitution `eq:g-definition` performs in the proof of
`eq:g-recursion`, kept as an identity rather than combined with the recursion. -/
theorem renewalDefect_eq {s : ℝ} {μ : Measure ℝ} (w : ℝ) :
    S.renewalDefect s μ w
      = Real.exp (s * w) * (Phi μ (Real.exp (-w))
          - ∑ i, S.ratio i ^ (2 * s) * Phi μ (Real.exp (-w) / S.ratio i)) := by
  have hterm : ∀ i : ι, S.ratio i ^ s * G s μ (w - S.logRatio i)
      = Real.exp (s * w) * (S.ratio i ^ (2 * s) * Phi μ (Real.exp (-w) / S.ratio i)) := by
    intro i
    have hlog : S.logRatio i = -Real.log (S.ratio i) := by
      rw [System.logRatio, Real.log_inv]
    have hri : Real.exp (-(w - S.logRatio i)) = Real.exp (-w) / S.ratio i := by
      rw [hlog, show -(w - -Real.log (S.ratio i)) = -w - Real.log (S.ratio i) from by ring,
        Real.exp_sub, Real.exp_log (S.ratio_pos i)]
    have hexp : Real.exp (s * (w - S.logRatio i)) = Real.exp (s * w) * S.ratio i ^ s := by
      rw [hlog,
        show s * (w - -Real.log (S.ratio i)) = s * w + Real.log (S.ratio i) * s from by ring,
        Real.exp_add, ← Real.rpow_def_of_pos (S.ratio_pos i)]
    have h2s : S.ratio i ^ (2 * s) = S.ratio i ^ s * S.ratio i ^ s := by
      rw [two_mul, Real.rpow_add (S.ratio_pos i)]
    rw [G, hri, hexp, h2s]
    ring
  rw [System.renewalDefect, System.renewalConv]
  simp only [hterm]
  rw [← Finset.mul_sum, G]
  ring

/-- **The renewal defect is non-negative**, at every scale: `phi_recursion_le`. -/
theorem renewalDefect_nonneg {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (w : ℝ) : 0 ≤ S.renewalDefect s μ w := by
  rw [renewalDefect_eq]
  exact mul_nonneg (Real.exp_pos _).le
    (by linarith [phi_recursion_le S hμ (Real.exp (-w))])

/-- **The renewal defect is strictly positive below the origin**, where
`z(w) = e^{sw}(1 - ∑ r_i^{2s})`: at `δ ≥ 1` every `Φ` in sight is `1`, and
`∑ r_i^{2s} < ∑ r_i^s = 1`. -/
theorem renewalDefect_pos_of_nonpos [Nonempty ι] {K : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) {w : ℝ}
    (hw : w ≤ 0) : 0 < S.renewalDefect s μ w := by
  haveI := hμ.isProbabilityMeasure
  have hsupp := hμ.support_Icc
  have hδ : (1:ℝ) ≤ Real.exp (-w) := Real.one_le_exp (by linarith)
  have hΦ : Phi μ (Real.exp (-w)) = 1 := phi_eq_one_of_one_le hsupp hδ
  have hΦi : ∀ i : ι, Phi μ (Real.exp (-w) / S.ratio i) = 1 := by
    intro i
    refine phi_eq_one_of_one_le hsupp ?_
    have hr := S.ratio_pos i
    have hr1 := S.ratio_lt_one i
    rw [le_div_iff₀ hr]
    nlinarith
  have hsum : ∑ i, S.ratio i ^ (2 * s) < 1 := by
    have hlt : ∀ i ∈ (Finset.univ : Finset ι), S.ratio i ^ (2 * s) < S.ratio i ^ s :=
      fun i _ => Real.rpow_lt_rpow_of_exponent_gt (S.ratio_pos i) (S.ratio_lt_one i)
        (by linarith)
    calc ∑ i, S.ratio i ^ (2 * s) < ∑ i, S.ratio i ^ s :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
      _ = 1 := hdim
  rw [renewalDefect_eq]
  refine mul_pos (Real.exp_pos _) ?_
  rw [hΦ]
  simp only [hΦi, mul_one]
  linarith

/-- The renewal defect is integrable: `driNorm_renewalDefect_ne_top` dominates the
`L¹` norm. -/
theorem integrable_renewalDefect {K : Set ℝ} {ρ s : ℝ} (hs : 0 < s)
    (hsep : S.StronglySeparated K ρ) (hdim : S.IsDimension s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) : Integrable (S.renewalDefect s μ) := by
  haveI := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs hsep hμ
  have hGc : Continuous (G s μ) := continuous_G hs hA
  have hzc : Continuous (S.renewalDefect s μ) := by
    refine hGc.sub (continuous_finsetSum _ fun i _ => ?_)
    exact continuous_const.mul (hGc.comp (continuous_id.sub continuous_const))
  refine ⟨hzc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (lintegral_le_driNorm _)
    (lt_top_iff_ne_top.mpr (driNorm_renewalDefect_ne_top S hs hsep hdim hμ))

/-- **`∫ z > 0`**, the second analytic fact `sec:renewal` proves about the renewal
defect: `z ≥ 0` everywhere and `z > 0` on the whole half-line `w ≤ 0`. -/
theorem integral_renewalDefect_pos [Nonempty ι] {K : Set ℝ} {ρ s : ℝ} (hs : 0 < s)
    (hsep : S.StronglySeparated K ρ) (hdim : S.IsDimension s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) : 0 < ∫ x : ℝ, S.renewalDefect s μ x := by
  rw [integral_pos_iff_support_of_nonneg (fun x => renewalDefect_nonneg S hμ x)
    (integrable_renewalDefect S hs hsep hdim hμ)]
  have hsub : Set.Iic (0:ℝ) ⊆ Function.support (S.renewalDefect s μ) := fun w hw =>
    ne_of_gt (renewalDefect_pos_of_nonpos S hs hdim hμ hw)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Iic]
  exact ENNReal.zero_lt_top

end RenewalDefect

/-- **`thm:non-lattice-limit`, reduced to two analytic facts about the renewal defect.**
Everything the paper's proof needs of the ambient set-up is discharged here: `G` is
continuous and bounded by `eq:phi-frostman`, it vanishes at `-∞` by `Φ ≤ 1`, the renewal
recursion `eq:g-recursion` is the definition of `z = G - ϑ * G`, and `ϑ` satisfies
Feller's hypothesis by `eq:non-lattice`.  What is assumed is exactly what `sec:renewal`
proves about `z` and nothing else: that `z` is directly Riemann integrable, and that its
integral is strictly positive.  The first rests on `z = 0` above `log(1/ρ)` together with
`|z| ≤ C e^{sw}` below it, the second on the off-diagonal blocks of the self-similar
decomposition being non-negative. -/
theorem non_lattice_limit_of_driNorm {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hsep : S.StronglySeparated K ρ)
    (hdim : S.IsDimension s) (hna : S.NonArithmetic)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hzd : AbsorptionCutoff.Renewal.driNorm
      (fun x => ‖S.renewalDefect s μ x‖ₑ) ≠ ∞)
    (hzpos : 0 < ∫ x : ℝ, S.renewalDefect s μ x) :
    0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
      Filter.Tendsto (G s μ) Filter.atTop
        (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)) := by
  haveI := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0 hsep hμ
  have hGc : Continuous (G s μ) := continuous_G hs0 hA
  have hzc : Continuous (S.renewalDefect s μ) := by
    refine hGc.sub (continuous_finsetSum _ fun i _ => ?_)
    exact continuous_const.mul (hGc.comp (continuous_id.sub continuous_const))
  have hGbdd : ∀ u, |G s μ u| ≤ A := fun u => abs_G_le hs0 hA u
  have hbot : Filter.Tendsto (G s μ) Filter.atBot (𝓝 0) := by
    have hexp : Filter.Tendsto (fun w : ℝ => Real.exp (s * w)) Filter.atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atBot hs0 Filter.tendsto_id)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
      (fun w => G_nonneg w) (fun w => G_le_exp hs0.le le_rfl)
  refine ⟨mul_pos (inv_pos.mpr (S.renewalMean_pos s)) hzpos, ?_⟩
  refine S.tendsto_of_renewalEquation hdim hna hzc hzd hGc hGbdd hbot fun y => ?_
  rw [System.renewalDefect]
  ring

/-- **`thm:non-lattice-limit`, reduced to the positivity of `∫ z`.**  Direct Riemann
integrability of the renewal defect is `driNorm_renewalDefect_ne_top`, so the only input
`eq:g-non-lattice-limit` still waits on is that its integral is strictly positive, which
in `sec:renewal` comes from the off-diagonal blocks of the self-similar decomposition
being non-negative together with `z(w) = e^{sw}(1 - ∑ r_i^{2s})` below the origin. -/
theorem non_lattice_limit_of_integral_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : System ι) {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hsep : S.StronglySeparated K ρ)
    (hdim : S.IsDimension s) (hna : S.NonArithmetic)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hzpos : 0 < ∫ x : ℝ, S.renewalDefect s μ x) :
    0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
      Filter.Tendsto (G s μ) Filter.atTop
        (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)) :=
  non_lattice_limit_of_driNorm S hs0 hsep hdim hna hμ
    (driNorm_renewalDefect_ne_top S hs0 hsep hdim hμ) hzpos

set_option linter.unusedVariables false in
/-- **`thm:non-lattice-limit`, `eq:g-non-lattice-limit`.**  In the non-arithmetic case
the normalised profile converges to `m⁻¹ ∫ z`, which is finite and strictly positive,
where `m = ∑ p_i a_i` is the renewal mean and `z = G - F * G` the renewal defect.

The vendored key renewal theorem does not apply: `not_nonlattice_renewalLaw` refutes its
`Nonlattice` hypothesis for `ϑ`, and `exists_norm_charFun_renewalLaw_eq_one` refutes even
the analytic condition `‖charFun ϑ t‖ < 1` behind it.  What replaces it is
`FellerNonlattice`, which is what the Fourier proof actually consumes and what
`eq:non-lattice` supplies. -/
theorem non_lattice_limit {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
    (hdim : S.IsDimension s) (hna : S.NonArithmetic)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
      Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)) :=
  non_lattice_limit_of_integral_pos S hs0 hsep hdim hna hμ
    (integral_renewalDefect_pos S hs0 hsep hdim hμ)

end BrownianImages
