module

/-
`eq:lattice-periodisation` of `sec:renewal`: the periodisation
`f̃(t) = (ℓ/m) ∑_{k∈ℤ} z(t + kℓ)` of an exponentially decaying forcing `z`, the limit in
the lattice case of the key renewal theorem of `sec:renewal-equation`, its identification
with any periodic limit of a solution of the renewal equation, and the explicit periodic
limit `G̃` of the lattice branch of `thm:renewal-limits`, with `thm:lattice-nonconvergence`
for it and the lattice branch of `thm:profile-asymptotics` with the limit
`H̃_μ^s = T G̃` of `sec:smoothing`.

`LatticeProfile` gives a continuous positive `ℓ`-periodic `g` with `G - g → 0`, from the
finite-delay renewal theorem.  Along a lattice `t + ℓℤ` the renewal equation telescopes
(`LatticeNonconstancy`), so the symmetric partial sums of `z(t + kℓ)` converge to
`g(t) ∑ p_i n_i = g(t) m/ℓ`; the exponential tails of `z` make the series summable, so
they also converge to its sum.  Hence `g = G̃`, and the continuity, positivity and
non-constancy of `g` are those of `G̃`.

* `summable_int_of_abs_le_exp_neg_mul_abs`: an exponentially decaying sequence over `ℤ`
  is summable.
* `tendsto_sum_range_sub_of_hasSum`: the symmetric partial sums of a summable series
  over `ℤ` converge to its sum.
* `summable_translates_of_exp_decay`: the lattice translates of an exponentially decaying
  function are summable.
* `System.periodisation`: `f̃`, the periodisation of a forcing.
* `System.renewalMean_eq_of_lattice`: `m = ℓ ∑ p_i n_i` for a lattice span `ℓ`.
* `System.hasSum_periodisation`: the series converges, to `(m/ℓ) f̃`.
* `System.eq_periodisation_of_periodic_limit`: every periodic limit of a solution of the
  renewal equation vanishing at `-∞` is `f̃`.
* `System.latticePeriodisation`: `eq:lattice-periodisation`, `G̃ = f̃` at `z = G - ϑ * G`.
* `System.IsNatural.summable_renewalDefect_lattice`,
  `System.IsNatural.hasSum_latticePeriodisation`: the series converges, to `(m/ℓ) G̃`.
* `System.IsNatural.eq_latticePeriodisation_of_periodic_limit`: every periodic limit of
  `G` is `G̃`.
* `System.IsNatural.lattice_periodisation_limit`: the lattice branch of
  `thm:renewal-limits`.
* `System.IsNatural.latticePeriodisation_nonconstant`: `thm:lattice-nonconvergence`.
* `System.IsNatural.smoothed_latticePeriodisation`: `H̃_μ^s = T G̃` of `sec:smoothing`,
  continuous, `ℓ/2`-periodic, positive and non-constant, with `H_μ^s - H̃_μ^s → 0`.
* `lattice_profile_asymptotics_nonconstant`: the lattice branch of
  `thm:profile-asymptotics`.
-/
public import BrownianImages.LatticeNonconstancy

@[expose] public section

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Series over `ℤ` -/

/-- A sequence over `ℤ` bounded by `C e^{-a|k|}` with `a > 0` is summable. -/
theorem summable_int_of_abs_le_exp_neg_mul_abs {f : ℤ → ℝ} {C a : ℝ} (ha : 0 < a)
    (hf : ∀ k : ℤ, |f k| ≤ C * Real.exp (-a * |(k : ℝ)|)) : Summable f := by
  have hgeom : Summable fun n : ℕ => C * Real.exp ((n : ℝ) * (-a)) :=
    (Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left C
  refine Summable.of_nat_of_neg (Summable.of_norm_bounded hgeom fun n => ?_)
    (Summable.of_norm_bounded hgeom fun n => ?_)
  · rw [Real.norm_eq_abs]
    refine (hf n).trans_eq ?_
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    ring_nf
  · rw [Real.norm_eq_abs]
    refine (hf (-n)).trans_eq ?_
    rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    ring_nf

/-- The symmetric partial sums `∑_{|k|≤N} f(k)` of a summable series over `ℤ` converge to
its sum. -/
theorem tendsto_sum_range_sub_of_hasSum {f : ℤ → ℝ} {a : ℝ} (hf : HasSum f a) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), f ((k : ℤ) - N)) atTop (𝓝 a) := by
  have hinj : ∀ N : ℕ, Function.Injective (fun k : ℕ => (k : ℤ) - N) := fun N k₁ k₂ h => by
    simpa using h
  let F : ℕ → Finset ℤ := fun N => (Finset.range (2 * N + 1)).map ⟨_, hinj N⟩
  have hF : Tendsto F atTop atTop := by
    refine tendsto_atTop_atTop.2 fun t => ⟨t.sup Int.natAbs, fun N hN b hb => ?_⟩
    have hb' : b.natAbs ≤ N := (Finset.le_sup hb).trans hN
    simp only [F, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    exact ⟨(b + N).toNat, by omega, by omega⟩
  have hlim : Tendsto (fun N => ∑ b ∈ F N, f b) atTop (𝓝 a) :=
    (hf : Tendsto (fun t : Finset ℤ => ∑ b ∈ t, f b) atTop (𝓝 a)).comp hF
  refine hlim.congr fun N => ?_
  simp only [F, Finset.sum_map, Function.Embedding.coeFn_mk]

/-- The lattice translates `z(t + kℓ)` of a function with two-sided exponential tails are
summable over `k ∈ ℤ`. -/
theorem summable_translates_of_exp_decay {z : ℝ → ℝ} {C c h : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-c * |x|)) (t : ℝ) :
    Summable fun k : ℤ => z (t + k * h) := by
  have hC : 0 ≤ C := by
    have h0 := hzb 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h0
    exact (abs_nonneg _).trans h0
  refine summable_int_of_abs_le_exp_neg_mul_abs (C := C * Real.exp (c * |t|))
    (mul_pos hc hh) fun k => (hzb _).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have h1 : |(k : ℝ) * h| - |t| ≤ |t + k * h| := by
    have := abs_sub_abs_le_abs_sub ((k : ℝ) * h) (-t)
    rwa [abs_neg, sub_neg_eq_add, add_comm] at this
  rw [abs_mul, abs_of_pos hh] at h1
  nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-! ### The periodisation of a forcing -/

/-- **`eq:lattice-periodisation`** for a general forcing: the periodisation
`f̃(t) = (ℓ/m) ∑_{k∈ℤ} z(t + kℓ)`, the limit in the lattice case of the key renewal theorem
of `sec:renewal-equation`, with `m = ∑ p_i α_i` the renewal mean.  The series converges
for an exponentially decaying `z` by `hasSum_periodisation`. -/
def periodisation (s h : ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  h / S.renewalMean s * ∑' k : ℤ, z (t + k * h)

/-- A lattice span `ℓ` with `α_i = n_i ℓ` gives `m = ℓ ∑ p_i n_i`. -/
theorem renewalMean_eq_of_lattice (s : ℝ) {h : ℝ} (n : ι → ℕ)
    (hn : ∀ i, S.logRatio i = n i * h) :
    S.renewalMean s = h * ∑ i, S.ratio i ^ s * n i := by
  simp only [renewalMean, hn, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

variable [Nonempty ι]

/-- The series of the periodisation converges: `∑_{k∈ℤ} z(t + kℓ)` has sum `(m/ℓ) f̃(t)`. -/
theorem hasSum_periodisation {s h : ℝ} (hh : 0 < h) {z : ℝ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-c * |x|)) (t : ℝ) :
    HasSum (fun k : ℤ => z (t + k * h)) (S.renewalMean s / h * S.periodisation s h z t) := by
  have hsum := summable_translates_of_exp_decay hh hc hzb t
  convert hsum.hasSum using 1
  unfold periodisation
  have := S.renewalMean_pos s
  field_simp

/-- Every `ℓ`-periodic limit of a solution `f` of the renewal equation `f = ϑ * f + z`
vanishing at `-∞` is the periodisation `f̃` of its forcing: the symmetric partial sums of
the series converge both to its sum and, by the telescoped renewal equation, to
`g(t) ∑ p_i n_i = g(t) m/ℓ`. -/
theorem eq_periodisation_of_periodic_limit {s h : ℝ} (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {f z : ℝ → ℝ} {C c : ℝ} (hbot : Tendsto f atBot (𝓝 0)) (hc : 0 < c)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-c * |x|))
    (hren : ∀ x, f x = S.renewalConv s f x + z x)
    {g : ℝ → ℝ} (hgp : Function.Periodic g h)
    (hg : Tendsto (fun w => f w - g w) atTop (𝓝 0)) (t : ℝ) :
    g t = S.periodisation s h z t := by
  choose n hn using S.exists_nat_mul_of_lattice hh hlat
  have hsum := summable_translates_of_exp_decay hh hc hzb t
  have h1 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), z (t + ((k : ℝ) - N) * h))
      atTop (𝓝 (∑' k : ℤ, z (t + k * h))) := by
    refine (tendsto_sum_range_sub_of_hasSum hsum.hasSum).congr fun N => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring_nf
  have h2 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), z (t + ((k : ℝ) - N) * h))
      atTop (𝓝 (g t * ∑ i, S.ratio i ^ s * n i)) := by
    refine (S.tendsto_sum_defect_of_periodic hdim hbot n hn hgp hg t).congr fun N => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hren (t + ((k : ℝ) - N) * h)]
    ring
  have heq := tendsto_nhds_unique h1 h2
  have hm : S.renewalMean s = h * ∑ i, S.ratio i ^ s * n i := S.renewalMean_eq_of_lattice s n hn
  have hne : ∑ i, S.ratio i ^ s * n i ≠ 0 := by
    intro h0
    have := S.renewalMean_pos s
    rw [hm, h0, mul_zero] at this
    exact lt_irrefl _ this
  unfold periodisation
  rw [heq, hm]
  field_simp

/-! ### The periodic limit of the correlation profile -/

/-- **`eq:lattice-periodisation`.**  The periodic limit of the lattice branch of
`thm:renewal-limits`, `G̃(t) = (ℓ/m) ∑_{k∈ℤ} z(t + kℓ)`, the periodisation of the renewal
defect `z = G - ϑ * G` of `eq:g-recursion`.  The series converges by
`IsNatural.summable_renewalDefect_lattice`. -/
def latticePeriodisation (s : ℝ) (μ : Measure ℝ) (h : ℝ) : ℝ → ℝ :=
  S.periodisation s h (S.renewalDefect s μ)

/-- The series in `eq:lattice-periodisation` converges at every phase, by the exponential
tails of the renewal defect from `thm:renewal-defect-left-tail` and
`thm:cross-piece-mass`. -/
theorem IsNatural.summable_renewalDefect_lattice {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (t : ℝ) :
    Summable fun k : ℤ => S.renewalDefect s μ (t + k * h) := by
  obtain ⟨C, c, -, hc, hbound⟩ := exists_abs_renewalDefect_le_exp S
    (hosc.strongOpenSetCondition S hμ.attractor) hs0 hs1 hdim hμ
  exact summable_translates_of_exp_decay hh hc hbound t

/-- `eq:lattice-periodisation` as a convergent series: `∑_{k∈ℤ} z(t + kℓ)` has sum
`(m/ℓ) G̃(t)`. -/
theorem IsNatural.hasSum_latticePeriodisation {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (t : ℝ) :
    HasSum (fun k : ℤ => S.renewalDefect s μ (t + k * h))
      (S.renewalMean s / h * S.latticePeriodisation s μ h t) := by
  obtain ⟨C, c, -, hc, hbound⟩ := exists_abs_renewalDefect_le_exp S
    (hosc.strongOpenSetCondition S hμ.attractor) hs0 hs1 hdim hμ
  exact S.hasSum_periodisation hh hc hbound t

/-- Every `ℓ`-periodic limit of `G` is the periodisation `G̃`. -/
theorem IsNatural.eq_latticePeriodisation_of_periodic_limit {K : Set ℝ} {s h : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) {g : ℝ → ℝ} (hgp : Function.Periodic g h)
    (hg : Tendsto (fun w => G s μ w - g w) atTop (𝓝 0)) (t : ℝ) :
    g t = S.latticePeriodisation s μ h t := by
  have := hμ.isProbabilityMeasure
  obtain ⟨C, c, -, hc, hbound⟩ := exists_abs_renewalDefect_le_exp S
    (hosc.strongOpenSetCondition S hμ.attractor) hs0 hs1 hdim hμ
  exact S.eq_periodisation_of_periodic_limit hdim hh hlat
    (HomogeneousNonconstancy.tendsto_G_atBot_zero hs0) hc hbound
    (fun x => by rw [renewalDefect]; ring) hgp hg t

/-- **`thm:renewal-limits`, the lattice case.**  Under the open set condition, at the
similarity dimension, if the log-ratios generate `ℓℤ`, the periodisation `G̃` of
`eq:lattice-periodisation` is continuous, `ℓ`-periodic and strictly positive, and
`G(t) - G̃(t) → 0` as `t → ∞`. -/
theorem IsNatural.lattice_periodisation_limit {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    Continuous (S.latticePeriodisation s μ h) ∧
      Function.Periodic (S.latticePeriodisation s μ h) h ∧
      (∀ t, 0 < S.latticePeriodisation s μ h t) ∧
      Tendsto (fun t => G s μ t - S.latticePeriodisation s μ h t) atTop (𝓝 0) := by
  obtain ⟨g, hgc, hgp, hgpos, hglim⟩ := S.lattice_G_limit hs0 hs1 hosc hdim hh hlat hμ
  have heq : g = S.latticePeriodisation s μ h :=
    funext (hμ.eq_latticePeriodisation_of_periodic_limit S hs0 hs1 hosc hdim hh hlat hgp hglim)
  rw [← heq]
  exact ⟨hgc, hgp, hgpos, hglim⟩

/-- **`thm:lattice-nonconvergence`.**  For a lattice system under the open set condition,
the periodic profile `G̃` of `eq:lattice-periodisation` is non-constant: a constant `G̃`
would make `G` converge, against `IsNatural.not_tendsto_G_of_lattice`. -/
theorem IsNatural.latticePeriodisation_nonconstant {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ v w, S.latticePeriodisation s μ h v ≠ S.latticePeriodisation s μ h w := by
  obtain ⟨-, -, -, hlim⟩ := hμ.lattice_periodisation_limit S hs0 hs1 hosc hdim hh hlat
  by_contra hcon
  push Not at hcon
  have hconst : Tendsto (G s μ) atTop (𝓝 (S.latticePeriodisation s μ h 0)) := by
    have h0 := hlim.add_const (S.latticePeriodisation s μ h 0)
    rw [zero_add] at h0
    refine h0.congr fun w => ?_
    rw [hcon w 0]
    ring
  exact hμ.not_tendsto_G_of_lattice S hs0 hs1 hosc hdim (S.exists_nat_mul_of_lattice hh hlat)
    _ hconst

/-- `sec:smoothing`, the lattice case: `H̃_μ^s = T G̃` is continuous, `ℓ/2`-periodic,
strictly positive and non-constant, by `thm:lattice-nonconvergence` and
`thm:smoothing-injective`, and `H_μ^s(t) - H̃_μ^s(t) → 0` since Gaussian smoothing
preserves a bounded error tending to zero. -/
theorem IsNatural.smoothed_latticePeriodisation {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    Continuous (smoothOp s (S.latticePeriodisation s μ h)) ∧
      Function.Periodic (smoothOp s (S.latticePeriodisation s μ h)) (h / 2) ∧
      (∀ t, 0 < smoothOp s (S.latticePeriodisation s μ h) t) ∧
      (∃ v w, smoothOp s (S.latticePeriodisation s μ h) v
        ≠ smoothOp s (S.latticePeriodisation s μ h) w) ∧
      Tendsto (fun t => H s μ t - smoothOp s (S.latticePeriodisation s μ h) t) atTop (𝓝 0) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  obtain ⟨hgc, hgp, hgpos, hglim⟩ := hμ.lattice_periodisation_limit S hs0 hs1 hosc hdim hh hlat
  obtain ⟨B, -, hB⟩ := exists_nonneg_bound_of_periodic hh.ne' hgc hgp
  exact ⟨continuous_smoothOp hs0 hs1 hgc hB, smoothOp_periodic hgp,
    smoothOp_pos hs0 hs1 hgc hgpos hB,
    smoothOp_nonconstant hs0 hs1 hh hgc hgp
      (hμ.latticePeriodisation_nonconstant S hs0 hs1 hosc hdim hh hlat),
    smooth_profile_error_tendsto hs0 hs1 hA hgc hh hgp hglim⟩

end System

/-- `thm:profile-asymptotics`, the lattice branch: the limit `H̃_μ^s = T G̃` of
`sec:smoothing` is continuous, `ℓ/2`-periodic, strictly positive and non-constant, and
`H_μ^s - H̃_μ^s → 0`. -/
theorem lattice_profile_asymptotics_nonconstant {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : System ι) {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ P : ℝ → ℝ, Continuous P ∧ Function.Periodic P (h / 2) ∧
      (∀ t, 0 < P t) ∧ (∃ v w, P v ≠ P w) ∧ Tendsto (fun t ↦ H s μ t - P t) atTop (𝓝 0) :=
  ⟨_, hμ.smoothed_latticePeriodisation S hs0 hs1 hosc hdim hh hlat⟩

end

end BrownianImages
