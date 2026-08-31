/-
Vendored into `BrownianImages` from
  https://github.com/BennyAvelin/AbsorptionCutoff
  AbsorptionCutoff/Supercritical/RenewalEquation.lean
at commit 41c45c6d72e979419e46224bb7b4be5cee31f2b5, under the Apache License 2.0
(a copy is in this directory as `LICENSE`).

Modified, twice:
  1. the `import` lines were rewritten to the module paths of this project;
  2. the `Nonlattice` hypothesis was weakened to `FellerNonlattice`, which is what
     the proofs below actually consume.  `FellerNonlattice` and its almost everywhere
     consequence are defined in `Basic.lean`; the hypothesis is swapped in the
     declarations that merely forward it, `charFun_ne_one_of_nonlattice` is replaced by
     the corresponding field, and the one live use of the pointwise bound
     `norm_charFun_lt_one_of_nonlattice` becomes an almost everywhere statement inside
     the `filter_upwards` that consumes it.  `Nonlattice`,
     `charFun_ne_one_of_nonlattice`, `norm_charFun_lt_one_of_nonlattice` and
     `tendsto_charFun_pow_of_nonlattice` are kept unchanged.
     See `PLAN.md`, *Reusing the external renewal library*.
-/
/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import BrownianImages.Renewal.Approx

/-!
# Solving the renewal equation

The renewal *equation* `h = h ⋆ μ + ψ`, as opposed to the renewal *theorem*. This
module holds unit **A-7** of the Chapter 7 lane: everything in the proof of the
paper's `lem:nd-gaussian-renewal` that sits
between the abstract renewal equation and the key renewal limit, which
`AbsorptionCutoff.Supercritical.RenewalApprox` now supplies.

The paper's proof runs in four blocks, and so does this module:

* **A-7a** (paper L4801–4818) — iterating the equation `n` times turns it into
  `h_y = 𝔼 h_{y−Sₙ} + ∑_{k<n} 𝔼 ψ_{y−S_k}`;
* **A-7b** (L4819–4866) — the terminal term `𝔼 h_{y−Sₙ}` vanishes as `n → ∞`,
  leaving `h_y = ∑_{k≥0} 𝔼 ψ_{y−S_k}`;
* **A-7c** (L4867–4896) — the key renewal theorem then gives
  `h_y ⟶ (∫ψ)/m̂`;
* **A-7d** (L4897–4911) — angular reconstruction, the only block that leaves the
  scalar setting.

Split off from `RenewalApprox.lean` because it is a different subject — solution
theory rather than bandlimited approximation — and because keeping it at the top
of the pure-Mathlib leaf chain preserves the cheap (~20 s) build target that the
one-lemma loop needs.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace AbsorptionCutoff

namespace Renewal

/-! ### A-7a — iterating the renewal equation

Paper `lem:nd-gaussian-renewal`, block "Scalar renewal equation" (L4801–4818).
-/

/-- **Iterating the renewal equation** (paper L4808–4818). If `h` solves

  `h y = ∫ h (y − z) μ(dz) + ψ y`   for every `y`,

then for every `n`

  `h y = ∫ h (y − s) μ^{*n}(ds) + ∑_{k<n} ∫ ψ (y − s) μ^{*k}(ds)`,

which is the paper's `h_y = 𝔼 h_{y−Sₙ} + ∑_{k<n} 𝔼 Ψ_{y−S_k}(1)` written against
the convolution powers instead of the walk. Blocks A-7b and A-7c then send the
first term to `0` and the second to `(∫ψ)/m̂`.

The two integrability hypotheses are stated as the induction actually consumes
them — at every level `n` and every shift — rather than in some weakest form;
in the chapter they come from the growth conditions
`eq:nd-renewal-left-boundary` and `eq:nd-renewal-right-minimality` on `ℋ`, which
bound `|h|` by a constant multiple of `e^{β y⁺}`.

The step is `convPow_succ` plus `integral_conv`: the double integral
`∫∫ h (y − (s + z)) μ(dz) μ^{*n}(ds)` *is* `∫ h (y − u) μ^{*(n+1)}(du)`. -/
theorem eq_integral_convPow_add_sum_of_renewalEquation
    {μ : Measure ℝ} [SFinite μ] {h ψ : ℝ → ℝ}
    (hh : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => h (y - s)) (convPow μ n))
    (hψ : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => ψ (y - s)) (convPow μ n))
    (hren : ∀ y : ℝ, h y = (∫ z, h (y - z) ∂μ) + ψ y) (y : ℝ) (n : ℕ) :
    h y = (∫ s, h (y - s) ∂convPow μ n)
      + ∑ k ∈ Finset.range n, ∫ s, ψ (y - s) ∂convPow μ k := by
  induction n with
  | zero => simp [convPow_zero]
  | succ n ih =>
      -- one more step of the walk, applied under the `μ^{*n}` integral
      have key : (∫ s, h (y - s) ∂convPow μ n)
          = (∫ s, h (y - s) ∂convPow μ (n + 1)) + ∫ s, ψ (y - s) ∂convPow μ n := by
        have hsplit : ∀ s : ℝ, h (y - s) = (∫ z, h (y - (s + z)) ∂μ) + ψ (y - s) := by
          intro s
          simpa [sub_add_eq_sub_sub] using hren (y - s)
        -- the inner integral is `h - ψ` along the shift, hence integrable
        have hinner : Integrable (fun s => ∫ z, h (y - (s + z)) ∂μ) (convPow μ n) := by
          have hrw : (fun s => ∫ z, h (y - (s + z)) ∂μ)
              = fun s => h (y - s) - ψ (y - s) := by
            funext s; rw [hsplit s]; ring
          rw [hrw]; exact (hh n y).sub (hψ n y)
        rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
          integral_add hinner (hψ n y), convPow_succ,
          integral_conv (by rw [← convPow_succ]; exact hh (n + 1) y)]
      rw [ih, key, Finset.sum_range_succ]
      ring

/-! ### A-7b — the terminal term vanishes

Paper `lem:nd-gaussian-renewal`, block starting "We claim that, for this fixed
`y`, the terminal term tends to zero" (L4819–4866).
-/

/-- **Mass escapes every compact interval**: `μ^{*n}(I) → 0` for every bounded
interval `I`.

This is the paper's "since `m̂ > 0`, we have `Sₙ → ∞` almost surely" in the form
the terminal-term estimate actually consumes. **Deviation, deliberate:** the
paper gets the middle region under control from that almost-sure divergence plus
dominated convergence, on a probability space carrying the walk. Here it comes
instead from local finiteness of the renewal measure — `∑ₙ μ^{*n}(I) < ∞`,
already proved as `renewalMeasure_Icc_lt_top` — whose terms therefore tend to
zero. Same content, but it stays with the convolution powers and needs no walk,
and it reuses a Chernoff bound the lane already paid for. -/
theorem tendsto_convPow_Icc_zero {μ : Measure ℝ} [SFinite μ] {θ : ℝ} (hθ : 0 < θ)
    (hlt : expTransform θ μ < 1) (a b : ℝ) :
    Filter.Tendsto (fun n => convPow μ n (Set.Icc a b)) Filter.atTop (nhds 0) := by
  refine ENNReal.tendsto_atTop_zero_of_tsum_ne_top ?_
  rw [← renewalMeasure_apply μ measurableSet_Icc]
  exact (renewalMeasure_Icc_lt_top hθ hlt a b).ne

/-- **The three-region bound on the terminal term** (paper L4819–4858), for a
single measure `ν` — in the application `ν = μ^{*n}`, so this is `𝔼|h_{y−Sₙ}|`.

Split the shifted argument `u = y − s` at `−M` and at `L`:

* far left, `u ≤ −M`: the left-boundary hypothesis
  `eq:nd-renewal-left-boundary` makes `|h|` at most `ε`;
* middle, `−M < u ≤ L`: local boundedness gives `|h| ≤ C`, and the middle region
  is exactly `s ∈ [y−L, y+M]`, a *bounded interval* — this is the only term that
  carries any dependence on `n`, and `tendsto_convPow_Icc_zero` kills it;
* far right, `L < u`: the right-tail minimality
  `eq:nd-renewal-right-minimality` gives `|h u| ≤ ε e^{βu}`, and
  `e^{β(y−s)} = e^{βy} e^{−βs}` integrates to `e^{βy}` times the exponential
  transform — which is `1` along the tilted walk.

The proof is a pointwise domination followed by one linear integration; there is
no set splitting, because the middle bound is written as an indicator. -/
theorem lintegral_enorm_comp_sub_le {ν : Measure ℝ} {h : ℝ → ℝ} {β ε C M L y : ℝ}
    (hε : 0 ≤ ε)
    (hleft : ∀ u, u ≤ -M → |h u| ≤ ε)
    (hmid : ∀ u, -M < u → u ≤ L → |h u| ≤ C)
    (hright : ∀ u, L < u → |h u| ≤ ε * Real.exp (β * u)) :
    ∫⁻ s, ‖h (y - s)‖ₑ ∂ν
      ≤ ENNReal.ofReal ε * ν Set.univ
        + ENNReal.ofReal C * ν (Set.Icc (y - L) (y + M))
        + ENNReal.ofReal (ε * Real.exp (β * y)) * expTransform β ν := by
  have hind : Measurable ((Set.Icc (y - L) (y + M)).indicator fun _ : ℝ => (1 : ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Icc
  have hpt : ∀ s : ℝ, ‖h (y - s)‖ₑ ≤ ENNReal.ofReal ε
      + ENNReal.ofReal C * (Set.Icc (y - L) (y + M)).indicator (fun _ => (1 : ℝ≥0∞)) s
      + ENNReal.ofReal (ε * Real.exp (β * y)) * ENNReal.ofReal (Real.exp (-(β * s))) := by
    intro s
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_or_gt (y - s) (-M) with hcase | hcase
    · exact le_add_right (le_add_right (ENNReal.ofReal_le_ofReal (hleft _ hcase)))
    rcases le_or_gt (y - s) L with hcase2 | hcase2
    · have hs : s ∈ Set.Icc (y - L) (y + M) := ⟨by linarith, by linarith⟩
      rw [Set.indicator_of_mem hs]
      refine le_add_right ?_
      calc ENNReal.ofReal |h (y - s)| ≤ ENNReal.ofReal C :=
            ENNReal.ofReal_le_ofReal (hmid _ hcase hcase2)
        _ = ENNReal.ofReal C * 1 := by rw [mul_one]
        _ ≤ _ := le_add_self
    · refine le_add_left ?_
      have hb : |h (y - s)| ≤ ε * Real.exp (β * y) * Real.exp (-(β * s)) := by
        calc |h (y - s)| ≤ ε * Real.exp (β * (y - s)) := hright _ hcase2
          _ = ε * Real.exp (β * y) * Real.exp (-(β * s)) := by
              rw [mul_assoc, ← Real.exp_add]; ring_nf
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hb
  calc ∫⁻ s, ‖h (y - s)‖ₑ ∂ν ≤ _ := lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_left
            (f := fun s : ℝ => ENNReal.ofReal ε
              + ENNReal.ofReal C * (Set.Icc (y - L) (y + M)).indicator (fun _ => (1 : ℝ≥0∞)) s)
            (measurable_const.add (hind.const_mul _)),
          lintegral_add_left (f := fun _ : ℝ => ENNReal.ofReal ε) measurable_const,
          lintegral_const, lintegral_const_mul _ hind,
          lintegral_indicator measurableSet_Icc, lintegral_const_mul _ (by fun_prop),
          expTransform_def]
        simp

/-- **The terminal term vanishes** (paper L4819–4866): for each fixed `y`,

  `𝔼 h_{y−Sₙ} = ∫ h (y − s) μ^{*n}(ds) ⟶ 0`  as `n → ∞`.

The three hypotheses on `h` are the paper's, transcribed:
`hbot` is `eq:nd-renewal-left-boundary` (`‖ℋ_y‖_TV → 0` as `y → −∞`), `hloc` is
local boundedness — which, with `hbot`, is the paper's
`sup_{u≤L}‖ℋ_u‖_TV < ∞` — and `htop` is the minimal right-tail condition
`eq:nd-renewal-right-minimality`. `hexp` is `𝔼e^{−βSₙ} = 1`, the defining
property of the tilt; `hθ`/`hlt` are the Chernoff data behind the local
finiteness of the renewal measure.

No integrability hypothesis is needed: the Bochner integral of a non-integrable
function is `0`, and `enorm_integral_le_lintegral_enorm` holds regardless.

Given `ε`, the far-left and far-right regions are each made `≤ ε₁` by choosing
the thresholds `−M` and `L`, and `ε₁` is calibrated so that the two of them
together — one of which is inflated by `e^{βy}` — cost `ε/4`. Only the middle
region depends on `n`, and it vanishes by `tendsto_convPow_Icc_zero`. -/
theorem tendsto_integral_comp_sub_convPow_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β θ : ℝ} (hθ : 0 < θ)
    (hlt : expTransform θ μ < 1) (hexp : ∀ n : ℕ, expTransform β (convPow μ n) = 1)
    {h : ℝ → ℝ}
    (hbot : Filter.Tendsto h Filter.atBot (nhds 0))
    (hloc : ∀ L : ℝ, ∃ C : ℝ, ∀ u, u ≤ L → |h u| ≤ C)
    (htop : Filter.Tendsto (fun u => Real.exp (-(β * u)) * |h u|) Filter.atTop (nhds 0))
    (y : ℝ) :
    Filter.Tendsto (fun n => ∫ s, h (y - s) ∂convPow μ n) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- calibrate the two `ε₁` regions so that together they cost `ε/4`
  obtain ⟨ε₁, hε₁, hKε⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ * (1 + Real.exp (β * y)) = ε / 4 := by
    refine ⟨ε / (4 * (1 + Real.exp (β * y))), by positivity, ?_⟩
    field_simp
  -- the far-left threshold, from `eq:nd-renewal-left-boundary`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ u, u ≤ -M → |h u| ≤ ε₁ := by
    have h1 : ∀ᶠ u in Filter.atBot, |h u| ≤ ε₁ := by
      filter_upwards [hbot (Metric.closedBall_mem_nhds (0 : ℝ) hε₁)] with u hu
      simpa [Real.dist_eq] using hu
    obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 h1
    exact ⟨-a, fun u hu => ha u (by linarith)⟩
  -- the far-right threshold, from `eq:nd-renewal-right-minimality`
  obtain ⟨L, hLM, hL⟩ : ∃ L : ℝ, -M ≤ L ∧ ∀ u, L < u → |h u| ≤ ε₁ * Real.exp (β * u) := by
    have h1 : ∀ᶠ u in Filter.atTop, Real.exp (-(β * u)) * |h u| ≤ ε₁ := by
      filter_upwards [htop (Metric.closedBall_mem_nhds (0 : ℝ) hε₁)] with u hu
      have hnn : (0 : ℝ) ≤ Real.exp (-(β * u)) * |h u| := by positivity
      simpa [Real.dist_eq, abs_of_nonneg hnn] using hu
    obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 h1
    refine ⟨max b (-M), le_max_right _ _, fun u hu => ?_⟩
    have hkey := hb u (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hu))
    have hid : Real.exp (-(β * u)) * Real.exp (β * u) = 1 := by rw [← Real.exp_add]; simp
    have hrw : |h u| = Real.exp (-(β * u)) * |h u| * Real.exp (β * u) := by
      rw [mul_comm (Real.exp (-(β * u))) |h u|, mul_assoc, hid, mul_one]
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
  -- the middle bound, from local boundedness
  obtain ⟨C, hC⟩ := hloc L
  have hmidbd : ∀ u, -M < u → u ≤ L → |h u| ≤ max C 0 := fun u _ hu2 =>
    (hC u hu2).trans (le_max_left _ _)
  -- the middle region is a bounded interval, so its mass vanishes
  have h2 : Filter.Tendsto
      (fun n => ENNReal.ofReal (max C 0) * convPow μ n (Set.Icc (y - L) (y + M)))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (tendsto_convPow_Icc_zero hθ hlt (y - L) (y + M))
      (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (h2.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by linarith : (0 : ℝ) < ε / 2))))
  refine ⟨n₀, fun n hn => ?_⟩
  have hfin : ‖∫ s, h (y - s) ∂convPow μ n‖ₑ < ENNReal.ofReal ε := by
    calc ‖∫ s, h (y - s) ∂convPow μ n‖ₑ ≤ ∫⁻ s, ‖h (y - s)‖ₑ ∂convPow μ n :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ENNReal.ofReal ε₁ * convPow μ n Set.univ
          + ENNReal.ofReal (max C 0) * convPow μ n (Set.Icc (y - L) (y + M))
          + ENNReal.ofReal (ε₁ * Real.exp (β * y)) * expTransform β (convPow μ n) :=
          lintegral_enorm_comp_sub_le hε₁.le hM hmidbd hL
      _ ≤ ENNReal.ofReal ε₁ + ENNReal.ofReal (ε / 2)
          + ENNReal.ofReal (ε₁ * Real.exp (β * y)) := by
          rw [measure_univ, hexp n, mul_one, mul_one]
          gcongr
          exact (hn₀ n hn).le
      _ = ENNReal.ofReal (ε₁ + ε / 2 + ε₁ * Real.exp (β * y)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by nlinarith [hKε])
  rw [Real.dist_eq, sub_zero]
  rw [Real.enorm_eq_ofReal_abs] at hfin
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hfin

/-- **The renewal equation is solved by the forcing's renewal series** (paper
L4864–4866):

  `h y = ∑ₖ ∫ ψ (y − s) μ^{*k}(ds)`,

the paper's `h_y = ∑_{k≥0} 𝔼 Ψ_{y−S_k}(1)`. This is A-7a with the terminal term
of A-7b removed: the partial sums equal `h y − ∫ h (y − s) μ^{*n}(ds)`, whose
second term vanishes.

Summability of the series is a hypothesis rather than a conclusion, because
convergence of the partial sums is by itself weaker than `Summable`. In the
chapter it is free — `summable_integral_comp_sub_of_driNorm` supplies it from the
same d.R.i. bound `eq:nd-dri-definition` that A-7c consumes. -/
theorem eq_tsum_integral_comp_sub_of_renewalEquation
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β θ : ℝ} (hθ : 0 < θ)
    (hlt : expTransform θ μ < 1) (hexp : ∀ n : ℕ, expTransform β (convPow μ n) = 1)
    {h ψ : ℝ → ℝ}
    (hh : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => h (y - s)) (convPow μ n))
    (hψ : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => ψ (y - s)) (convPow μ n))
    (hren : ∀ y : ℝ, h y = (∫ z, h (y - z) ∂μ) + ψ y)
    (hbot : Filter.Tendsto h Filter.atBot (nhds 0))
    (hloc : ∀ L : ℝ, ∃ C : ℝ, ∀ u, u ≤ L → |h u| ≤ C)
    (htop : Filter.Tendsto (fun u => Real.exp (-(β * u)) * |h u|) Filter.atTop (nhds 0))
    {y : ℝ} (hsum : Summable fun n => ∫ s, ψ (y - s) ∂convPow μ n) :
    h y = ∑' n, ∫ s, ψ (y - s) ∂convPow μ n := by
  have hpart : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, ∫ s, ψ (y - s) ∂convPow μ k)
      Filter.atTop (nhds (h y)) := by
    have hA : ∀ n : ℕ, (∑ k ∈ Finset.range n, ∫ s, ψ (y - s) ∂convPow μ k)
        = h y - ∫ s, h (y - s) ∂convPow μ n := fun n => by
      have := eq_integral_convPow_add_sum_of_renewalEquation hh hψ hren y n
      linarith
    simp_rw [hA]
    simpa using (tendsto_const_nhds (x := h y) (f := Filter.atTop (α := ℕ))).sub
      (tendsto_integral_comp_sub_convPow_zero hθ hlt hexp hbot hloc htop y)
  exact (hsum.hasSum_iff_tendsto_nat.2 hpart).tsum_eq.symm

/-! ### A-7c — the renewal limit

Paper `lem:nd-gaussian-renewal`, block "Renewal limit" (L4867–4896).
-/

/-- **The scalar renewal limit** (paper L4867–4896): a solution of the renewal
equation with directly Riemann integrable forcing satisfies

  `h y ⟶ (∫ ψ) / m̂`  as  `y → ∞`.

Composition of A-7b's series representation with the key renewal theorem
`tendsto_tsum_integral_comp_sub_of_driNorm_real`. The d.R.i. hypothesis on `ψ`
does double duty: it drives the renewal limit *and* discharges the summability
and integrability side conditions of A-7a/A-7b, via
`summable_integral_comp_sub_of_driNorm` and `integrable_comp_sub_of_driNorm`
against the uniform cell bound.

**Simplification over the paper**, worth recording: the paper splits the signed
forcing as `Ψ = Ψ⁺ − Ψ⁻` and applies Feller's theorem to each part, because that
theorem needs a nonnegative integrand. Ours takes signed kernels directly, so no
split is needed. That is a weaker demand on the input, not a stronger one.

The continuity hypothesis `hψc`, by contrast, *is* stronger than the paper's a.e.
continuity — the standing deviation of the d.R.i.-norm route, recorded on
`tendsto_tsum_integral_comp_sub_of_driNorm`. -/
theorem tendsto_of_renewalEquation_of_driNorm
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : FellerNonlattice μ) (hmem : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {β : ℝ} (hexp : ∀ n : ℕ, expTransform β (convPow μ n) = 1)
    {h ψ : ℝ → ℝ}
    (hψc : Continuous ψ) (hψd : driNorm (fun x => ‖ψ x‖ₑ) ≠ ∞)
    (hh : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => h (y - s)) (convPow μ n))
    (hren : ∀ y : ℝ, h y = (∫ z, h (y - z) ∂μ) + ψ y)
    (hbot : Filter.Tendsto h Filter.atBot (nhds 0))
    (hloc : ∀ L : ℝ, ∃ C : ℝ, ∀ u, u ≤ L → |h u| ≤ C)
    (htop : Filter.Tendsto (fun u => Real.exp (-(β * u)) * |h u|) Filter.atTop (nhds 0)) :
    Filter.Tendsto h Filter.atTop (nhds ((∫ x : ℝ, ψ x) / (∫ x, x ∂μ))) := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_renewalMeasure_Icc_of_expTransform hμ hmem hm hθ hlt 1
  have hψd' : driNorm (fun x => ‖((ψ x : ℝ) : ℂ)‖ₑ) ≠ ∞ := by
    simpa [enorm_eq_nnnorm] using hψd
  -- the forcing's shifts are integrable against every convolution power
  have hψi : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => ψ (y - s)) (convPow μ n) := by
    intro n y
    have := integrable_comp_sub_of_driNorm hC₀ ENNReal.ofReal_ne_top
      (Complex.continuous_ofReal.comp hψc) hψd' y n
    simpa using this.re
  -- and its renewal series converges
  have hsum : ∀ y : ℝ, Summable fun n => ∫ s, ψ (y - s) ∂convPow μ n := by
    intro y
    rw [← Complex.summable_ofReal]
    refine (summable_integral_comp_sub_of_driNorm hC₀ ENNReal.ofReal_ne_top hψd' y).congr
      fun n => ?_
    rw [integral_complex_ofReal]
  have hval : ∀ y : ℝ, h y = ∑' n, ∫ s, ψ (y - s) ∂convPow μ n := fun y =>
    eq_tsum_integral_comp_sub_of_renewalEquation hθ hlt hexp hh hψi hren hbot hloc htop (hsum y)
  exact (tendsto_tsum_integral_comp_sub_of_driNorm_real hμ hmem hm hθ hlt hψc hψd).congr
    fun y => (hval y).symm

/-! ### A-7d — angular reconstruction

Paper `lem:nd-gaussian-renewal`, final block (L4897–4911). The step below is its
scalar prerequisite: the paper's "using direct Riemann integrability to get
`Ψ_y(φ) → 0` and `Ψ_y(1) → 0`".
-/

/-- **A directly Riemann integrable kernel vanishes at `+∞`.** If
`‖g‖_DRI = ∑_{k∈ℤ} sup_{[k,k+1]} g` is finite then `g y → 0` as `y → ∞`.

The cell suprema over `k ≥ 0` form a subseries of a convergent series, so they
tend to `0`; and `g y` is dominated by the supremum over the cell containing
`y`, namely `k = ⌊y⌋`, which runs off to `+∞` with `y`. -/
theorem tendsto_atTop_zero_of_driNorm {g : ℝ → ℝ≥0∞} (hg : driNorm g ≠ ∞) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have hsub : ∑' n : ℕ, cellSup g (n : ℤ) ≠ ∞ :=
    ne_top_of_le_ne_top hg
      (ENNReal.tsum_comp_le_tsum_of_injective (fun a b hab => by exact_mod_cast hab) _)
  have hcell : Filter.Tendsto (fun n : ℕ => cellSup g (n : ℤ)) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsub
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := (ENNReal.tendsto_atTop_zero.1 hcell) ε hε
  refine ⟨(n₀ : ℝ), fun x hx => ?_⟩
  have hfl : (n₀ : ℤ) ≤ ⌊x⌋ := by rw [Int.le_floor]; exact_mod_cast hx
  have hmem : x ∈ Set.Icc ((⌊x⌋ : ℝ)) ((⌊x⌋ : ℝ) + 1) :=
    ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩
  refine (le_cellSup hmem).trans ?_
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌊x⌋ = (m : ℤ) :=
    ⟨⌊x⌋.toNat, (Int.toNat_of_nonneg ((Int.natCast_nonneg n₀).trans hfl)).symm⟩
  rw [hm]
  exact hn₀ m (by exact_mod_cast hm ▸ hfl)

/-- Real-valued form of `tendsto_atTop_zero_of_driNorm`: this is the paper's
`Ψ_y(φ) → 0` and `Ψ_y(1) → 0` at L4909–4911. -/
theorem tendsto_atTop_zero_of_driNorm_real {z : ℝ → ℝ}
    (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto z Filter.atTop (nhds 0) :=
  tendsto_zero_iff_enorm_tendsto_zero.2 (tendsto_atTop_zero_of_driNorm hz)

/-- **Angular reconstruction** (paper L4897–4911), completing
`lem:nd-gaussian-renewal`:

  `ℋ_y(φ) ⟶ (∫ φ dσ̄) · (∫ Ψ_t(1) dt) / m̂`.

`Hφ` is `y ↦ ℋ_y(φ)`, `Ψφ` is `y ↦ Ψ_y(φ)`, `h` and `ψ` are their `φ = 1`
counterparts, and `a` is the constant `∫ φ dσ̄`. Hypothesis `hang` is the
paper's display at L4901–4906, which is what the product form of the tilted
kernel `eq:nd-tilted-kernel` buys: the angular integral factors out completely,
leaving the *same* scalar convolution `∫ h (y − z) μ̂(dz)` for every `φ`.

**No measures on `𝕊^{N−1}` appear.** Once the angular variable has factored
through the constant `a`, the paper's remaining argument is entirely scalar:
replace the convolution by `h y − ψ y` using the scalar renewal equation, then
send `ψ y → 0` and `Ψφ y → 0` by direct Riemann integrability. Formalizing the
sphere would add nothing the proof uses. -/
theorem tendsto_angular_of_renewalEquation_of_driNorm
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : FellerNonlattice μ) (hmem : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {β : ℝ} (hexp : ∀ n : ℕ, expTransform β (convPow μ n) = 1)
    {h ψ Hφ Ψφ : ℝ → ℝ} {a : ℝ}
    (hψc : Continuous ψ) (hψd : driNorm (fun x => ‖ψ x‖ₑ) ≠ ∞)
    (hΨφd : driNorm (fun x => ‖Ψφ x‖ₑ) ≠ ∞)
    (hh : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => h (y - s)) (convPow μ n))
    (hren : ∀ y : ℝ, h y = (∫ z, h (y - z) ∂μ) + ψ y)
    (hang : ∀ y : ℝ, Hφ y = a * (∫ z, h (y - z) ∂μ) + Ψφ y)
    (hbot : Filter.Tendsto h Filter.atBot (nhds 0))
    (hloc : ∀ L : ℝ, ∃ C : ℝ, ∀ u, u ≤ L → |h u| ≤ C)
    (htop : Filter.Tendsto (fun u => Real.exp (-(β * u)) * |h u|) Filter.atTop (nhds 0)) :
    Filter.Tendsto Hφ Filter.atTop (nhds (a * ((∫ x : ℝ, ψ x) / (∫ x, x ∂μ)))) := by
  have hlim := tendsto_of_renewalEquation_of_driNorm hμ hmem hm hθ hlt hexp hψc hψd hh hren
    hbot hloc htop
  have hψ0 := tendsto_atTop_zero_of_driNorm_real hψd
  have hΨ0 := tendsto_atTop_zero_of_driNorm_real hΨφd
  -- the scalar equation turns the convolution into `h − ψ`
  have hrw : ∀ y : ℝ, Hφ y = a * (h y - ψ y) + Ψφ y := fun y => by
    rw [hang y, show (∫ z, h (y - z) ∂μ) = h y - ψ y by linarith [hren y]]
  refine Filter.Tendsto.congr (fun y => (hrw y).symm) ?_
  simpa using ((hlim.sub hψ0).const_mul a).add hΨ0

end Renewal

end AbsorptionCutoff
