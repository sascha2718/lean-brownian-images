module

/-
Vendored into `BrownianImages` from
  https://github.com/BennyAvelin/AbsorptionCutoff
  AbsorptionCutoff/Supercritical/RenewalEquation.lean
at commit 41c45c6d72e979419e46224bb7b4be5cee31f2b5, under the Apache License 2.0
(a copy is in this directory as `LICENSE`).

Modifications to the vendored subset:
  1. project-local imports replace the upstream module paths where needed;
  2. renewal-limit declarations use `FellerNonlattice`, the weaker hypothesis
     consumed by their proofs. `Basic.lean` defines it and its almost everywhere
     consequence; forwarding declarations and three proof sites are adjusted.
     The upstream `Nonlattice` definition and the lemmas
     `charFun_ne_one_of_nonlattice` and `norm_charFun_lt_one_of_nonlattice` remain
     for the proved comparison and the two-atom counterexample;
  3. unused helper declarations were removed from `Basic.lean`, `Equation.lean`
     and `Kernel.lean`; related documentation was updated;
  4. Lean module headers, public imports and exposed public definitions preserve
     the retained interfaces under the module system.
See `docs/renewal-library.md` and the top-level `NOTICE`.
-/
/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
public import BrownianImages.Renewal.Approx

@[expose] public section

/-!
# Solving the renewal equation

The renewal *equation* `h = h ⋆ μ + ψ`, as opposed to the renewal *theorem*. This
module holds unit **A-7** of the Chapter 7 lane: everything in the proof of the
paper's `lem:nd-gaussian-renewal` that sits
between the abstract renewal equation and the key renewal limit, which
`AbsorptionCutoff.Supercritical.RenewalApprox` now supplies.

The retained part of the upstream proof has two blocks:

* **A-7a** (upstream paper L4801–4818) — iterating the equation `n` times gives
  `h_y = 𝔼 h_{y−Sₙ} + ∑_{k<n} 𝔼 ψ_{y−S_k}`;
* **A-7b** (L4819–4866) — the terminal term `𝔼 h_{y−Sₙ}` vanishes as `n → ∞`,
  leaving `h_y = ∑_{k≥0} 𝔼 ψ_{y−S_k}`.

The key renewal limit is supplied by `BrownianImages.Renewal.Approx` and applied
in this project by `BrownianImages.KeyRenewalFourier`. The unused upstream
scalar-limit wrapper and angular-reconstruction block have been removed.

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
the convolution powers instead of the walk. Block A-7b sends the first term to
`0`, leaving the renewal series to which the key renewal theorem applies.

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

end Renewal

end AbsorptionCutoff
