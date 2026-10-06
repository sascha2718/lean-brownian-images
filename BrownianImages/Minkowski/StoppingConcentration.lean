/-
`thm:neighbourhood-concentration` of `sec:reconstruction`, under the strong open set
condition.

At logarithmic scale `t = log(1/r)` the profile `X(t)` is compared with the sum
`Y_{r,u}` of the normalised tube masses of the Brownian images of the stopping cylinders
at temporal scale `u`.  Brownian scaling gives each summand the law of `p_w X(t - β_w)`;
the partition of `thm:stopping-overlap` into `M` classes of cylinders with disjoint
interiors makes each class independent, so `eq:stopping-neighbourhood-variance` bounds
the variance of `Y_{r,u}` by `M ∑ p_w² Var X(t - β_w) = O(u^s)`.  The error
`F_{r,u} = Y_{r,u} - X(t)` is the multiple-counting defect of the leaf family; it
telescopes into the internal defects `D_{v,r}` of the stopping tree, each bounded in
expectation by `eq:neighbourhood-defect-mean` below the node `v`, which gives
`eq:stopping-neighbourhood-defect`; since `0 ≤ F_{r,u} ≤ Y_{r,u}`, its third moment is
bounded, and interpolation gives the `L²` bound.  With `u = r` both terms decay
exponentially in `t`.

* `stoppingHalfLogRatio`, `IsPlanarBrownian.identDistrib_normalizedTubeMass_brownianStoppingCylinder`:
  Brownian scaling for a stopping cylinder, `M_r(BM(S_w K)) ~ p_w X_w(t - β_w)`.
* `IsPlanarBrownian.iIndepFun_normalizedTubeMass_brownianStoppingCylinders`: cylinders
  whose time intervals have disjoint interiors have independent tube masses.
* `IsNatural.stoppingLeafDefect`, `IsNatural.stoppingLeafDefect_succ_of_not_le`: the
  telescoping of `F_{r,u}` over the stopping tree.
* `IsNatural.integral_stoppingLeafDefect_le`: `eq:stopping-neighbourhood-defect`.
* `IsNatural.centeredL2Norm_sum_stoppingCylinders_le`:
  `eq:stopping-neighbourhood-variance`.
* `IsNatural.tubeConcentration_of_sosc`: `thm:neighbourhood-concentration`.
-/
import Mathlib.Algebra.Order.Chebyshev
import BrownianImages.Minkowski.StoppingOverlap
import BrownianImages.Minkowski.ProfileL2
import BrownianImages.Minkowski.DefectL2
import BrownianImages.Minkowski.AlmostSure

namespace BrownianImages

open MeasureTheory ProbabilityTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe u

/-! ### Two elementary inequalities -/

/-- A linear function is dominated by every exponential, `1 + t ≤ (1 + ε⁻¹) e^{εt}`. -/
theorem one_add_le_mul_exp {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    1 + t ≤ (1 + ε⁻¹) * Real.exp (ε * t) := by
  have h1 : 1 ≤ Real.exp (ε * t) := Real.one_le_exp (mul_nonneg hε.le ht)
  have h2 : ε * t + 1 ≤ Real.exp (ε * t) := Real.add_one_le_exp _
  have h3 : t ≤ ε⁻¹ * Real.exp (ε * t) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hε]
    linarith
  linarith

/-- A real power of the logarithmic radius is an exponential. -/
theorem tubeRadiusReal_rpow (v x : ℝ) : tubeRadiusReal v ^ x = Real.exp (-(x * v)) := by
  unfold tubeRadiusReal
  rw [← Real.exp_mul]
  ring_nf

namespace MinkowskiL2Recurrence

/-- Minkowski's inequality for the centred `L²` norm of a finite sum. -/
theorem centeredL2Norm_sum_le {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    {P : Measure Ω} [IsFiniteMeasure P] (Y : κ → Ω → ℝ) (hY : ∀ m, MemLp (Y m) 2 P) :
    centeredL2Norm (fun ω => ∑ m, Y m ω) P ≤ ∑ m, centeredL2Norm (Y m) P := by
  unfold centeredL2Norm
  have hint : ∀ m, Integrable (Y m) P := fun m => (hY m).integrable one_le_two
  rw [integral_finsetSum _ fun m _ => hint m]
  have heq : (fun ω => (∑ m, Y m ω) - ∑ m, ∫ x, Y m x ∂P)
      = ∑ m, (fun ω => Y m ω - ∫ x, Y m x ∂P) := by
    funext ω
    simp only [Finset.sum_apply, Finset.sum_sub_distrib]
  rw [heq]
  exact lpNorm_sum_le (fun m _ => (hY m).sub (memLp_const _)) one_le_two

end MinkowskiL2Recurrence

/-! ### Finite unions of compact sets -/

/-- A finite union of compact sets is determined by mutual inclusion of the underlying
sets. -/
theorem compactUnion_eq_of_subset_of_forall_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ι → CompactPlane) (G : CompactPlane) (hFG : ∀ i, (F i : Set Plane) ⊆ G)
    (hGF : ∀ x ∈ (G : Set Plane), ∃ i, x ∈ (F i : Set Plane)) : compactUnion F = G := by
  apply le_antisymm
  · unfold compactUnion
    exact (Finset.sup'_le_iff Finset.univ_nonempty _).2 fun i _ => hFG i
  · intro x hx
    obtain ⟨i, hi⟩ := hGF x hx
    exact Finset.le_sup' F (Finset.mem_univ i) hi

/-- Convexity of the cube: for weights `p` summing to one and non-negative `z`,
`(∑ z)³ ≤ ∑ p⁻² z³`. -/
theorem cube_sum_le_sum_inv_sq_mul_cube {ι : Type*} [Fintype ι] (p z : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) (hz : ∀ i, 0 ≤ z i) :
    (∑ i, z i) ^ 3 ≤ ∑ i, (p i)⁻¹ ^ 2 * z i ^ 3 := by
  have h := Real.pow_arith_mean_le_arith_mean_pow (s := Finset.univ) p (fun i => z i / p i)
    (fun i _ => (hp i).le) hsum (fun i _ => div_nonneg (hz i) (hp i).le) 3
  have hleft : ∑ i, p i * (z i / p i) = ∑ i, z i :=
    Finset.sum_congr rfl fun i _ => mul_div_cancel₀ _ (hp i).ne'
  have hright : ∑ i, p i * (z i / p i) ^ 3 = ∑ i, (p i)⁻¹ ^ 2 * z i ^ 3 :=
    Finset.sum_congr rfl fun i _ => by
      have := (hp i).ne'
      field_simp
  rw [hleft, hright] at h
  exact h

open _root_.BrownianImages.System (StoppingWord stoppingRoot stoppingChild)

variable {iota : Type u} [Fintype iota] [Nonempty iota] (S : System iota)
variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  {W : ℝ≥0 → Omega → Plane}

namespace System

/-! ### Brownian scaling for a stopping cylinder -/

omit [Nonempty iota] in
/-- The half-logarithmic delay `β_w = (1/2) log(1/r_w)` of a stopping word. -/
def stoppingHalfLogRatio (w : StoppingWord iota) : ℝ :=
  (1 / 2 : ℝ) * Real.log (S.stoppingRatio w)⁻¹

omit [Nonempty iota] in
/-- The physical radius at the delayed scale is divided by `√r_w`. -/
theorem tubeRadiusReal_sub_stoppingHalfLogRatio (w : StoppingWord iota) (v : ℝ) :
    tubeRadiusReal (v - S.stoppingHalfLogRatio w)
      = tubeRadiusReal v / Real.sqrt (S.stoppingRatio w) := by
  have hr : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have hsqrt : Real.sqrt (S.stoppingRatio w)
      = Real.exp (Real.log (S.stoppingRatio w) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
  unfold tubeRadiusReal stoppingHalfLogRatio
  rw [hsqrt, Real.log_inv, ← Real.exp_sub]
  congr 1
  ring

omit [Nonempty iota] in
/-- The planar Brownian Jacobian and the profile normalisation combine to the natural
weight of the cylinder. -/
theorem exp_tubeExponent_mul_stoppingRatio (s : ℝ) (w : StoppingWord iota) (v : ℝ) :
    Real.exp (tubeExponent s * v) * S.stoppingRatio w
      = S.stoppingWeight s w * Real.exp (tubeExponent s * (v - S.stoppingHalfLogRatio w)) := by
  have hr : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  rw [S.stoppingWeight_eq_ratio_rpow, Real.rpow_def_of_pos hr, stoppingHalfLogRatio,
    Real.log_inv, ← Real.exp_add, tubeExponent]
  conv_lhs => rw [← Real.exp_log hr, ← Real.exp_add]
  congr 1
  ring

omit [Nonempty iota] in
/-- The delayed scale is non-negative as soon as `r² ≤ r_w`. -/
theorem sub_stoppingHalfLogRatio_nonneg {w : StoppingWord iota} {v : ℝ}
    (hrw : tubeRadiusReal v ^ 2 ≤ S.stoppingRatio w) :
    0 ≤ v - S.stoppingHalfLogRatio w := by
  have hr : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have hpos := tubeRadiusReal_pos v
  have hlog : Real.log (tubeRadiusReal v ^ 2) ≤ Real.log (S.stoppingRatio w) :=
    Real.log_le_log (by positivity) hrw
  rw [Real.log_pow, tubeRadiusReal, Real.log_exp] at hlog
  unfold stoppingHalfLogRatio
  rw [Real.log_inv]
  push_cast at hlog
  linarith

end System

omit [Nonempty iota] in
/-- Exact tube-mass law of the Brownian image of a stopping cylinder. -/
theorem IsPlanarBrownian.map_tubeMass_brownianStoppingCylinder_eq [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (w : StoppingWord iota) (v : ℝ) :
    P.map (fun omega => tubeMass (tubeRadiusReal v)
        (brownianImage W (hμ.attractor.stoppingCylinder S w.1 w.2) omega))
      = P.map (fun omega => S.stoppingRatio w *
        tubeMass (tubeRadiusReal (v - S.stoppingHalfLogRatio w))
          (brownianImage W hμ.compactAttractor omega)) := by
  have hlaw := hW.map_tubeMass_affineBrownianCompactPiece_orientCompact_eq
    (tubeRadiusReal_pos v) (S.stoppingAnchor w) (S.stoppingLength_ne_zero w)
    (S.stoppingSign_eq w) hμ.compactAttractor hμ.attractor.2.2.1
  simpa only [hμ.attractor.stoppingCylinder_eq_affineTimeCompact S w,
    affineBrownianCompactPiece, System.IsNatural.compactAttractor, System.coe_stoppingLength,
    ← S.tubeRadiusReal_sub_stoppingHalfLogRatio w v] using hlaw

omit [Nonempty iota] in
/-- **Brownian scaling for a stopping cylinder**: the normalised tube mass of
`BM(S_w K)` has the law of `p_w X(t - β_w)`. -/
theorem IsPlanarBrownian.identDistrib_normalizedTubeMass_brownianStoppingCylinder
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (w : StoppingWord iota) (v : ℝ) :
    IdentDistrib
      (fun omega => normalizedTubeMass s v
        (brownianImage W (hμ.attractor.stoppingCylinder S w.1 w.2) omega))
      (fun omega => S.stoppingWeight s w *
        brownianTubeProfile W hμ.compactAttractor s (v - S.stoppingHalfLogRatio w) omega)
      P P := by
  let X : Omega → ℝ := fun omega => tubeMass (tubeRadiusReal v)
    (brownianImage W (hμ.attractor.stoppingCylinder S w.1 w.2) omega)
  let Y : Omega → ℝ := fun omega => S.stoppingRatio w *
    tubeMass (tubeRadiusReal (v - S.stoppingHalfLogRatio w))
      (brownianImage W hμ.compactAttractor omega)
  have hX : AEMeasurable X P :=
    (continuous_tubeMass (tubeRadiusReal_pos v)).measurable.comp_aemeasurable
      (hW.aemeasurable_brownianImage _)
  have hY : AEMeasurable Y P :=
    (continuous_const.mul (continuous_tubeMass
      (tubeRadiusReal_pos (v - S.stoppingHalfLogRatio w)))).measurable.comp_aemeasurable
      (hW.aemeasurable_brownianImage hμ.compactAttractor)
  have hmass : IdentDistrib X Y P P :=
    ⟨hX, hY, hW.map_tubeMass_brownianStoppingCylinder_eq S hμ w v⟩
  have hscaled := hmass.const_mul (Real.exp (tubeExponent s * v))
  simpa only [X, Y, normalizedTubeMass, brownianTubeProfile, ← mul_assoc,
    S.exp_tubeExponent_mul_stoppingRatio s w v] using hscaled

/-! ### Independence of cylinders with disjoint time intervals -/

omit [Nonempty iota] in
/-- Stopping cylinders whose host intervals have pairwise disjoint interiors have
independent normalised tube masses. -/
theorem IsPlanarBrownian.iIndepFun_normalizedTubeMass_brownianStoppingCylinders
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (v : ℝ) {J : Type*} [Fintype J] (word : J → StoppingWord iota)
    (hdisj : ∀ j j' : J, j ≠ j' →
      S.stoppingLeft (word j) + S.stoppingRatio (word j) ≤ S.stoppingLeft (word j') ∨
      S.stoppingLeft (word j') + S.stoppingRatio (word j') ≤ S.stoppingLeft (word j)) :
    iIndepFun (fun j omega => normalizedTubeMass s v
      (brownianImage W (hμ.attractor.stoppingCylinder S (word j).1 (word j).2) omega)) P := by
  let a : J → NNReal := fun j => S.stoppingAnchor (word j)
  let r : J → NNReal := fun j => S.stoppingLength (word j)
  let L : J → NonemptyCompacts ℝ := fun j =>
    orientCompact (S.stoppingSign (word j)) hμ.compactAttractor
  have hr : ∀ j, r j ≠ 0 := fun j => S.stoppingLength_ne_zero _
  have hL : ∀ j, (L j : Set ℝ) ⊆ Set.Icc 0 1 := fun j =>
    orientCompact_subset_Icc (S.stoppingSign_eq _) hμ.attractor.2.2.1
  have hdisjoint : ∀ ⦃j j' : J⦄, j ≠ j' → a j + r j ≤ a j' ∨ a j' + r j' ≤ a j := by
    intro j j' hne
    rcases hdisj j j' hne with h | h
    · left
      exact NNReal.coe_le_coe.mp (by simpa only [NNReal.coe_add, a, r,
        System.coe_stoppingAnchor, System.coe_stoppingLength] using h)
    · right
      exact NNReal.coe_le_coe.mp (by simpa only [NNReal.coe_add, a, r,
        System.coe_stoppingAnchor, System.coe_stoppingLength] using h)
  have hind := hW.iIndepFun_centeredBrownianCompactPieces a r L hr hL hdisjoint
  have hmass : iIndepFun (fun j omega => normalizedTubeMass s v
      (centeredBrownianCompactPiece W (a j) (r j) (L j) omega)) P := by
    simpa only [Function.comp_def] using
      hind.comp (fun _ F => normalizedTubeMass s v F)
        (fun _ => (continuous_normalizedTubeMass s v).measurable)
  apply hmass.congr
  intro j
  filter_upwards [hW.ae_continuous] with omega homega
  have haffine : translateCompact (W (a j) omega)
      (centeredBrownianCompactPiece W (a j) (r j) (L j) omega)
      = brownianImage W (hμ.attractor.stoppingCylinder S (word j).1 (word j).2) omega := by
    have h := translate_dilate_rescaledBrownianCompactPiece_of_continuous
      (a := a j) (r := r j) (K := L j) (hr j) (hL j) homega
    simpa only [centeredBrownianCompactPiece, L, smulCompact_eq_dilateCompact,
      hμ.attractor.stoppingCylinder_eq_affineTimeCompact S (word j),
      affineBrownianCompactPiece, a, r, System.IsNatural.compactAttractor] using h
  unfold normalizedTubeMass
  rw [← haffine, tubeMass_translate]

namespace System

/-! ### Sums over the leaves of the stopping tree -/

omit [Nonempty iota] in
/-- At depth zero the only leaf is the root. -/
theorem sum_stoppingLeaves_zero {M : Type*} [AddCommMonoid M] (delta : ℝ)
    (w : StoppingWord iota) (f : StoppingWord iota → M) :
    ∑ L : S.StoppingLeaves delta 0 w, f (S.stoppingLeafWord delta L) = f w := by
  calc ∑ L : S.StoppingLeaves delta 0 w, f (S.stoppingLeafWord delta L)
      = ∑ _u : PUnit.{u + 1}, f w := by
        apply Fintype.sum_equiv (S.stoppingLeavesCutoffEquiv delta w).symm
        intro L
        cases L
        rfl
    _ = f w := by simp

omit [Nonempty iota] in
/-- Below a word that has crossed the threshold the only leaf is the word itself. -/
theorem sum_stoppingLeaves_succ_of_le {M : Type*} [AddCommMonoid M] (delta : ℝ) {n : ℕ}
    {w : StoppingWord iota} (h : S.stoppingRatio w ≤ delta) (f : StoppingWord iota → M) :
    ∑ L : S.StoppingLeaves delta (n + 1) w, f (S.stoppingLeafWord delta L) = f w := by
  calc ∑ L : S.StoppingLeaves delta (n + 1) w, f (S.stoppingLeafWord delta L)
      = ∑ _u : PUnit.{u + 1}, f w := by
        apply Fintype.sum_equiv (S.stoppingLeavesStopEquiv delta h).symm
        intro L
        cases L with
        | stop _ => rfl
        | branch h' i child => exact (h' h).elim
    _ = f w := by simp

omit [Nonempty iota] in
/-- Below a word that has not crossed the threshold the leaves are the leaves below its
children. -/
theorem sum_stoppingLeaves_succ_of_not_le {M : Type*} [AddCommMonoid M] (delta : ℝ) {n : ℕ}
    {w : StoppingWord iota} (h : ¬ S.stoppingRatio w ≤ delta) (f : StoppingWord iota → M) :
    ∑ L : S.StoppingLeaves delta (n + 1) w, f (S.stoppingLeafWord delta L)
      = ∑ i, ∑ L : S.StoppingLeaves delta n (stoppingChild w i), f (S.stoppingLeafWord delta L) := by
  classical
  calc ∑ L : S.StoppingLeaves delta (n + 1) w, f (S.stoppingLeafWord delta L)
      = ∑ child : (Σ i : iota, S.StoppingLeaves delta n (stoppingChild w i)),
          f (S.stoppingLeafWord delta child.2) := by
        apply Fintype.sum_equiv (S.stoppingLeavesBranchEquiv delta h).symm
        intro L
        cases L with
        | stop h' => exact (h h').elim
        | branch _ i child => rfl
    _ = _ := by rw [Fintype.sum_sigma]

/-! ### The cylinders below a node cover it -/

omit [Nonempty iota] in
/-- The cylinder of a child lies in the cylinder of its parent. -/
theorem IsAttractor.stoppingCylinder_child_subset {K : Set ℝ} (hK : S.IsAttractor K)
    (w : StoppingWord iota) (i : iota) :
    (hK.stoppingCylinder S (stoppingChild w i).1 (stoppingChild w i).2 : Set ℝ)
      ⊆ hK.stoppingCylinder S w.1 w.2 := by
  rw [IsAttractor.coe_stoppingCylinder, IsAttractor.coe_stoppingCylinder]
  change (S.stoppingMap w.1 w.2 ∘ S.map i) '' K ⊆ S.stoppingMap w.1 w.2 '' K
  rw [Set.image_comp]
  exact Set.image_mono (hK.mapsTo_map S i).image_subset

omit [MeasurableSpace Omega] in
/-- On a continuous path, the Brownian image of a cylinder is the union of the Brownian
images of its children. -/
theorem IsAttractor.compactUnion_brownianStoppingCylinder_children_eq {K : Set ℝ}
    (hK : S.IsAttractor K) (w : StoppingWord iota) {omega : Omega}
    (homega : Continuous fun t => W t omega) :
    compactUnion (fun i => brownianImage W
        (hK.stoppingCylinder S (stoppingChild w i).1 (stoppingChild w i).2) omega)
      = brownianImage W (hK.stoppingCylinder S w.1 w.2) omega := by
  apply compactUnion_eq_of_subset_of_forall_exists
  · intro i
    rw [coe_brownianImage_of_continuous _ homega, coe_brownianImage_of_continuous _ homega]
    exact Set.image_mono (hK.stoppingCylinder_child_subset S w i)
  · intro x hx
    rw [coe_brownianImage_of_continuous _ homega] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨i, hi⟩ := hK.exists_mem_stoppingCylinder_child S ht
    refine ⟨i, ?_⟩
    rw [coe_brownianImage_of_continuous _ homega]
    exact ⟨t, hi, rfl⟩

omit [MeasurableSpace Omega] in
/-- On a continuous path, the Brownian image of a cylinder is the union of the Brownian
images of the stopping cylinders below it. -/
theorem IsAttractor.compactUnion_brownianStoppingCylinder_leaves_eq {K : Set ℝ}
    (hK : S.IsAttractor K) (delta : ℝ) (n : ℕ) (w : StoppingWord iota) {omega : Omega}
    (homega : Continuous fun t => W t omega) :
    compactUnion (fun L : S.StoppingLeaves delta n w => brownianImage W
        (hK.stoppingCylinder S (S.stoppingLeafWord delta L).1
          (S.stoppingLeafWord delta L).2) omega)
      = brownianImage W (hK.stoppingCylinder S w.1 w.2) omega := by
  apply compactUnion_eq_of_subset_of_forall_exists
  · intro L
    rw [coe_brownianImage_of_continuous _ homega, coe_brownianImage_of_continuous _ homega]
    refine Set.image_mono ?_
    rw [IsAttractor.coe_stoppingCylinder, IsAttractor.coe_stoppingCylinder]
    exact hK.image_stoppingLeafWord_subset S delta L
  · intro x hx
    rw [coe_brownianImage_of_continuous _ homega] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨L, hL⟩ := hK.exists_stoppingLeaf_mem S delta n w ht
    refine ⟨L, ?_⟩
    rw [coe_brownianImage_of_continuous _ homega]
    exact ⟨t, hL, rfl⟩

/-! ### The telescoped defect -/

omit [Nonempty iota] in
/-- The defect of the leaf family below a node: the sum of the tube masses of the Brownian
images of the stopping cylinders below `w` minus the tube mass of the Brownian image of
the cylinder of `w`.  On a continuous path this is the multiple-counting defect of the
leaf family. -/
def IsNatural.stoppingLeafDefect {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (W : ℝ≥0 → Omega → Plane) (r delta : ℝ) (n : ℕ) (w : StoppingWord iota)
    (omega : Omega) : ℝ :=
  (∑ L : S.StoppingLeaves delta n w, tubeMass r (brownianImage W
      (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord delta L).1
        (S.stoppingLeafWord delta L).2) omega))
    - tubeMass r (brownianImage W (hμ.attractor.stoppingCylinder S w.1 w.2) omega)

omit [Nonempty iota] in
/-- The internal defect `D_{w,r}` at a node: the sum over the children minus the node. -/
def IsNatural.stoppingNodeDefect {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (W : ℝ≥0 → Omega → Plane) (r : ℝ) (w : StoppingWord iota) (omega : Omega) : ℝ :=
  (∑ i, tubeMass r (brownianImage W
      (hμ.attractor.stoppingCylinder S (stoppingChild w i).1 (stoppingChild w i).2) omega))
    - tubeMass r (brownianImage W (hμ.attractor.stoppingCylinder S w.1 w.2) omega)

omit [Nonempty iota] [MeasurableSpace Omega] in
/-- At depth zero the leaf defect vanishes. -/
theorem IsNatural.stoppingLeafDefect_zero {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (r delta : ℝ) (w : StoppingWord iota) (omega : Omega) :
    hμ.stoppingLeafDefect S W r delta 0 w omega = 0 := by
  unfold IsNatural.stoppingLeafDefect
  rw [S.sum_stoppingLeaves_zero delta w (fun w' => tubeMass r (brownianImage W
    (hμ.attractor.stoppingCylinder S w'.1 w'.2) omega)), sub_self]

omit [Nonempty iota] [MeasurableSpace Omega] in
/-- Below a word that has crossed the threshold the leaf defect vanishes. -/
theorem IsNatural.stoppingLeafDefect_succ_of_le {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (r : ℝ) {delta : ℝ} {n : ℕ} {w : StoppingWord iota}
    (h : S.stoppingRatio w ≤ delta) (omega : Omega) :
    hμ.stoppingLeafDefect S W r delta (n + 1) w omega = 0 := by
  unfold IsNatural.stoppingLeafDefect
  rw [S.sum_stoppingLeaves_succ_of_le delta h (fun w' => tubeMass r (brownianImage W
    (hμ.attractor.stoppingCylinder S w'.1 w'.2) omega)), sub_self]

omit [Nonempty iota] [MeasurableSpace Omega] in
/-- **Telescoping over the stopping tree.**  Below a word that has not crossed the
threshold, the leaf defect is the sum of the leaf defects below the children plus the
internal defect at the word. -/
theorem IsNatural.stoppingLeafDefect_succ_of_not_le {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (r : ℝ) {delta : ℝ} {n : ℕ} {w : StoppingWord iota}
    (h : ¬ S.stoppingRatio w ≤ delta) (omega : Omega) :
    hμ.stoppingLeafDefect S W r delta (n + 1) w omega
      = (∑ i, hμ.stoppingLeafDefect S W r delta n (stoppingChild w i) omega)
        + hμ.stoppingNodeDefect S W r w omega := by
  unfold IsNatural.stoppingLeafDefect IsNatural.stoppingNodeDefect
  rw [S.sum_stoppingLeaves_succ_of_not_le delta h (fun w' => tubeMass r (brownianImage W
    (hμ.attractor.stoppingCylinder S w'.1 w'.2) omega)), Finset.sum_sub_distrib]
  ring

omit [MeasurableSpace Omega] in
/-- On a continuous path the internal defect is the multiple-counting defect of the
children. -/
theorem IsNatural.stoppingNodeDefect_eq_tubeDefect {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (r : ℝ) (w : StoppingWord iota) {omega : Omega}
    (homega : Continuous fun t => W t omega) :
    hμ.stoppingNodeDefect S W r w omega
      = tubeDefect r (fun i => brownianImage W
          (hμ.attractor.stoppingCylinder S (stoppingChild w i).1 (stoppingChild w i).2) omega) := by
  unfold IsNatural.stoppingNodeDefect tubeDefect
  rw [hμ.attractor.compactUnion_brownianStoppingCylinder_children_eq S w homega]

omit [MeasurableSpace Omega] in
/-- On a continuous path the leaf defect is the multiple-counting defect of the leaf
family. -/
theorem IsNatural.stoppingLeafDefect_eq_tubeDefect {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (r delta : ℝ) (n : ℕ) (w : StoppingWord iota) {omega : Omega}
    (homega : Continuous fun t => W t omega) :
    hμ.stoppingLeafDefect S W r delta n w omega
      = tubeDefect r (fun L : S.StoppingLeaves delta n w => brownianImage W
          (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord delta L).1
            (S.stoppingLeafWord delta L).2) omega) := by
  unfold IsNatural.stoppingLeafDefect tubeDefect
  rw [hμ.attractor.compactUnion_brownianStoppingCylinder_leaves_eq S delta n w homega]


/-! ### `eq:stopping-neighbourhood-defect` -/

omit [Nonempty iota] in
/-- The weights of the children of a word sum to the weight of the word. -/
theorem sum_stoppingWeight_child {s : ℝ} (hdim : S.IsDimension s) (w : StoppingWord iota) :
    ∑ i, S.stoppingWeight s (stoppingChild w i) = S.stoppingWeight s w := by
  simp only [stoppingWeight_child, ← Finset.mul_sum, S.sum_tubeWeight hdim, mul_one]

/-- The generation count `max(0, 1 + log(r_w/u) / log(1/r_max))`: an upper bound for the
number of generations of the stopping tree at threshold `u` below the word `w` that
have not yet crossed the threshold. -/
def stoppingGenerationCount (u : ℝ) (w : StoppingWord iota) : ℝ :=
  max 0 (1 + Real.log (S.stoppingRatio w / u) / Real.log (Hutchinson.maxRatio S)⁻¹)

/-- The generation count is non-negative. -/
theorem stoppingGenerationCount_nonneg (u : ℝ) (w : StoppingWord iota) :
    0 ≤ S.stoppingGenerationCount u w :=
  le_max_left _ _

/-- The logarithm of the reciprocal maximal ratio is positive. -/
theorem log_inv_maxRatio_pos : 0 < Real.log (Hutchinson.maxRatio S)⁻¹ :=
  Real.log_pos ((one_lt_inv₀ (Hutchinson.maxRatio_pos S)).mpr (Hutchinson.maxRatio_lt_one S))

/-- Below a word that has not crossed the threshold, the generation count of every child
is smaller by one. -/
theorem stoppingGenerationCount_child_add_one_le {u : ℝ} (hu : 0 < u) {w : StoppingWord iota}
    (h : u < S.stoppingRatio w) (i : iota) :
    S.stoppingGenerationCount u (stoppingChild w i) + 1 ≤ S.stoppingGenerationCount u w := by
  have hL := S.log_inv_maxRatio_pos
  have hrw : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have hri : 0 < S.ratio i := S.ratio_pos i
  have hlogw : 0 < Real.log (S.stoppingRatio w / u) := Real.log_pos ((one_lt_div hu).mpr h)
  have hw : S.stoppingGenerationCount u w
      = 1 + Real.log (S.stoppingRatio w / u) / Real.log (Hutchinson.maxRatio S)⁻¹ := by
    unfold stoppingGenerationCount
    exact max_eq_right (by positivity)
  have hlogi : Real.log (S.ratio i) / Real.log (Hutchinson.maxRatio S)⁻¹ ≤ -1 := by
    rw [div_le_iff₀ hL, Real.log_inv]
    linarith [Real.log_le_log hri (Hutchinson.ratio_le_maxRatio S i)]
  have hsplit : Real.log (S.stoppingRatio (stoppingChild w i) / u)
      = Real.log (S.stoppingRatio w / u) + Real.log (S.ratio i) := by
    rw [stoppingRatio_child, mul_div_right_comm, Real.log_mul (by positivity) hri.ne']
  rw [hw]
  unfold stoppingGenerationCount
  rw [hsplit, add_div]
  have hpos : (0:ℝ) ≤ Real.log (S.stoppingRatio w / u) / Real.log (Hutchinson.maxRatio S)⁻¹ := by
    positivity
  have hmax : max 0 (1 + (Real.log (S.stoppingRatio w / u) / Real.log (Hutchinson.maxRatio S)⁻¹ +
      Real.log (S.ratio i) / Real.log (Hutchinson.maxRatio S)⁻¹))
      ≤ Real.log (S.stoppingRatio w / u) / Real.log (Hutchinson.maxRatio S)⁻¹ :=
    max_le hpos (by linarith)
  linarith

/-- At the root the generation count is `1 + log(1/u) / log(1/r_max)`. -/
theorem stoppingGenerationCount_root {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    S.stoppingGenerationCount u (stoppingRoot : StoppingWord iota)
      = 1 + Real.log u⁻¹ / Real.log (Hutchinson.maxRatio S)⁻¹ := by
  have hL := S.log_inv_maxRatio_pos
  have hlog : 0 ≤ Real.log u⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hu0).mpr hu1)
  unfold stoppingGenerationCount
  rw [stoppingRatio_root, one_div]
  exact max_eq_right (by positivity)

set_option maxHeartbeats 800000 in
/-- **`eq:stopping-neighbourhood-defect`, node by node.**  If the internal defect at
every node `w` with `r² ≤ r_w` has expectation at most `C r_w^{s-η} r^{α+2η}`, then the
leaf defect at threshold `u ≥ r²` below `w` is integrable with expectation at most
`C u^{-η} r^{α+2η} p_w ν_u(w)`, where `ν_u(w)` is the generation count. -/
theorem IsNatural.integrable_and_integral_stoppingLeafDefect_le [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hdim : S.IsDimension s) {C η : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hnode : ∀ (w : StoppingWord iota) (r : ℝ), 0 < r → r ≤ 1 → r ^ 2 ≤ S.stoppingRatio w →
      Integrable (fun omega => tubeDefect r (fun i => brownianImage W
        (hμ.attractor.stoppingCylinder S (stoppingChild w i).1 (stoppingChild w i).2) omega)) P ∧
      (∫ omega, tubeDefect r (fun i => brownianImage W
        (hμ.attractor.stoppingCylinder S (stoppingChild w i).1 (stoppingChild w i).2) omega) ∂P)
        ≤ C * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η))
    {u r : ℝ} (hu : 0 < u) (hr : 0 < r) (hr1 : r ≤ 1) (hru : r ^ 2 ≤ u) :
    ∀ (n : ℕ) (w : StoppingWord iota),
      Integrable (hμ.stoppingLeafDefect S W r u n w) P ∧
      (∫ omega, hμ.stoppingLeafDefect S W r u n w omega ∂P)
        ≤ C * u ^ (-η) * r ^ (tubeExponent s + 2 * η) * S.stoppingWeight s w *
            S.stoppingGenerationCount u w := by
  intro n
  induction n with
  | zero =>
      intro w
      have hfun : hμ.stoppingLeafDefect S W r u 0 w = fun _ => 0 :=
        funext fun omega => hμ.stoppingLeafDefect_zero S r u w omega
      rw [hfun]
      refine ⟨integrable_const 0, ?_⟩
      rw [integral_const, smul_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hu.le _))
        (Real.rpow_nonneg hr.le _)) (S.generationWeight_nonneg s w.1 w.2))
        (S.stoppingGenerationCount_nonneg u w)
  | succ n ih =>
      intro w
      by_cases h : S.stoppingRatio w ≤ u
      · have hfun : hμ.stoppingLeafDefect S W r u (n + 1) w = fun _ => 0 :=
          funext fun omega => hμ.stoppingLeafDefect_succ_of_le S r h omega
        rw [hfun]
        refine ⟨integrable_const 0, ?_⟩
        rw [integral_const, smul_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hu.le _))
          (Real.rpow_nonneg hr.le _)) (S.generationWeight_nonneg s w.1 w.2))
          (S.stoppingGenerationCount_nonneg u w)
      · have hlt : u < S.stoppingRatio w := lt_of_not_ge h
        have hrw0 : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
        have hrw : r ^ 2 ≤ S.stoppingRatio w := hru.trans hlt.le
        have hfun : hμ.stoppingLeafDefect S W r u (n + 1) w = fun omega =>
            (∑ i, hμ.stoppingLeafDefect S W r u n (stoppingChild w i) omega) +
              hμ.stoppingNodeDefect S W r w omega :=
          funext fun omega => hμ.stoppingLeafDefect_succ_of_not_le S r h omega
        have hih := fun i => ih (stoppingChild w i)
        have hae : hμ.stoppingNodeDefect S W r w =ᵐ[P] fun omega => tubeDefect r
            (fun i => brownianImage W (hμ.attractor.stoppingCylinder S (stoppingChild w i).1
              (stoppingChild w i).2) omega) := by
          filter_upwards [hW.ae_continuous] with omega homega
          exact hμ.stoppingNodeDefect_eq_tubeDefect S r w homega
        obtain ⟨hndint, hndle⟩ := hnode w r hr hr1 hrw
        have hnd : Integrable (hμ.stoppingNodeDefect S W r w) P := hndint.congr hae.symm
        have hndint' : (∫ omega, hμ.stoppingNodeDefect S W r w omega ∂P)
            ≤ C * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η) := by
          rw [integral_congr_ae hae]
          exact hndle
        have hsumint : Integrable (fun omega =>
            ∑ i, hμ.stoppingLeafDefect S W r u n (stoppingChild w i) omega) P :=
          integrable_finsetSum _ fun i _ => (hih i).1
        refine ⟨by rw [hfun]; exact hsumint.add hnd, ?_⟩
        rw [hfun, integral_add hsumint hnd, integral_finsetSum _ fun i _ => (hih i).1]
        -- the factor `r_w^{s-η} ≤ u^{-η} p_w`
        have hfactor : S.stoppingRatio w ^ (s - η) ≤ u ^ (-η) * S.stoppingWeight s w := by
          rw [S.stoppingWeight_eq_ratio_rpow, sub_eq_add_neg, Real.rpow_add hrw0, mul_comm]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hu hlt.le (neg_nonpos.mpr hη))
            (Real.rpow_nonneg hrw0.le _)
        set A : ℝ := C * u ^ (-η) * r ^ (tubeExponent s + 2 * η) with hA
        have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hu.le _))
          (Real.rpow_nonneg hr.le _)
        have hchild : ∀ i, S.stoppingGenerationCount u (stoppingChild w i)
            ≤ S.stoppingGenerationCount u w - 1 := fun i => by
          linarith [S.stoppingGenerationCount_child_add_one_le hu hlt i]
        calc (∑ i, ∫ omega, hμ.stoppingLeafDefect S W r u n (stoppingChild w i) omega ∂P)
              + ∫ omega, hμ.stoppingNodeDefect S W r w omega ∂P
            ≤ (∑ i, A * S.stoppingWeight s (stoppingChild w i) *
                (S.stoppingGenerationCount u w - 1)) + A * S.stoppingWeight s w := by
              refine add_le_add (Finset.sum_le_sum fun i _ => ?_) ?_
              · refine ((hih i).2).trans ?_
                exact mul_le_mul_of_nonneg_left (hchild i)
                  (mul_nonneg hA0 (S.generationWeight_nonneg s _ _))
              · refine hndint'.trans ?_
                calc C * S.stoppingRatio w ^ (s - η) * r ^ (tubeExponent s + 2 * η)
                    ≤ C * (u ^ (-η) * S.stoppingWeight s w) * r ^ (tubeExponent s + 2 * η) :=
                      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hC)
                        (Real.rpow_nonneg hr.le _)
                  _ = A * S.stoppingWeight s w := by rw [hA]; ring
          _ = A * S.stoppingWeight s w * S.stoppingGenerationCount u w := by
              rw [← Finset.sum_mul, ← Finset.mul_sum, S.sum_stoppingWeight_child hdim w]
              ring

/-! ### `eq:stopping-neighbourhood-variance` -/

omit [Nonempty iota] in
/-- Two stopping intervals with disjoint interiors are ordered. -/
theorem ordered_of_disjoint_interior (w w' : StoppingWord iota)
    (h : Disjoint (interior (S.stoppingWordMap w '' Icc (0:ℝ) 1))
      (interior (S.stoppingWordMap w' '' Icc (0:ℝ) 1))) :
    S.stoppingLeft w + S.stoppingRatio w ≤ S.stoppingLeft w' ∨
      S.stoppingLeft w' + S.stoppingRatio w' ≤ S.stoppingLeft w := by
  have hr : 0 < S.stoppingRatio w := S.generationRatio_pos w.1 w.2
  have hr' : 0 < S.stoppingRatio w' := S.generationRatio_pos w'.1 w'.2
  rw [S.stoppingWordMap_image_unitInterval, S.stoppingWordMap_image_unitInterval, interior_Icc,
    interior_Icc, Set.Ioo_disjoint_Ioo, min_le_iff, le_max_iff, le_max_iff] at h
  rcases h with (h | h) | (h | h)
  · linarith
  · exact Or.inl h
  · exact Or.inr h
  · linarith

set_option maxHeartbeats 800000 in
/-- **`eq:stopping-neighbourhood-variance`.**  The sum `Y` of the normalised tube masses
of the Brownian images of the stopping cylinders at threshold `u`, coloured with `M`
colours so that cylinders of one colour have disjoint interiors, has centred `L²` norm
at most `√M · B · u^{s/2}`, where `B` bounds the `L²` norm of the profile at every
non-negative scale. -/
theorem IsNatural.centeredL2Norm_sum_leaves_le [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hs0 : 0 < s) (hdim : S.IsDimension s) {B : ℝ} (hB : 0 ≤ B)
    (hprofile : ∀ v' : ℝ, 0 ≤ v' →
      MemLp (brownianTubeProfile W hμ.compactAttractor s v') 2 P ∧
      lpNorm (brownianTubeProfile W hμ.compactAttractor s v') 2 P ≤ B)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {n : ℕ} (hn : Hutchinson.maxRatio S ^ n ≤ u)
    {v : ℝ} (hru : tubeRadiusReal v ^ 2 ≤ S.minRatio * u)
    {M : ℕ} (c : S.StoppingLeaves u n stoppingRoot → Fin M)
    (hc : ∀ L₁ L₂, L₁ ≠ L₂ → c L₁ = c L₂ →
      Disjoint (interior (S.stoppingWordMap (S.stoppingLeafWord u L₁) '' Icc (0:ℝ) 1))
        (interior (S.stoppingWordMap (S.stoppingLeafWord u L₂) '' Icc (0:ℝ) 1))) :
    MemLp (fun omega => ∑ L : S.StoppingLeaves u n stoppingRoot, normalizedTubeMass s v
      (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord u L).1
        (S.stoppingLeafWord u L).2) omega)) 2 P ∧
    MinkowskiL2Recurrence.centeredL2Norm
      (fun omega => ∑ L : S.StoppingLeaves u n stoppingRoot, normalizedTubeMass s v
        (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord u L).1
          (S.stoppingLeafWord u L).2) omega)) P
      ≤ Real.sqrt M * B * u ^ (s / 2) := by
  classical
  set word : S.StoppingLeaves u n stoppingRoot → StoppingWord iota :=
    fun L => S.stoppingLeafWord u L with hword
  set N : S.StoppingLeaves u n stoppingRoot → Omega → ℝ := fun L omega => normalizedTubeMass s v
    (brownianImage W (hμ.attractor.stoppingCylinder S (word L).1 (word L).2) omega) with hN
  set p : S.StoppingLeaves u n stoppingRoot → ℝ := fun L => S.stoppingWeight s (word L) with hp
  -- the leaves have ratio between `r_min u` and `u`
  have hleaf : ∀ L : S.StoppingLeaves u n stoppingRoot, S.minRatio * u ≤ S.stoppingRatio (word L) ∧
      S.stoppingRatio (word L) ≤ u := fun L => S.stoppingLeafRatio_bounds hu0 hu1 hn L
  have hdelay : ∀ L : S.StoppingLeaves u n stoppingRoot, 0 ≤ v - S.stoppingHalfLogRatio (word L) := fun L =>
    S.sub_stoppingHalfLogRatio_nonneg (hru.trans (hleaf L).1)
  have hp0 : ∀ L, 0 ≤ p L := fun L => S.generationWeight_nonneg s _ _
  have hpu : ∀ L, p L ≤ u ^ s := fun L => by
    rw [hp]
    dsimp only
    rw [S.stoppingWeight_eq_ratio_rpow]
    exact Real.rpow_le_rpow (S.generationRatio_pos _ _).le (hleaf L).2 hs0.le
  have hpsum : ∑ L, p L = 1 := by
    rw [hp]
    dsimp only
    rw [hword]
    dsimp only
    rw [S.sum_stoppingLeafWeight hdim u n stoppingRoot, stoppingWeight_root]
  -- scaling of every leaf
  have hcopy : ∀ L : S.StoppingLeaves u n stoppingRoot, IdentDistrib (N L) (fun omega => p L *
      brownianTubeProfile W hμ.compactAttractor s (v - S.stoppingHalfLogRatio (word L)) omega)
      P P := fun L =>
    hW.identDistrib_normalizedTubeMass_brownianStoppingCylinder S hμ (word L) v
  have hNmem : ∀ L, MemLp (N L) 2 P := fun L =>
    (hcopy L).memLp_iff.mpr ((hprofile _ (hdelay L)).1.const_mul _)
  have hNcent : ∀ L, MinkowskiL2Recurrence.centeredL2Norm (N L) P ≤ p L * B := fun L => by
    rw [MinkowskiL2Recurrence.centeredL2Norm_eq_of_identDistrib (hcopy L) (hNmem L),
      MinkowskiL2Recurrence.centeredL2Norm_const_mul (hprofile _ (hdelay L)).1 (hp0 L)]
    exact mul_le_mul_of_nonneg_left
      ((MinkowskiL2Recurrence.centeredL2Norm_le_lpNorm (hprofile _ (hdelay L)).1).trans
        (hprofile _ (hdelay L)).2) (hp0 L)
  -- the colour classes
  set Y : Fin M → Omega → ℝ := fun m omega => ∑ L : {L : S.StoppingLeaves u n stoppingRoot // c L = m}, N L.1 omega with hY
  have hfib : ∀ omega, (∑ L : S.StoppingLeaves u n stoppingRoot, N L omega) = ∑ m, Y m omega := fun omega =>
    (Fintype.sum_fiberwise c (fun L => N L omega)).symm
  have hYmem : ∀ m, MemLp (Y m) 2 P := fun m =>
    memLp_finsetSum _ fun L _ => hNmem L.1
  have hindep : ∀ m, iIndepFun (fun L : {L : S.StoppingLeaves u n stoppingRoot // c L = m} => N L.1) P := fun m => by
    refine hW.iIndepFun_normalizedTubeMass_brownianStoppingCylinders S hμ v
      (fun L : {L : S.StoppingLeaves u n stoppingRoot // c L = m} => word L.1) fun L L' hne => ?_
    exact S.ordered_of_disjoint_interior _ _
      (hc L.1 L'.1 (fun h => hne (Subtype.ext h)) (L.2.trans L'.2.symm))
  have hYcent : ∀ m, MinkowskiL2Recurrence.centeredL2Norm (Y m) P
      ≤ Real.sqrt (∑ L : {L : S.StoppingLeaves u n stoppingRoot // c L = m}, (p L.1 * B) ^ 2) := fun m => by
    have h := MinkowskiL2Recurrence.centeredL2Norm_weighted_sum_le
      (fun L : {L : S.StoppingLeaves u n stoppingRoot // c L = m} => N L.1) (fun _ => (1:ℝ)) (fun L => p L.1 * B)
      (fun L => hNmem L.1)
      (MinkowskiL2Recurrence.pairwise_indepFun_of_iIndepFun (hindep m))
      (fun L => mul_nonneg (hp0 L.1) hB) (fun L => hNcent L.1)
    simpa only [one_mul, hY] using h
  -- the sum of the classes
  have hsum : (fun omega => ∑ L : S.StoppingLeaves u n stoppingRoot, N L omega) = fun omega => ∑ m, Y m omega :=
    funext hfib
  have hmem : MemLp (fun omega => ∑ L : S.StoppingLeaves u n stoppingRoot, N L omega) 2 P := by
    rw [hsum]
    exact memLp_finsetSum _ fun m _ => hYmem m
  refine ⟨hmem, ?_⟩
  have hfib2 : ∑ m, (Real.sqrt (∑ L : {L : S.StoppingLeaves u n stoppingRoot // c L = m},
      (p L.1 * B) ^ 2)) ^ 2 = ∑ L : S.StoppingLeaves u n stoppingRoot, (p L * B) ^ 2 := by
    calc ∑ m, (Real.sqrt (∑ L : {L : S.StoppingLeaves u n stoppingRoot // c L = m},
          (p L.1 * B) ^ 2)) ^ 2
        = ∑ m, ∑ L : {L : S.StoppingLeaves u n stoppingRoot // c L = m}, (p L.1 * B) ^ 2 :=
          Finset.sum_congr rfl fun m _ =>
            Real.sq_sqrt (Finset.sum_nonneg fun L _ => sq_nonneg _)
      _ = _ := Fintype.sum_fiberwise c (fun L => (p L * B) ^ 2)
  have hsq : ∑ L : S.StoppingLeaves u n stoppingRoot, (p L * B) ^ 2 ≤ B ^ 2 * u ^ s := by
    calc ∑ L : S.StoppingLeaves u n stoppingRoot, (p L * B) ^ 2 = B ^ 2 * ∑ L : S.StoppingLeaves u n stoppingRoot, p L * p L := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun L _ => by ring
      _ ≤ B ^ 2 * ∑ L : S.StoppingLeaves u n stoppingRoot, u ^ s * p L := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun L _ => ?_) (sq_nonneg B)
          exact mul_le_mul_of_nonneg_right (hpu L) (hp0 L)
      _ = B ^ 2 * u ^ s := by rw [← Finset.mul_sum, hpsum, mul_one]
  calc MinkowskiL2Recurrence.centeredL2Norm (fun omega => ∑ L : S.StoppingLeaves u n stoppingRoot, N L omega) P
      = MinkowskiL2Recurrence.centeredL2Norm (fun omega => ∑ m, Y m omega) P := by rw [hsum]
    _ ≤ ∑ m, MinkowskiL2Recurrence.centeredL2Norm (Y m) P :=
        MinkowskiL2Recurrence.centeredL2Norm_sum_le Y hYmem
    _ ≤ ∑ m, Real.sqrt (∑ L : {L : S.StoppingLeaves u n stoppingRoot // c L = m}, (p L.1 * B) ^ 2) :=
        Finset.sum_le_sum fun m _ => hYcent m
    _ ≤ Real.sqrt ((M : ℝ) * ∑ m, (Real.sqrt (∑ L : {L : S.StoppingLeaves u n stoppingRoot // c L = m}, (p L.1 * B) ^ 2)) ^ 2) := by
        refine Real.le_sqrt_of_sq_le ?_
        have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin M)))
          (f := fun m => Real.sqrt (∑ L : {L : S.StoppingLeaves u n stoppingRoot // c L = m}, (p L.1 * B) ^ 2))
        simpa only [Finset.card_univ, Fintype.card_fin] using h
    _ = Real.sqrt ((M : ℝ) * ∑ L : S.StoppingLeaves u n stoppingRoot, (p L * B) ^ 2) := by
        rw [hfib2]
    _ ≤ Real.sqrt ((M : ℝ) * (B ^ 2 * u ^ s)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
    _ = Real.sqrt M * B * u ^ (s / 2) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB,
          Real.sqrt_eq_rpow (u ^ s), ← Real.rpow_mul hu0.le, mul_assoc]
        congr 2
        ring

/-! ### The third moment of `Y` -/

set_option maxHeartbeats 800000 in
/-- **The third moment of `Y`.**  Since the weights `p_w` of the leaves sum to one,
convexity bounds `Y³` by `∑ p_w (p_w⁻¹ M_r(BM(S_w K)))³`, and Brownian scaling bounds the
expectation of every term by the third moment of the profile at the delayed scale. -/
theorem IsNatural.integrable_and_integral_cube_sum_leaves_le [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (_hs0 : 0 < s) (hdim : S.IsDimension s) {C3 : ℝ} (_hC3 : 0 ≤ C3)
    (hcube : ∀ v' : ℝ, 0 ≤ v' →
      Integrable (fun omega => brownianTubeProfile W hμ.compactAttractor s v' omega ^ 3) P ∧
      (∫ omega, brownianTubeProfile W hμ.compactAttractor s v' omega ^ 3 ∂P) ≤ C3)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {n : ℕ} (hn : Hutchinson.maxRatio S ^ n ≤ u)
    {v : ℝ} (hru : tubeRadiusReal v ^ 2 ≤ S.minRatio * u) :
    Integrable (fun omega => (∑ L : S.StoppingLeaves u n stoppingRoot, normalizedTubeMass s v
      (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord u L).1
        (S.stoppingLeafWord u L).2) omega)) ^ 3) P ∧
    (∫ omega, (∑ L : S.StoppingLeaves u n stoppingRoot, normalizedTubeMass s v
      (brownianImage W (hμ.attractor.stoppingCylinder S (S.stoppingLeafWord u L).1
        (S.stoppingLeafWord u L).2) omega)) ^ 3 ∂P) ≤ C3 := by
  classical
  set word : S.StoppingLeaves u n stoppingRoot → StoppingWord iota :=
    fun L => S.stoppingLeafWord u L with hword
  set N : S.StoppingLeaves u n stoppingRoot → Omega → ℝ := fun L omega => normalizedTubeMass s v
    (brownianImage W (hμ.attractor.stoppingCylinder S (word L).1 (word L).2) omega) with hN
  set p : S.StoppingLeaves u n stoppingRoot → ℝ := fun L => S.stoppingWeight s (word L) with hp
  have hleaf : ∀ L : S.StoppingLeaves u n stoppingRoot, S.minRatio * u ≤ S.stoppingRatio (word L) ∧
      S.stoppingRatio (word L) ≤ u := fun L => S.stoppingLeafRatio_bounds hu0 hu1 hn L
  have hdelay : ∀ L : S.StoppingLeaves u n stoppingRoot, 0 ≤ v - S.stoppingHalfLogRatio (word L) := fun L =>
    S.sub_stoppingHalfLogRatio_nonneg (hru.trans (hleaf L).1)
  have hppos : ∀ L, 0 < p L := fun L => by
    rw [hp]
    dsimp only
    rw [S.stoppingWeight_eq_ratio_rpow]
    exact Real.rpow_pos_of_pos (S.generationRatio_pos _ _) _
  have hpsum : ∑ L, p L = 1 := by
    rw [hp]
    dsimp only
    rw [hword]
    dsimp only
    rw [S.sum_stoppingLeafWeight hdim u n stoppingRoot, stoppingWeight_root]
  have hN0 : ∀ L omega, 0 ≤ N L omega := fun L omega => normalizedTubeMass_nonneg _ _ _
  have hNmeas : ∀ L, AEMeasurable (N L) P := fun L =>
    (continuous_normalizedTubeMass s v).measurable.comp_aemeasurable
      (hW.aemeasurable_brownianImage _)
  -- scaling of every leaf, at the level of cubes
  have hcopy : ∀ L : S.StoppingLeaves u n stoppingRoot, IdentDistrib (fun omega => N L omega ^ 3) (fun omega => p L ^ 3 *
      brownianTubeProfile W hμ.compactAttractor s (v - S.stoppingHalfLogRatio (word L)) omega ^ 3)
      P P := fun L => by
    have h := (hW.identDistrib_normalizedTubeMass_brownianStoppingCylinder S hμ (word L) v).comp
      (continuous_pow 3).measurable
    simpa only [Function.comp_def, mul_pow] using h
  have hNcube : ∀ L, Integrable (fun omega => N L omega ^ 3) P := fun L =>
    (hcopy L).integrable_iff.mpr ((hcube _ (hdelay L)).1.const_mul _)
  have hNcubeInt : ∀ L, (∫ omega, N L omega ^ 3 ∂P) ≤ p L ^ 3 * C3 := fun L => by
    rw [(hcopy L).integral_eq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hcube _ (hdelay L)).2 (pow_nonneg (hppos L).le 3)
  -- the convexity bound
  have hconv : ∀ omega, (∑ L, N L omega) ^ 3 ≤ ∑ L, (p L)⁻¹ ^ 2 * N L omega ^ 3 := fun omega =>
    cube_sum_le_sum_inv_sq_mul_cube p (fun L => N L omega) hppos hpsum (fun L => hN0 L omega)
  have halg : ∀ a c : ℝ, 0 < a → a⁻¹ ^ 2 * (a ^ 3 * c) = a * c := fun a c ha => by
    field_simp
  have hdom : Integrable (fun omega => ∑ L, (p L)⁻¹ ^ 2 * N L omega ^ 3) P :=
    integrable_finsetSum _ fun L _ => (hNcube L).const_mul ((p L)⁻¹ ^ 2)
  have hsummeas : AEStronglyMeasurable (fun omega => (∑ L, N L omega) ^ 3) P := by
    have h := ((Finset.aemeasurable_sum (s := Finset.univ) (f := N)
      fun L _ => hNmeas L).pow_const 3).aestronglyMeasurable
    simpa only [Finset.sum_apply] using h
  have hint : Integrable (fun omega => (∑ L, N L omega) ^ 3) P := by
    refine hdom.mono' hsummeas ?_
    filter_upwards with omega
    rw [Real.norm_of_nonneg (pow_nonneg (Finset.sum_nonneg fun L _ => hN0 L omega) 3)]
    exact hconv omega
  refine ⟨hint, ?_⟩
  calc (∫ omega, (∑ L, N L omega) ^ 3 ∂P)
      ≤ ∫ omega, ∑ L, (p L)⁻¹ ^ 2 * N L omega ^ 3 ∂P :=
        integral_mono hint hdom hconv
    _ = ∑ L, (p L)⁻¹ ^ 2 * ∫ omega, N L omega ^ 3 ∂P := by
        rw [integral_finsetSum _ fun L _ => (hNcube L).const_mul _]
        exact Finset.sum_congr rfl fun L _ => integral_const_mul _ _
    _ ≤ ∑ L, (p L)⁻¹ ^ 2 * (p L ^ 3 * C3) :=
        Finset.sum_le_sum fun L _ => mul_le_mul_of_nonneg_left (hNcubeInt L) (by positivity)
    _ = ∑ L, p L * C3 := Finset.sum_congr rfl fun L _ => halg _ _ (hppos L)
    _ = C3 := by rw [← Finset.sum_mul, hpsum, one_mul]

/-! ### `thm:neighbourhood-concentration` -/

omit [Nonempty iota] in
/-- The `q = 3` tube-moment estimate bounds the third moment of the normalised profile
uniformly on the non-negative half-line. -/
theorem IsNatural.exists_brownianTubeProfile_cube_bound_of_tubeMomentsUpper
    [IsProbabilityMeasure P] (_hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ)
    (hmom : ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧ ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      Integrable (fun omega => (tubeArea rho (brownianImage W hμ.compactAttractor omega)) ^ q) P ∧
      Integrable (fun omega => (tubeMass rho (brownianImage W hμ.compactAttractor omega)) ^ q) P ∧
      (∫ omega, (tubeArea rho (brownianImage W hμ.compactAttractor omega)) ^ q ∂P) +
        (∫ omega, (tubeMass rho (brownianImage W hμ.compactAttractor omega)) ^ q ∂P)
          ≤ Cq * rho ^ (q * tubeExponent s)) :
    ∃ C3 : ℝ, 0 < C3 ∧ ∀ v : ℝ, 0 ≤ v →
      Integrable (fun omega => brownianTubeProfile W hμ.compactAttractor s v omega ^ 3) P ∧
      (∫ omega, brownianTubeProfile W hμ.compactAttractor s v omega ^ 3 ∂P) ≤ C3 := by
  obtain ⟨C, hC, hmoment⟩ := hmom 3 (by norm_num)
  refine ⟨C, hC, fun v hv => ?_⟩
  have hrho : 0 < tubeRadiusReal v := tubeRadiusReal_pos v
  have hrho1 : tubeRadiusReal v ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.mpr hv)
  obtain ⟨_, hmass3, hsum⟩ := hmoment (tubeRadiusReal v) hrho hrho1
  have hpow : (fun omega => (tubeMass (tubeRadiusReal v)
      (brownianImage W hμ.compactAttractor omega)) ^ (3:ℝ))
      = fun omega => tubeMass (tubeRadiusReal v) (brownianImage W hμ.compactAttractor omega) ^ 3 :=
    funext fun omega => Real.rpow_natCast _ 3
  have hmass3' : Integrable (fun omega =>
      tubeMass (tubeRadiusReal v) (brownianImage W hμ.compactAttractor omega) ^ 3) P := by
    rw [← hpow]
    exact hmass3
  have hmassMean : (∫ omega, tubeMass (tubeRadiusReal v)
      (brownianImage W hμ.compactAttractor omega) ^ 3 ∂P)
      ≤ C * tubeRadiusReal v ^ (3 * tubeExponent s) := by
    rw [← hpow]
    refine le_trans (le_add_of_nonneg_left (integral_nonneg fun omega =>
      Real.rpow_nonneg (tubeArea_nonneg _ _) _)) hsum
  have hX : (fun omega => brownianTubeProfile W hμ.compactAttractor s v omega ^ 3)
      = fun omega => Real.exp (tubeExponent s * v) ^ 3 *
        tubeMass (tubeRadiusReal v) (brownianImage W hμ.compactAttractor omega) ^ 3 :=
    funext fun omega => by
      unfold brownianTubeProfile normalizedTubeMass
      ring
  refine ⟨by rw [hX]; exact hmass3'.const_mul _, ?_⟩
  rw [hX, integral_const_mul]
  have hexp : Real.exp (tubeExponent s * v) ^ 3 * tubeRadiusReal v ^ (3 * tubeExponent s) = 1 := by
    rw [tubeRadiusReal_rpow, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_eq_one_iff]
    push_cast
    ring
  calc Real.exp (tubeExponent s * v) ^ 3 *
        ∫ omega, tubeMass (tubeRadiusReal v) (brownianImage W hμ.compactAttractor omega) ^ 3 ∂P
      ≤ Real.exp (tubeExponent s * v) ^ 3 * (C * tubeRadiusReal v ^ (3 * tubeExponent s)) :=
        mul_le_mul_of_nonneg_left hmassMean (by positivity)
    _ = C * (Real.exp (tubeExponent s * v) ^ 3 * tubeRadiusReal v ^ (3 * tubeExponent s)) := by
        ring
    _ = C := by rw [hexp, mul_one]

set_option maxHeartbeats 1600000 in
/-- **`thm:neighbourhood-concentration`** under the strong open set condition, given the
moments of the unit-interval Brownian radius: the centred profile satisfies
`eq:neighbourhood-concentration`, and `eq:neighbourhood-grid-concentration` follows. -/
theorem IsNatural.tubeConcentration_of_sosc [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hunit : ∀ p : ℝ, 1 ≤ p →
      Integrable (fun omega => (1 + standardBrownianRadius W omega) ^ p) P) :
    (∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧ ∀ v : ℝ, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v))) ∧
    ∀ t : ℝ, ∀ᵐ omega ∂P, Tendsto
      (fun n : ℕ => centeredBrownianTubeProfile W P hμ.compactAttractor s
        ((n : ℝ) + t) omega) atTop (nhds 0) := by
  classical
  -- the moment bounds of `thm:neighbourhood-moments`
  have hupper' := hμ.tubeMomentUpper_of_standardRadiusMoments S hdim hs0 hW hunit
  have hmom : ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧ ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      Integrable (fun omega => (tubeArea rho (brownianImage W hμ.compactAttractor omega)) ^ q) P ∧
      Integrable (fun omega => (tubeMass rho (brownianImage W hμ.compactAttractor omega)) ^ q) P ∧
      (∫ omega, (tubeArea rho (brownianImage W hμ.compactAttractor omega)) ^ q ∂P) +
        (∫ omega, (tubeMass rho (brownianImage W hμ.compactAttractor omega)) ^ q ∂P)
          ≤ Cq * rho ^ (q * tubeExponent s) := by
    intro q hq
    obtain ⟨Cq, hCq, hqbound⟩ := hupper' q hq
    exact ⟨Cq, hCq, fun rho hrho hrho1 => by
      simpa only [brownianTubeArea] using hqbound rho hrho hrho1⟩
  obtain ⟨B, hB, hprofile⟩ :=
    hμ.exists_brownianTubeProfile_lpNorm_bound_of_tubeMomentsUpper hW S hmom
  obtain ⟨C3, hC3, hcube⟩ :=
    hμ.exists_brownianTubeProfile_cube_bound_of_tubeMomentsUpper S hW hmom
  -- `eq:neighbourhood-defect-mean` below every node
  obtain ⟨CD, η, hCD, hη, -, hnode⟩ :=
    hμ.exists_tubeDefect_node_of_sosc S hW hs0 hs1 hsosc hdim
      (hμ.exists_tubeArea_mean_bound_of_tubeMoments S hupper')
  -- the partition of `thm:stopping-overlap`
  obtain ⟨U, hU, -⟩ := hsosc
  obtain ⟨M, -, hcolor⟩ := hU.exists_stopping_coloring S
  -- the constants
  have hLpos : 0 < Real.log (Hutchinson.maxRatio S)⁻¹ := S.log_inv_maxRatio_pos
  have hrmin := S.minRatio_pos
  have hrmin1 := S.minRatio_le_one
  have hv₀0 : 0 ≤ Real.log (S.minRatio)⁻¹ := Real.log_nonneg ((one_le_inv₀ hrmin).mpr hrmin1)
  have hγ0 : 0 < min (s / 2) (η / 8) := lt_min (by positivity) (by positivity)
  have hε0 : 0 < η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4 := by positivity
  have hK₁0 : 0 ≤ (CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹) := by
    positivity
  -- the estimate at large scales, with `u = r`
  have hlarge : ∀ v : ℝ, Real.log (S.minRatio)⁻¹ ≤ v →
      MinkowskiL2Recurrence.centeredL2Norm (brownianTubeProfile W hμ.compactAttractor s v) P
        ≤ (Real.sqrt M * B +
            Real.sqrt ((CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹))) *
          Real.exp (-min (s / 2) (η / 8) * v) := by
    intro v hv
    have hv0 : 0 ≤ v := hv₀0.trans hv
    have hr0 : 0 < tubeRadiusReal v := tubeRadiusReal_pos v
    have hr1 : tubeRadiusReal v ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.mpr hv0)
    have hrmin' : tubeRadiusReal v ≤ S.minRatio := by
      unfold tubeRadiusReal
      calc Real.exp (-v) ≤ Real.exp (-Real.log (S.minRatio)⁻¹) := Real.exp_le_exp.2 (by linarith)
        _ = S.minRatio := by rw [Real.log_inv, neg_neg, Real.exp_log hrmin]
    have hru : tubeRadiusReal v ^ 2 ≤ S.minRatio * tubeRadiusReal v := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hrmin' hr0.le
    have hrr : tubeRadiusReal v ^ 2 ≤ tubeRadiusReal v := by
      rw [sq]
      exact mul_le_of_le_one_left hr0.le hr1
    obtain ⟨n, hn⟩ := S.exists_stoppingDepth hr0
    obtain ⟨c, hc⟩ := hcolor (tubeRadiusReal v) hr0 hr1 n hn
    -- the sum `Y` over the leaves and the error `F`
    obtain ⟨Y, hY⟩ : ∃ Y : Omega → ℝ, Y = fun omega =>
        ∑ L : S.StoppingLeaves (tubeRadiusReal v) n stoppingRoot, normalizedTubeMass s v
          (brownianImage W (hμ.attractor.stoppingCylinder S
            (S.stoppingLeafWord (tubeRadiusReal v) L).1
            (S.stoppingLeafWord (tubeRadiusReal v) L).2) omega) := ⟨_, rfl⟩
    obtain ⟨F, hF⟩ : ∃ F : Omega → ℝ, F = fun omega =>
        normalizedTubeDefect s v (fun L : S.StoppingLeaves (tubeRadiusReal v) n stoppingRoot =>
          brownianImage W (hμ.attractor.stoppingCylinder S
            (S.stoppingLeafWord (tubeRadiusReal v) L).1
            (S.stoppingLeafWord (tubeRadiusReal v) L).2) omega) := ⟨_, rfl⟩
    have hXYF : brownianTubeProfile W hμ.compactAttractor s v =ᵐ[P]
        fun omega => Y omega - F omega := by
      filter_upwards [hW.ae_continuous] with omega homega
      rw [hY, hF]
      dsimp only
      rw [← normalizedTubeMass_compactUnion_eq_sum_sub_defect,
        hμ.attractor.compactUnion_brownianStoppingCylinder_leaves_eq S (tubeRadiusReal v) n
          stoppingRoot homega, hμ.attractor.stoppingCylinder_root S]
      rfl
    -- `eq:stopping-neighbourhood-variance`
    have hYvar := hμ.centeredL2Norm_sum_leaves_le S hW hs0 hdim hB.le hprofile hr0 hr1 hn hru c hc
    have hYmem : MemLp Y 2 P := by
      rw [hY]
      exact hYvar.1
    have hYcent : MinkowskiL2Recurrence.centeredL2Norm Y P
        ≤ Real.sqrt M * B * tubeRadiusReal v ^ (s / 2) := by
      rw [hY]
      exact hYvar.2
    -- the third moment of `Y`
    have hY3 := hμ.integrable_and_integral_cube_sum_leaves_le S hW hs0 hdim hC3.le hcube hr0 hr1 hn hru
    have hY3int : Integrable (fun omega => Y omega ^ 3) P := by
      rw [hY]
      exact hY3.1
    have hY3le : (∫ omega, Y omega ^ 3 ∂P) ≤ C3 := by
      rw [hY]
      exact hY3.2
    -- `eq:stopping-neighbourhood-defect`
    obtain ⟨hLDint, hLDle⟩ := hμ.integrable_and_integral_stoppingLeafDefect_le S hW hdim hCD.le
      hη.le hnode hr0 hr0 hr1 hrr n stoppingRoot
    have hFae : F =ᵐ[P] fun omega => Real.exp (tubeExponent s * v) *
        hμ.stoppingLeafDefect S W (tubeRadiusReal v) (tubeRadiusReal v) n stoppingRoot omega := by
      filter_upwards [hW.ae_continuous] with omega homega
      rw [hF]
      dsimp only
      rw [normalizedTubeDefect, hμ.stoppingLeafDefect_eq_tubeDefect S (tubeRadiusReal v)
        (tubeRadiusReal v) n stoppingRoot homega]
    have hFint : Integrable F P := (hLDint.const_mul _).congr hFae.symm
    have hF0 : ∀ omega, 0 ≤ F omega := fun omega => by
      rw [hF]
      exact normalizedTubeDefect_nonneg _ _ _
    have hFY : ∀ omega, F omega ≤ Y omega := fun omega => by
      rw [hF, hY]
      dsimp only
      unfold normalizedTubeDefect tubeDefect normalizedTubeMass
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (tubeMass_nonneg _ _)) (Real.exp_pos _).le
    have hnu : S.stoppingGenerationCount (tubeRadiusReal v) stoppingRoot
        = 1 + v / Real.log (Hutchinson.maxRatio S)⁻¹ := by
      rw [S.stoppingGenerationCount_root hr0 hr1]
      congr 2
      rw [tubeRadiusReal, ← Real.exp_neg, neg_neg, Real.log_exp]
    have hFmean : (∫ omega, F omega ∂P)
        ≤ CD * Real.exp (-(η * v)) * (1 + v / Real.log (Hutchinson.maxRatio S)⁻¹) := by
      rw [integral_congr_ae hFae, integral_const_mul]
      have hexp : Real.exp (tubeExponent s * v) * (Real.exp (-(-η * v)) *
          Real.exp (-((tubeExponent s + 2 * η) * v))) = Real.exp (-(η * v)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc Real.exp (tubeExponent s * v) * ∫ omega,
            hμ.stoppingLeafDefect S W (tubeRadiusReal v) (tubeRadiusReal v) n stoppingRoot omega ∂P
          ≤ Real.exp (tubeExponent s * v) * (CD * tubeRadiusReal v ^ (-η) *
              tubeRadiusReal v ^ (tubeExponent s + 2 * η) * S.stoppingWeight s stoppingRoot *
              S.stoppingGenerationCount (tubeRadiusReal v) stoppingRoot) :=
            mul_le_mul_of_nonneg_left hLDle (Real.exp_pos _).le
        _ = CD * (Real.exp (tubeExponent s * v) * (Real.exp (-(-η * v)) *
              Real.exp (-((tubeExponent s + 2 * η) * v)))) *
              (1 + v / Real.log (Hutchinson.maxRatio S)⁻¹) := by
            rw [hnu, tubeRadiusReal_rpow, tubeRadiusReal_rpow, stoppingWeight_root]
            ring
        _ = _ := by rw [hexp]
    -- the third moment of `F`
    have hF3int : Integrable (fun omega => F omega ^ 3) P := by
      refine hY3int.mono' (hFint.aestronglyMeasurable.pow 3) ?_
      filter_upwards with omega
      rw [Real.norm_of_nonneg (pow_nonneg (hF0 omega) 3)]
      exact pow_le_pow_left₀ (hF0 omega) (hFY omega) 3
    have hF3 : (∫ omega, F omega ^ 3 ∂P) ≤ C3 :=
      (integral_mono hF3int hY3int fun omega =>
        pow_le_pow_left₀ (hF0 omega) (hFY omega) 3).trans hY3le
    -- interpolation between the first and third moments
    have hT0 : 0 < Real.exp (η * v / 2) := Real.exp_pos _
    have hA0 : 0 ≤ CD * Real.exp (-(η * v)) * (1 + v / Real.log (Hutchinson.maxRatio S)⁻¹) := by
      positivity
    obtain ⟨hFmem, hFlp⟩ := memLp_two_and_lpNorm_le_of_first_third hFint hF3int
      (Filter.Eventually.of_forall hF0) hT0 hA0 hC3.le hFmean hF3
    have hTA : Real.exp (η * v / 2) *
          (CD * Real.exp (-(η * v)) * (1 + v / Real.log (Hutchinson.maxRatio S)⁻¹)) +
          (Real.exp (η * v / 2))⁻¹ * C3
        ≤ (CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹) *
            Real.exp (-(η * v / 4)) := by
      have h1 : 1 + v / Real.log (Hutchinson.maxRatio S)⁻¹
          ≤ (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹) * Real.exp (η * v / 4) := by
        have h := one_add_le_mul_exp hε0 (div_nonneg hv0 hLpos.le)
        have hcancel : η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4 *
            (v / Real.log (Hutchinson.maxRatio S)⁻¹) = η * v / 4 := by
          calc η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4 *
                (v / Real.log (Hutchinson.maxRatio S)⁻¹)
              = η * v / 4 * (Real.log (Hutchinson.maxRatio S)⁻¹ /
                  Real.log (Hutchinson.maxRatio S)⁻¹) := by ring
            _ = η * v / 4 := by rw [div_self hLpos.ne', mul_one]
        rwa [hcancel] at h
      have h2 : (1:ℝ) ≤ (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹) *
          Real.exp (η * v / 4) := by
        have := Real.one_le_exp (by positivity : 0 ≤ η * v / 4)
        nlinarith [inv_pos.mpr hε0]
      have hTe : Real.exp (η * v / 2) * Real.exp (-(η * v)) = Real.exp (-(η * v / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hTi : (Real.exp (η * v / 2))⁻¹ = Real.exp (-(η * v / 2)) := by
        rw [← Real.exp_neg]
      have hsplit : Real.exp (-(η * v / 2)) * Real.exp (η * v / 4) = Real.exp (-(η * v / 4)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc Real.exp (η * v / 2) *
            (CD * Real.exp (-(η * v)) * (1 + v / Real.log (Hutchinson.maxRatio S)⁻¹)) +
            (Real.exp (η * v / 2))⁻¹ * C3
          = CD * (Real.exp (η * v / 2) * Real.exp (-(η * v))) *
              (1 + v / Real.log (Hutchinson.maxRatio S)⁻¹) + (Real.exp (η * v / 2))⁻¹ * C3 := by
            ring
        _ = CD * Real.exp (-(η * v / 2)) * (1 + v / Real.log (Hutchinson.maxRatio S)⁻¹) +
              Real.exp (-(η * v / 2)) * C3 := by rw [hTe, hTi]
        _ ≤ CD * Real.exp (-(η * v / 2)) *
              ((1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹) * Real.exp (η * v / 4)) +
              Real.exp (-(η * v / 2)) * (C3 *
                ((1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹) * Real.exp (η * v / 4))) := by
            refine add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
              (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
            exact le_mul_of_one_le_right hC3.le h2
        _ = (CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹) *
              (Real.exp (-(η * v / 2)) * Real.exp (η * v / 4)) := by ring
        _ = _ := by rw [hsplit]
    have hFlp' : lpNorm F 2 P
        ≤ Real.sqrt ((CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹)) *
            Real.exp (-(η * v / 8)) := by
      refine hFlp.trans ?_
      calc Real.sqrt (Real.exp (η * v / 2) *
            (CD * Real.exp (-(η * v)) * (1 + v / Real.log (Hutchinson.maxRatio S)⁻¹)) +
            (Real.exp (η * v / 2))⁻¹ * C3)
          ≤ Real.sqrt ((CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹) *
              Real.exp (-(η * v / 4))) := Real.sqrt_le_sqrt hTA
        _ = _ := by
            rw [Real.sqrt_mul hK₁0, Real.sqrt_eq_rpow (Real.exp _), ← Real.exp_mul]
            congr 2
            ring
    -- the two exponential rates
    have hrate1 : tubeRadiusReal v ^ (s / 2) ≤ Real.exp (-min (s / 2) (η / 8) * v) := by
      rw [tubeRadiusReal_rpow]
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_right (min_le_left (s / 2) (η / 8)) hv0
      linarith
    have hrate2 : Real.exp (-(η * v / 8)) ≤ Real.exp (-min (s / 2) (η / 8) * v) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_right (min_le_right (s / 2) (η / 8)) hv0
      linarith
    -- assembly
    have hXmem : MemLp (brownianTubeProfile W hμ.compactAttractor s v) 2 P :=
      (memLp_congr_ae hXYF).mpr (hYmem.sub hFmem)
    calc MinkowskiL2Recurrence.centeredL2Norm (brownianTubeProfile W hμ.compactAttractor s v) P
        = MinkowskiL2Recurrence.centeredL2Norm (fun omega => Y omega - F omega) P :=
          MinkowskiL2Recurrence.centeredL2Norm_congr hXmem (hYmem.sub hFmem) hXYF
      _ ≤ MinkowskiL2Recurrence.centeredL2Norm Y P + MinkowskiL2Recurrence.centeredL2Norm F P :=
          MinkowskiL2Recurrence.centeredL2Norm_sub_le hYmem hFmem
      _ ≤ Real.sqrt M * B * tubeRadiusReal v ^ (s / 2) + lpNorm F 2 P :=
          add_le_add hYcent (MinkowskiL2Recurrence.centeredL2Norm_le_lpNorm hFmem)
      _ ≤ Real.sqrt M * B * Real.exp (-min (s / 2) (η / 8) * v) +
            Real.sqrt ((CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹)) *
              Real.exp (-min (s / 2) (η / 8) * v) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hrate1 (by positivity)) ?_
          exact hFlp'.trans (mul_le_mul_of_nonneg_left hrate2 (Real.sqrt_nonneg _))
      _ = _ := by ring
  -- all scales
  have hall : ∀ v : ℝ, 0 ≤ v →
      MemLp (brownianTubeProfile W hμ.compactAttractor s v) 2 P ∧
      MinkowskiL2Recurrence.centeredL2Norm (brownianTubeProfile W hμ.compactAttractor s v) P
        ≤ (Real.sqrt M * B +
            Real.sqrt ((CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹)) +
            B * Real.exp (min (s / 2) (η / 8) * Real.log (S.minRatio)⁻¹)) *
          Real.exp (-min (s / 2) (η / 8) * v) := by
    intro v hv
    refine ⟨(hprofile v hv).1, ?_⟩
    by_cases hvv : Real.log (S.minRatio)⁻¹ ≤ v
    · refine (hlarge v hvv).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      have : 0 ≤ B * Real.exp (min (s / 2) (η / 8) * Real.log (S.minRatio)⁻¹) := by positivity
      linarith
    · have hvlt : v < Real.log (S.minRatio)⁻¹ := lt_of_not_ge hvv
      calc MinkowskiL2Recurrence.centeredL2Norm (brownianTubeProfile W hμ.compactAttractor s v) P
          ≤ lpNorm (brownianTubeProfile W hμ.compactAttractor s v) 2 P :=
            MinkowskiL2Recurrence.centeredL2Norm_le_lpNorm (hprofile v hv).1
        _ ≤ B := (hprofile v hv).2
        _ = B * Real.exp (min (s / 2) (η / 8) * Real.log (S.minRatio)⁻¹) *
              Real.exp (-min (s / 2) (η / 8) * Real.log (S.minRatio)⁻¹) := by
            rw [mul_assoc, ← Real.exp_add]
            simp
        _ ≤ B * Real.exp (min (s / 2) (η / 8) * Real.log (S.minRatio)⁻¹) *
              Real.exp (-min (s / 2) (η / 8) * v) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
            nlinarith
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            have : 0 ≤ Real.sqrt M * B +
              Real.sqrt ((CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹)) := by
              positivity
            linarith
  -- the endpoint form
  have hbound : ∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧ ∀ v : ℝ, 0 ≤ v →
      MemLp (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P ∧
      eLpNorm (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P ≤
        ENNReal.ofReal (C * Real.exp (-gamma * v)) := by
    refine ⟨Real.sqrt M * B +
      Real.sqrt ((CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹)) +
      B * Real.exp (min (s / 2) (η / 8) * Real.log (S.minRatio)⁻¹), ?_, min (s / 2) (η / 8), hγ0,
      fun v hv => ?_⟩
    · have : 0 ≤ Real.sqrt M * B +
        Real.sqrt ((CD + C3) * (1 + (η * Real.log (Hutchinson.maxRatio S)⁻¹ / 4)⁻¹)) := by
        positivity
      have : 0 < B * Real.exp (min (s / 2) (η / 8) * Real.log (S.minRatio)⁻¹) := by positivity
      linarith
    · obtain ⟨hmem, hle⟩ := hall v hv
      have hcenter : MemLp (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P := by
        unfold centeredBrownianTubeProfile meanBrownianTubeProfile
        exact hmem.sub (memLp_const _)
      refine ⟨hcenter, ?_⟩
      rw [← ofReal_lpNorm hcenter]
      exact ENNReal.ofReal_le_ofReal hle
  exact ⟨hbound, MinkowskiAlmostSure.tubeGridConcentration_of_exponential_eLpNorm hbound⟩

end System

end

end BrownianImages
