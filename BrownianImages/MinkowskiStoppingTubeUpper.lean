/-
Assembly of the stopping-tree cover and Brownian scaling reduction for the
upper half of `thm:neighbourhood-moments`.

All geometric, finite-sum, and self-similar stopping arguments are proved in
this file and its imports.  The only analytic input left explicit in the final
theorem is integrability of every positive moment of the normalized Brownian
radius on `[0,1]`.
-/
import BrownianImages.MinkowskiStopping
import BrownianImages.MinkowskiBrownianMaximalReduction
import BrownianImages.MinkowskiTubeMeanLower
import BrownianImages.AhlforsRegular

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace System

variable {iota : Type u} [Fintype iota] [Nonempty iota] (S : System iota)

/-! ### Stopping cylinders are affine time copies -/

omit [Nonempty iota] in
/-- A nested stopping cylinder is exactly the affine copy of the attractor
with the word's left endpoint and product ratio. -/
theorem IsAttractor.stoppingCylinder_eq_affineTimeCompact {K : Set ℝ}
    (hK : S.IsAttractor K) (w : StoppingWord iota) :
    hK.stoppingCylinder S w.1 w.2 =
      affineTimeCompact (S.stoppingAnchor w) (S.stoppingLength w)
        hK.toNonemptyCompacts := by
  apply NonemptyCompacts.ext
  rw [hK.coe_stoppingCylinder S w.1 w.2, coe_affineTimeCompact]
  apply Set.image_congr
  intro t ht
  exact S.stoppingMap_eq_zero_add_ratio_mul w.1 w.2 t

omit [Nonempty iota] in
@[simp]
theorem IsAttractor.stoppingCylinder_root {K : Set ℝ}
    (hK : S.IsAttractor K) :
    hK.stoppingCylinder S (stoppingRoot : StoppingWord iota).1
        (stoppingRoot : StoppingWord iota).2 = hK.toNonemptyCompacts := by
  change hK.stoppingCylinder S 0 PUnit.unit = hK.toNonemptyCompacts
  apply NonemptyCompacts.ext
  rw [hK.coe_stoppingCylinder S 0 PUnit.unit,
    IsAttractor.coe_toNonemptyCompacts]
  simp [stoppingMap]

/-! ### The almost-sure stopping-disc cover -/

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  {W : NNReal -> Omega -> Plane}

omit [Nonempty iota] in
/-- The Brownian image of a stopping cylinder lies in the normalized
oscillation disc associated to its affine host interval. -/
theorem IsAttractor.brownianStoppingCylinder_subset_disc
    {K : Set ℝ} (hK : S.IsAttractor K) (hKunit : K ⊆ Set.Icc 0 1)
    (W : NNReal -> Omega -> Plane) (w : StoppingWord iota) {omega : Omega}
    (homega : Continuous (fun t => W t omega)) :
    (brownianImage W (hK.stoppingCylinder S w.1 w.2) omega : Set Plane) ⊆
      Metric.closedBall (W (S.stoppingAnchor w) omega)
        (brownianIntervalOscillationRadius W (S.stoppingAnchor w)
          (S.stoppingLength w) omega) := by
  rw [hK.stoppingCylinder_eq_affineTimeCompact S w]
  exact affineBrownianCompactPiece_subset_intervalOscillation_disc
    (S.stoppingLength_ne_zero w) hKunit homega

omit [Nonempty iota] in
/-- At every sufficiently deep stopping level, the full Brownian attractor
image is covered almost surely by the stopping oscillation discs. -/
theorem IsPlanarBrownian.ae_stopping_disc_cover
    (hW : IsPlanarBrownian W P) {K : Set ℝ} (hK : S.IsAttractor K)
    (hKunit : K ⊆ Set.Icc 0 1) (delta : ℝ) (n : ℕ) :
    ∀ᵐ omega ∂P,
      (brownianImage W hK.toNonemptyCompacts omega : Set Plane) ⊆
        ⋃ leaf : S.StoppingLeaves delta n (stoppingRoot : StoppingWord iota),
          Metric.closedBall
            (W (S.stoppingAnchor (S.stoppingLeafWord delta leaf)) omega)
            (brownianIntervalOscillationRadius W
              (S.stoppingAnchor (S.stoppingLeafWord delta leaf))
              (S.stoppingLength (S.stoppingLeafWord delta leaf)) omega) := by
  filter_upwards [hW.ae_continuous] with omega homega
  intro x hx
  have hxroot : x ∈ brownianImage W
      (hK.stoppingCylinder S (stoppingRoot : StoppingWord iota).1
        (stoppingRoot : StoppingWord iota).2) omega := by
    simpa [hK.stoppingCylinder_root S]
      using hx
  change x ∈ (brownianImage W
    (hK.stoppingCylinder S (stoppingRoot : StoppingWord iota).1
      (stoppingRoot : StoppingWord iota).2) omega : Set Plane) at hxroot
  rw [coe_brownianImage_of_continuous _ homega] at hxroot
  obtain ⟨t, htroot, rfl⟩ := hxroot
  obtain ⟨leaf, htleaf⟩ :=
    hK.exists_stoppingLeaf_mem S delta n (stoppingRoot : StoppingWord iota)
      htroot
  apply Set.mem_iUnion.2
  refine ⟨leaf, ?_⟩
  apply hK.brownianStoppingCylinder_subset_disc S hKunit W
    (S.stoppingLeafWord delta leaf) homega
  rw [coe_brownianImage_of_continuous _ homega]
  exact ⟨t, htleaf, rfl⟩

/-! ### Fixed-radius moment assembly -/

/-- Rpower form of squaring followed by a real power, for a nonnegative
base. -/
theorem sq_rpow_eq_rpow_two_mul {x q : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ q = x ^ (2 * q) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

/-- The complete upper estimate at one radius, before replacing the stopping
cardinality by its deterministic power bound.  Every local integral has
already been reduced to the same unit-interval Brownian maximal moment. -/
theorem IsPlanarBrownian.stopping_tube_moments
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {K : Set ℝ} (hK : S.IsAttractor K) (hKunit : K ⊆ Set.Icc 0 1)
    {s r q : ℝ} (_hdim : S.IsDimension s) (hr : 0 < r) (hq : 1 ≤ q)
    {n : ℕ} (hscale : Hutchinson.maxRatio S ^ n ≤ r ^ 2)
    (hunit : Integrable (fun omega =>
      (1 + standardBrownianRadius W omega) ^ (2 * q)) P) :
    let J := S.StoppingLeaves (r ^ 2) n (stoppingRoot : StoppingWord iota)
    Integrable
        (fun omega => (brownianTubeArea W hK.toNonemptyCompacts r omega) ^ q) P ∧
      Integrable
        (fun omega =>
          (tubeMass r (brownianImage W hK.toNonemptyCompacts omega)) ^ q) P ∧
      (∫ omega,
          (brownianTubeArea W hK.toNonemptyCompacts r omega) ^ q ∂P) ≤
        Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ _leaf : J,
            r ^ (2 * q) *
              ∫ omega, (1 + standardBrownianRadius W omega) ^ (2 * q) ∂P ∧
      (∫ omega,
          (tubeMass r (brownianImage W hK.toNonemptyCompacts omega)) ^ q ∂P) ≤
        Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          ∑ _leaf : J,
            r ^ (2 * q) *
              ∫ omega, (1 + standardBrownianRadius W omega) ^ (2 * q) ∂P := by
  dsimp only
  let J := S.StoppingLeaves (r ^ 2) n (stoppingRoot : StoppingWord iota)
  let word : J -> StoppingWord iota := fun leaf =>
    S.stoppingLeafWord (r ^ 2) leaf
  let radius : J -> Omega -> ℝ := fun leaf =>
    brownianIntervalOscillationRadius W (S.stoppingAnchor (word leaf))
      (S.stoppingLength (word leaf))
  have hradius_nonneg : ∀ leaf omega, 0 ≤ radius leaf omega := by
    intro leaf omega
    exact brownianIntervalOscillationRadius_nonneg W _ _ omega
  have hradius_meas : ∀ leaf, AEMeasurable (radius leaf) P := by
    intro leaf
    exact aemeasurable_const.mul
      (hW.aemeasurable_rescaledBrownianRadius
        (S.stoppingAnchor (word leaf))
        (S.stoppingLength_ne_zero (word leaf)))
  have hlocal : ∀ leaf : J,
      Integrable (fun omega => ((r + radius leaf omega) ^ 2) ^ q) P ∧
      (∫ omega, ((r + radius leaf omega) ^ 2) ^ q ∂P) ≤
        r ^ (2 * q) *
          ∫ omega, (1 + standardBrownianRadius W omega) ^ (2 * q) ∂P := by
    intro leaf
    have hlen : (S.stoppingLength (word leaf) : ℝ) ≤ r ^ 2 := by
      change S.stoppingRatio (word leaf) ≤ r ^ 2
      exact S.stoppingLeafRatio_le hscale leaf
    have hp : 1 ≤ 2 * q := by nlinarith
    obtain ⟨hint, hbound⟩ :=
      hW.intervalOscillation_moment_le_of_standard
        (S.stoppingAnchor (word leaf))
        (S.stoppingLength_ne_zero (word leaf)) hr hp hlen hunit
    have heq : (fun omega => ((r + radius leaf omega) ^ 2) ^ q) =
        fun omega => (r + radius leaf omega) ^ (2 * q) := by
      funext omega
      exact sq_rpow_eq_rpow_two_mul
        (add_nonneg hr.le (hradius_nonneg leaf omega))
    rw [heq]
    exact ⟨hint, hbound⟩
  obtain ⟨hareaInt, hmassInt, harea, hmass⟩ :=
    random_tube_moments_of_finite_disc_cover
      (P := P) (J := J)
      (fun omega => brownianImage W hK.toNonemptyCompacts omega)
      (hW.aemeasurable_brownianImage hK.toNonemptyCompacts)
      (fun leaf omega => W (S.stoppingAnchor (word leaf)) omega)
      radius hr hq hradius_nonneg hradius_meas
      (by
        simpa [J, word, radius] using
          (BrownianImages.System.IsPlanarBrownian.ae_stopping_disc_cover
            (S := S) hW hK hKunit (r ^ 2) n))
      (fun leaf => (hlocal leaf).1)
  refine ⟨hareaInt, hmassInt, ?_, ?_⟩
  · exact harea.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun leaf _ => (hlocal leaf).2)
      (mul_nonneg (Real.rpow_nonneg Real.pi_nonneg q)
        (Real.rpow_nonneg (Nat.cast_nonneg _) (q - 1))))
  · exact hmass.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun leaf _ => (hlocal leaf).2)
      (mul_nonneg (Real.rpow_nonneg Real.pi_nonneg q)
        (Real.rpow_nonneg (Nat.cast_nonneg _) (q - 1))))

/-- The preceding estimate with its constant leaf sum evaluated. -/
theorem IsPlanarBrownian.stopping_tube_moments_card_bound
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {K : Set ℝ} (hK : S.IsAttractor K) (hKunit : K ⊆ Set.Icc 0 1)
    {s r q : ℝ} (hdim : S.IsDimension s) (hr : 0 < r) (hq : 1 ≤ q)
    {n : ℕ} (hscale : Hutchinson.maxRatio S ^ n ≤ r ^ 2)
    (hunit : Integrable (fun omega =>
      (1 + standardBrownianRadius W omega) ^ (2 * q)) P) :
    let J := S.StoppingLeaves (r ^ 2) n (stoppingRoot : StoppingWord iota)
    Integrable
        (fun omega => (brownianTubeArea W hK.toNonemptyCompacts r omega) ^ q) P ∧
      Integrable
        (fun omega =>
          (tubeMass r (brownianImage W hK.toNonemptyCompacts omega)) ^ q) P ∧
      (∫ omega,
          (brownianTubeArea W hK.toNonemptyCompacts r omega) ^ q ∂P) ≤
        Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          (Fintype.card J : ℝ) * r ^ (2 * q) *
            ∫ omega, (1 + standardBrownianRadius W omega) ^ (2 * q) ∂P ∧
      (∫ omega,
          (tubeMass r (brownianImage W hK.toNonemptyCompacts omega)) ^ q ∂P) ≤
        Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
          (Fintype.card J : ℝ) * r ^ (2 * q) *
            ∫ omega, (1 + standardBrownianRadius W omega) ^ (2 * q) ∂P := by
  dsimp only
  obtain ⟨hareaInt, hmassInt, harea, hmass⟩ :=
    BrownianImages.System.IsPlanarBrownian.stopping_tube_moments
      (S := S) hW hK hKunit hdim hr hq hscale hunit
  refine ⟨hareaInt, hmassInt, ?_, ?_⟩
  · simpa [nsmul_eq_mul, mul_assoc] using harea
  · simpa [nsmul_eq_mul, mul_assoc] using hmass

/-! ### Cardinality and exponent simplification -/

/-- The stopping-leaf cardinality has the sharp similarity-dimension power
bound. -/
theorem stoppingLeaves_card_le {s delta : ℝ} (hdim : S.IsDimension s)
    (hs : 0 < s) {rmin : ℝ} (hrmin : 0 < rmin) (hrmin1 : rmin ≤ 1)
    (hmin : ∀ i, rmin ≤ S.ratio i) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) {n : ℕ}
    (_hscale : Hutchinson.maxRatio S ^ n ≤ delta) :
    (Fintype.card
      (S.StoppingLeaves delta n (stoppingRoot : StoppingWord iota)) : ℝ) ≤
      (rmin * delta) ^ (-s) := by
  apply card_le_rpow_neg_of_sum_rpow_eq_one
    (fun leaf : S.StoppingLeaves delta n (stoppingRoot : StoppingWord iota) =>
      S.stoppingRatio (S.stoppingLeafWord delta leaf))
    hrmin hdelta hs
  · intro leaf
    exact S.stoppingRatio_lower_of_leaf hrmin.le hrmin1 hdelta.le hdelta1
      hmin leaf
  · simpa using S.sum_stoppingLeafRatio_rpow hdim delta n
      (stoppingRoot : StoppingWord iota)

/-- Numerical cancellation behind the exponent `q * (2 - 2s)`. -/
theorem stopping_card_factor_mul_rpow_le
    {N rmin r s q : ℝ} (hN0 : 0 ≤ N) (hrmin : 0 < rmin)
    (hr : 0 < r) (hq : 1 ≤ q)
    (hN : N ≤ (rmin * r ^ 2) ^ (-s)) :
    N ^ (q - 1) * N * r ^ (2 * q) ≤
      rmin ^ (-s * q) * r ^ (q * tubeExponent s) := by
  let B : ℝ := (rmin * r ^ 2) ^ (-s)
  have hbase : 0 < rmin * r ^ 2 := mul_pos hrmin (sq_pos_of_pos hr)
  have hB : 0 < B := Real.rpow_pos_of_pos hbase (-s)
  have hNpow : N ^ (q - 1) ≤ B ^ (q - 1) :=
    Real.rpow_le_rpow hN0 hN (sub_nonneg.mpr hq)
  have hproduct : N ^ (q - 1) * N ≤ B ^ (q - 1) * B :=
    mul_le_mul hNpow hN hN0 (Real.rpow_nonneg hB.le _)
  have hBcombine : B ^ (q - 1) * B = B ^ q := by
    calc
      B ^ (q - 1) * B = B ^ (q - 1) * B ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = B ^ ((q - 1) + 1) := (Real.rpow_add hB (q - 1) 1).symm
      _ = B ^ q := by ring_nf
  have hrpow : 0 ≤ r ^ (2 * q) := Real.rpow_nonneg hr.le _
  calc
    N ^ (q - 1) * N * r ^ (2 * q) ≤
        (B ^ (q - 1) * B) * r ^ (2 * q) :=
      mul_le_mul_of_nonneg_right hproduct hrpow
    _ = B ^ q * r ^ (2 * q) := by rw [hBcombine]
    _ = (rmin * r ^ 2) ^ (-s * q) * r ^ (2 * q) := by
      rw [← Real.rpow_mul hbase.le]
    _ = (rmin ^ (-s * q) * (r ^ 2) ^ (-s * q)) *
        r ^ (2 * q) := by
      rw [Real.mul_rpow hrmin.le (sq_nonneg r)]
    _ = rmin ^ (-s * q) *
        (r ^ (2 * (-s * q)) * r ^ (2 * q)) := by
      rw [sq_rpow_eq_rpow_two_mul (x := r) (q := -s * q) hr.le]
      ring
    _ = rmin ^ (-s * q) *
        r ^ (2 * (-s * q) + 2 * q) := by
      rw [← Real.rpow_add hr]
    _ = rmin ^ (-s * q) * r ^ (q * tubeExponent s) := by
      congr 2
      unfold tubeExponent
      ring

/-! ### Uniform upper moments -/

/-- The upper half of the tube-moment theorem, reduced to moments of the
Brownian radius on the unit interval.  This is the audit-shaped bridge: all
stopping-tree geometry, cardinality estimates, and powers of the radius have
already been discharged. -/
theorem IsNatural.tubeMomentUpper_of_standardRadiusMoments
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hdim : S.IsDimension s)
    (hmu : S.IsNatural K s mu) (hs : 0 < s)
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (hunit : ∀ p : ℝ, 1 ≤ p →
      Integrable (fun omega =>
        (1 + standardBrownianRadius W omega) ^ p) P) :
    ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        Integrable
          (fun omega =>
            (brownianTubeArea W hmu.compactAttractor r omega) ^ q) P ∧
        Integrable
          (fun omega =>
            (tubeMass r
              (brownianImage W hmu.compactAttractor omega)) ^ q) P ∧
        (∫ omega,
            (brownianTubeArea W hmu.compactAttractor r omega) ^ q ∂P) +
            (∫ omega,
              (tubeMass r
                (brownianImage W hmu.compactAttractor omega)) ^ q ∂P) ≤
          Cq * r ^ (q * tubeExponent s) := by
  obtain ⟨rmin, hrmin, hmin⟩ := AhlforsRegular.exists_ratio_lower S
  obtain ⟨i0⟩ := (‹Nonempty iota›)
  have hrmin1 : rmin ≤ 1 :=
    (hmin i0).trans (S.ratio_lt_one i0).le
  intro q hq
  let M : ℝ := ∫ omega,
    (1 + standardBrownianRadius W omega) ^ (2 * q) ∂P
  let Cq : ℝ :=
    2 * Real.pi ^ q * rmin ^ (-s * q) * (M + 1)
  have htwoq : 1 ≤ 2 * q := by nlinarith
  have hunitq : Integrable (fun omega =>
      (1 + standardBrownianRadius W omega) ^ (2 * q)) P :=
    hunit (2 * q) htwoq
  have hM0 : 0 ≤ M := by
    apply integral_nonneg
    intro omega
    exact Real.rpow_nonneg
      (add_nonneg zero_le_one
        (compactRadius_nonneg (standardBrownianPiece W omega))) _
  have hCq : 0 < Cq := by
    dsimp only [Cq]
    exact mul_pos
      (mul_pos
        (mul_pos two_pos (Real.rpow_pos_of_pos Real.pi_pos q))
        (Real.rpow_pos_of_pos hrmin (-s * q)))
      (by linarith)
  refine ⟨Cq, hCq, ?_⟩
  intro r hr hr1
  have hr_sq_pos : 0 < r ^ 2 := sq_pos_of_pos hr
  have hr_sq_one : r ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1)]
  obtain ⟨n, hscale⟩ := S.exists_stoppingDepth hr_sq_pos
  let J := S.StoppingLeaves (r ^ 2) n
    (stoppingRoot : StoppingWord iota)
  have hfixed :=
    BrownianImages.System.IsPlanarBrownian.stopping_tube_moments_card_bound
      (S := S) hW hmu.attractor hmu.attractor.2.2.1 hdim hr hq hscale hunitq
  dsimp only at hfixed
  have hcard : (Fintype.card J : ℝ) ≤
      (rmin * r ^ 2) ^ (-s) := by
    simpa only [J] using
      S.stoppingLeaves_card_le hdim hs hrmin hrmin1 hmin hr_sq_pos
        hr_sq_one hscale
  have hcardpow :
      (Fintype.card J : ℝ) ^ (q - 1) * (Fintype.card J : ℝ) *
          r ^ (2 * q) ≤
        rmin ^ (-s * q) * r ^ (q * tubeExponent s) :=
    stopping_card_factor_mul_rpow_le (Nat.cast_nonneg _) hrmin hr hq hcard
  have hMle : M ≤ M + 1 := by linarith
  have hright0 : 0 ≤
      rmin ^ (-s * q) * r ^ (q * tubeExponent s) :=
    mul_nonneg (Real.rpow_nonneg hrmin.le _)
      (Real.rpow_nonneg hr.le _)
  have hsingle :
      Real.pi ^ q *
          ((Fintype.card J : ℝ) ^ (q - 1) *
            (Fintype.card J : ℝ) * r ^ (2 * q)) * M ≤
        Real.pi ^ q *
          (rmin ^ (-s * q) * r ^ (q * tubeExponent s)) * (M + 1) := by
    calc
      Real.pi ^ q *
          ((Fintype.card J : ℝ) ^ (q - 1) *
            (Fintype.card J : ℝ) * r ^ (2 * q)) * M =
          Real.pi ^ q *
            (((Fintype.card J : ℝ) ^ (q - 1) *
              (Fintype.card J : ℝ) * r ^ (2 * q)) * M) := by ring
      _ ≤ Real.pi ^ q *
          ((rmin ^ (-s * q) * r ^ (q * tubeExponent s)) * (M + 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hcardpow hMle hM0 hright0)
          (Real.rpow_nonneg Real.pi_nonneg q)
      _ = Real.pi ^ q *
          (rmin ^ (-s * q) * r ^ (q * tubeExponent s)) * (M + 1) := by ring
  refine ⟨hfixed.1, hfixed.2.1, ?_⟩
  calc
    (∫ omega,
        (brownianTubeArea W hmu.compactAttractor r omega) ^ q ∂P) +
        (∫ omega,
          (tubeMass r
            (brownianImage W hmu.compactAttractor omega)) ^ q ∂P) ≤
        (Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
            (Fintype.card J : ℝ) * r ^ (2 * q) * M) +
          (Real.pi ^ q * (Fintype.card J : ℝ) ^ (q - 1) *
            (Fintype.card J : ℝ) * r ^ (2 * q) * M) :=
      add_le_add hfixed.2.2.1 hfixed.2.2.2
    _ ≤
        (Real.pi ^ q *
          (rmin ^ (-s * q) * r ^ (q * tubeExponent s)) * (M + 1)) +
        (Real.pi ^ q *
          (rmin ^ (-s * q) * r ^ (q * tubeExponent s)) * (M + 1)) := by
      apply add_le_add <;> simpa only [mul_assoc] using hsingle
    _ = Cq * r ^ (q * tubeExponent s) := by
      dsimp only [Cq]
      ring

/-- Every logarithmic-scale Brownian tube profile is integrable as soon as
the second moment of the normalized unit-interval Brownian radius is.  Unlike
the small-radius moment estimate, this statement covers negative logarithmic
scales as well: no assumption `tubeRadiusReal v ≤ 1` is used. -/
theorem IsNatural.integrable_brownianTubeProfile_of_standardRadiusSecondMoment
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hdim : S.IsDimension s)
    (hmu : S.IsNatural K s mu) [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P)
    (hunit2 : Integrable (fun omega =>
      (1 + standardBrownianRadius W omega) ^ (2 : ℝ)) P)
    (v : ℝ) :
    Integrable (brownianTubeProfile W hmu.compactAttractor s v) P := by
  let r : ℝ := tubeRadiusReal v
  have hr : 0 < r := tubeRadiusReal_pos v
  obtain ⟨n, hscale⟩ := S.exists_stoppingDepth (sq_pos_of_pos hr)
  have hfixed :=
    BrownianImages.System.IsPlanarBrownian.stopping_tube_moments_card_bound
      (S := S) hW hmu.attractor hmu.attractor.2.2.1 hdim hr
        (show (1 : ℝ) ≤ 1 from le_rfl) hscale (by simpa using hunit2)
  have hmass : Integrable (fun omega =>
      tubeMass r (brownianImage W hmu.compactAttractor omega)) P := by
    simpa only [IsNatural.compactAttractor, Real.rpow_one] using hfixed.2.1
  change Integrable (fun omega =>
    Real.exp (tubeExponent s * v) *
      tubeMass (tubeRadiusReal v)
        (brownianImage W hmu.compactAttractor omega)) P
  simpa only [r] using hmass.const_mul (Real.exp (tubeExponent s * v))

/-- All unit-radius moments in particular supply integrability of the tube
profile at every real logarithmic scale. -/
theorem IsNatural.integrable_brownianTubeProfile_of_standardRadiusMoments
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hdim : S.IsDimension s)
    (hmu : S.IsNatural K s mu) [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P)
    (hunit : ∀ p : ℝ, 1 ≤ p →
      Integrable (fun omega =>
        (1 + standardBrownianRadius W omega) ^ p) P) :
    ∀ v : ℝ,
      Integrable (brownianTubeProfile W hmu.compactAttractor s v) P := by
  intro v
  exact hmu.integrable_brownianTubeProfile_of_standardRadiusSecondMoment
    S hdim hW (hunit 2 (by norm_num)) v

end System

end

end BrownianImages
