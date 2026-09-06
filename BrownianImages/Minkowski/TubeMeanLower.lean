/-
The lower-bound half of `thm:neighbourhood-moments`.

The deterministic input compares the smoothed neighbourhood at radius `2r` with half
the area of the raw radius-`r` neighbourhood.  The probabilistic input says that the
occupation measure is carried by the compact Brownian image on every continuous
sample path.  These facts, the correlation-to-neighbourhood inequality, and a Markov
event split reduce the expected lower bound to the already proved Frostman
correlation estimate.  Integrability of the smoothed neighbourhood is kept explicit:
it is precisely the `q = 1` upper-moment input supplied by the other half of
`thm:neighbourhood-moments`.
-/
import BrownianImages.Minkowski.CorrelationLower
import BrownianImages.Minkowski.OverlapTranslation
import BrownianImages.AhlforsRegular
import BrownianImages.Concentration
import BrownianImages.Endpoints

namespace BrownianImages

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

/-- On the raw radius-`r` neighbourhood, the triangular cut-off at radius `2r` is at
least one half. -/
theorem half_tubeIndicator_le_tubeCutoff_two_mul {r : ℝ} (hr : 0 < r)
    (F : CompactPlane) (x : Plane) :
    (1 / 2 : ℝ) * tubeIndicator r F x ≤ tubeCutoff (2 * r) F x := by
  by_cases hx : x ∈ Metric.thickening r (F : Set Plane)
  · rw [tubeIndicator, Set.indicator_of_mem hx]
    have hdist : Metric.infDist x (F : Set Plane) < r :=
      (Metric.mem_thickening_iff_infDist_lt F.nonempty).mp hx
    have hdiv : Metric.infDist x (F : Set Plane) / (2 * r) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
      linarith
    rw [tubeCutoff]
    exact le_max_of_le_left (by linarith)
  · rw [tubeIndicator, Set.indicator_of_notMem hx, mul_zero]
    exact tubeCutoff_nonneg _ _ _

/-- Deterministic comparison of smoothed and raw neighbourhoods:
`M_{2r}(F) ≥ (1/2) |F_r|`. -/
theorem half_tubeArea_le_tubeMass_two_mul {r : ℝ} (hr : 0 < r)
    (F : CompactPlane) :
    (1 / 2 : ℝ) * tubeArea r F ≤ tubeMass (2 * r) F := by
  rw [← integral_tubeIndicator, tubeMass, ← integral_const_mul]
  exact integral_mono
    ((integrable_tubeIndicator r F).const_mul (1 / 2 : ℝ))
    (integrable_tubeCutoff (by positivity : (0 : ℝ) < 2 * r) F)
    (half_tubeIndicator_le_tubeCutoff_two_mul hr F)

variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} {W : ℝ≥0 → Omega → Plane}

omit [MeasurableSpace Omega] in
/-- On a continuous path, any time measure carried by `K` pushes forward to a
measure carried by the compact image of `K`. -/
theorem occupation_compl_brownianImage_eq_zero_of_continuous
    (K : NonemptyCompacts ℝ) (mu : Measure ℝ) {omega : Omega}
    (homega : Continuous (fun t : ℝ≥0 => W t omega))
    (hsupport : mu (K : Set ℝ)ᶜ = 0) :
    occupation W mu omega (brownianImage W K omega : Set Plane)ᶜ = 0 := by
  rw [occupation, Measure.map_apply (measurable_pathMap homega)
    (brownianImage W K omega).isCompact.isClosed.measurableSet.compl]
  apply measure_mono_null _ hsupport
  intro t ht htK
  apply ht
  rw [coe_brownianImage_of_continuous K homega]
  exact ⟨t, htK, rfl⟩

/-- Almost surely, the occupation measure is carried by the compact Brownian
image of every compact set carrying the time measure. -/
theorem IsPlanarBrownian.ae_occupation_compl_brownianImage_eq_zero
    (hW : IsPlanarBrownian W P) (K : NonemptyCompacts ℝ) (mu : Measure ℝ)
    (hsupport : mu (K : Set ℝ)ᶜ = 0) :
    ∀ᵐ omega ∂P,
      occupation W mu omega (brownianImage W K omega : Set Plane)ᶜ = 0 := by
  filter_upwards [hW.ae_continuous] with omega homega
  exact occupation_compl_brownianImage_eq_zero_of_continuous K mu homega hsupport

/-- A reusable Markov-event lower bound.  If `Y` has mean at most `b`, then
`Y < 2b` with probability at least one half.  On that event a reciprocal
pointwise lower bound for `X` gives the stated quarter-factor estimate. -/
theorem integral_ge_div_four_mul_of_reciprocal_lower
    [IsProbabilityMeasure P] {X Y : Omega → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hXint : Integrable X P) (hYint : Integrable Y P)
    (hXnonneg : ∀ᵐ omega ∂P, 0 ≤ X omega)
    (hYnonneg : ∀ᵐ omega ∂P, 0 ≤ Y omega)
    (hYpos : ∀ᵐ omega ∂P, 0 < Y omega)
    (hYmean : ∫ omega, Y omega ∂P ≤ b)
    (hreciprocal : ∀ᵐ omega ∂P, a / Y omega ≤ X omega) :
    a / (4 * b) ≤ ∫ omega, X omega ∂P := by
  let bad : Set Omega := {omega | 2 * b ≤ Y omega}
  have hbad : NullMeasurableSet bad P := by
    exact hYint.aemeasurable.nullMeasurable measurableSet_Ici
  have hmarkov : (2 * b) * P.real bad ≤ ∫ omega, Y omega ∂P := by
    exact mul_meas_ge_le_integral_of_nonneg hYnonneg hYint (2 * b)
  have hbad_le : P.real bad ≤ 1 / 2 := by
    nlinarith [hmarkov.trans hYmean]
  have hgood : 1 / 2 ≤ P.real badᶜ := by
    rw [probReal_compl_eq_one_sub₀ hbad]
    linarith
  have hpoint : ∀ᵐ omega ∂P.restrict badᶜ, a / (2 * b) ≤ X omega := by
    filter_upwards [ae_restrict_mem₀ hbad.compl,
      ae_restrict_of_ae hYpos, ae_restrict_of_ae hreciprocal] with
      omega homega hYomega hrecip
    have hYlt : Y omega < 2 * b := by
      exact not_le.mp (show omega ∉ bad from homega)
    calc
      a / (2 * b) ≤ a / Y omega := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b) hYomega]
        nlinarith
      _ ≤ X omega := hrecip
  have hconst_le :
      (a / (2 * b)) * P.real badᶜ ≤ ∫ omega in badᶜ, X omega ∂P := by
    have h := integral_mono_ae
      (integrable_const (a / (2 * b)) :
        Integrable (fun _ : Omega => a / (2 * b)) (P.restrict badᶜ))
      (hXint.mono_measure Measure.restrict_le_self) hpoint
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
      mul_comm] using h
  have hrestrict_le : (∫ omega in badᶜ, X omega ∂P) ≤ ∫ omega, X omega ∂P :=
    integral_mono_measure Measure.restrict_le_self hXnonneg hXint
  calc
    a / (4 * b) = (a / (2 * b)) * (1 / 2) := by field_simp; ring
    _ ≤ (a / (2 * b)) * P.real badᶜ :=
      mul_le_mul_of_nonneg_left hgood
        (div_nonneg ha.le (show 0 ≤ 2 * b by positivity))
    _ ≤ ∫ omega in badᶜ, X omega ∂P := hconst_le
    _ ≤ ∫ omega, X omega ∂P := hrestrict_le

/-- The real correlation of the occupation measure at a fixed radius is an
almost everywhere measurable random variable. -/
theorem IsPlanarBrownian.aemeasurable_occupationCorr
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (r : ℝ) :
    AEMeasurable (fun omega => (corr (occupation W mu omega) r).toReal) P := by
  refine ((ENNReal.measurable_toReal.comp (measurable_corr r)).comp_aemeasurable
    (hW.aemeasurable_occupationProb mu)).congr ?_
  filter_upwards [hW.ae_occupationProb_toMeasure mu] with omega homega
  simp only [Function.comp_apply]
  rw [homega]

/-- The real correlation of a probability occupation measure lies in `[0,1]`,
and is therefore integrable at every fixed radius. -/
theorem IsPlanarBrownian.integrable_occupationCorr
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (r : ℝ) :
    Integrable (fun omega => (corr (occupation W mu omega) r).toReal) P := by
  refine (integrable_const (1 : ℝ)).mono
    (hW.aemeasurable_occupationCorr mu r).aestronglyMeasurable ?_
  filter_upwards [hW.ae_isProbabilityMeasure_occupation mu] with omega homega
  letI := homega
  have hle : (corr (occupation W mu omega) r).toReal ≤ 1 := by
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, norm_one]
  exact hle

/-- The deterministic correlation-to-area estimate and the comparison
`M_r ≥ |F_{r/2}|/2` give the exact reciprocal lower bound used in the event
split. -/
theorem IsPlanarBrownian.ae_tubeMass_ge_discArea_div_corr
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (K : NonemptyCompacts ℝ) (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hsupport : mu (K : Set ℝ)ᶜ = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ omega ∂P,
      (Real.pi * r ^ 2 / 8) /
          (corr (occupation W mu omega) r).toReal ≤
        tubeMass r (brownianImage W K omega) := by
  filter_upwards [hW.ae_isProbabilityMeasure_occupation mu,
    hW.ae_occupation_compl_brownianImage_eq_zero K mu hsupport] with
    omega hprob hsupp
  letI := hprob
  have harea :
      Real.pi * (r / 2) ^ 2 /
          (corr (occupation W mu omega) r).toReal ≤
        tubeArea (r / 2) (brownianImage W K omega) := by
    simpa only [show 2 * (r / 2) = r by ring] using
      (tubeArea_ge_discArea_div_corr (occupation W mu omega)
        (brownianImage W K omega) (half_pos hr) hsupp)
  have hmass :
      (1 / 2 : ℝ) * tubeArea (r / 2) (brownianImage W K omega) ≤
        tubeMass r (brownianImage W K omega) := by
    simpa only [show 2 * (r / 2) = r by ring] using
      (half_tubeArea_le_tubeMass_two_mul (half_pos hr)
        (brownianImage W K omega))
  calc
    (Real.pi * r ^ 2 / 8) /
          (corr (occupation W mu omega) r).toReal =
        (1 / 2 : ℝ) *
          (Real.pi * (r / 2) ^ 2 /
            (corr (occupation W mu omega) r).toReal) := by ring
    _ ≤ (1 / 2 : ℝ) * tubeArea (r / 2) (brownianImage W K omega) :=
      mul_le_mul_of_nonneg_left harea (by norm_num)
    _ ≤ tubeMass r (brownianImage W K omega) := hmass

/-- Positive-radius occupation correlation is strictly positive almost surely.
This is the positivity needed at the division step of the event argument. -/
theorem IsPlanarBrownian.ae_occupationCorr_pos
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (K : NonemptyCompacts ℝ) (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hsupport : mu (K : Set ℝ)ᶜ = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ omega ∂P, 0 < (corr (occupation W mu omega) r).toReal := by
  filter_upwards [hW.ae_isProbabilityMeasure_occupation mu,
    hW.ae_occupation_compl_brownianImage_eq_zero K mu hsupport] with
    omega hprob hsupp
  letI := hprob
  have hpos : 0 < corr (occupation W mu omega) r := by
    simpa only [show 2 * (r / 2) = r by ring] using
      (corr_two_mul_pos_of_support (occupation W mu omega)
        (brownianImage W K omega) (half_pos hr) hsupp)
  exact ENNReal.toReal_pos hpos.ne' (corr_ne_top (occupation W mu omega) r)

/-- The expectation-level lower bound, in the general Frostman form.  The sole
extra analytic input is integrability of the radius-`r` smoothed neighbourhood.  The
proof uses the event where occupation correlation is at most twice its mean;
no unproved Jensen or reciprocal-integrability step is hidden here. -/
theorem exists_expected_tubeMass_lower_of_frostman
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (hmu : IsFrostman s A mu)
    (K : NonemptyCompacts ℝ) (hsupport : mu (K : Set ℝ)ᶜ = 0)
    (hint : ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable (fun omega => tubeMass r (brownianImage W K omega)) P) :
    ∃ c > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      c * r ^ (tubeExponent s) ≤
        ∫ omega, tubeMass r (brownianImage W K omega) ∂P := by
  let C : ℝ := max 1 (A * ∫ x : ℝ, logKern s x)
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  have hprofile_le : ∀ v : ℝ, H s mu v ≤ C := by
    intro v
    exact (Concentration.H_le hs0 hs1 hmu v).trans (le_max_right _ _)
  let c : ℝ := Real.pi / (32 * C)
  have hcpos : 0 < c := div_pos Real.pi_pos (by positivity)
  refine ⟨c, hcpos, fun r hr hr1 => ?_⟩
  let X : Omega → ℝ := fun omega => tubeMass r (brownianImage W K omega)
  let Y : Omega → ℝ := fun omega => (corr (occupation W mu omega) r).toReal
  let a : ℝ := Real.pi * r ^ 2 / 8
  let b : ℝ := C * r ^ (2 * s)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    exact mul_pos hCpos (Real.rpow_pos_of_pos hr _)
  have hYmean : ∫ omega, Y omega ∂P ≤ b := by
    calc
      ∫ omega, Y omega ∂P = expCorr W P mu r := rfl
      _ = r ^ (2 * s) * H s mu (Real.log r⁻¹) := smoothing hW hs0 hs1 hmu hr
      _ ≤ r ^ (2 * s) * C :=
        mul_le_mul_of_nonneg_left (hprofile_le _) (Real.rpow_nonneg hr.le _)
      _ = b := by simp only [b]; ring
  have hmarkov : a / (4 * b) ≤ ∫ omega, X omega ∂P :=
    integral_ge_div_four_mul_of_reciprocal_lower ha hb
      (hint r hr hr1) (hW.integrable_occupationCorr mu r)
      (Filter.Eventually.of_forall fun omega => tubeMass_nonneg r (brownianImage W K omega))
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (hW.ae_occupationCorr_pos K mu hsupport hr) hYmean
      (hW.ae_tubeMass_ge_discArea_div_corr K mu hsupport hr)
  calc
    c * r ^ (tubeExponent s) = a / (4 * b) := by
      dsimp [c, a, b]
      rw [tubeExponent, Real.rpow_sub hr, Real.rpow_two]
      field_simp
      ring
    _ ≤ ∫ omega, X omega ∂P := hmarkov

namespace System

variable {iota : Type*} [Fintype iota]

/-- The lower half of `thm:neighbourhood-moments` for a separated self-similar natural
measure.  `IsDimension` is carried to match the theorem's paper-level data;
`IsNatural` already supplies the probability measure and compact attractor.
Only the `q = 1` neighbourhood integrability input from the upper-moment argument
remains explicit. -/
theorem IsNatural.exists_expected_tubeMass_lower_of_integrable
    (S : System iota) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hsep : S.IntervalSeparated) (_hdim : S.IsDimension s)
    (hmu : S.IsNatural K s mu) (hs0 : 0 < s) (hs1 : s < 1)
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (hint : ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable (fun omega =>
        tubeMass r (brownianImage W hmu.compactAttractor omega)) P) :
    ∃ c > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      c * r ^ (tubeExponent s) ≤
        ∫ omega, tubeMass r (brownianImage W hmu.compactAttractor omega) ∂P := by
  letI := hmu.isProbabilityMeasure
  obtain ⟨rho, hsepIcc⟩ := hsep
  have hsepK : S.StronglySeparated K rho :=
    System.StronglySeparated.mono S hmu.attractor.2.2.1 hsepIcc
  obtain ⟨A, hFrostman⟩ :=
    AhlforsRegular.exists_isFrostman_of_isNatural hs0 hsepK hmu
  exact exists_expected_tubeMass_lower_of_frostman hW hs0 hs1 mu hFrostman
    hmu.compactAttractor (by simpa using hmu.support) hint

/-- Direct bridge from the upper-moment half of `thm:neighbourhood-moments` to its lower
half.  Taking `q = 1` supplies the only fact the Markov proof still needs,
namely integrability of `M_r(R)`. -/
theorem IsNatural.exists_expected_tubeMass_lower_of_tubeMomentUpper
    [Nonempty iota] (S : System iota) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    (hmu : S.IsNatural K s mu) (hs0 : 0 < s) (hs1 : s < 1)
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (hupper : ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        Integrable
          (fun omega => (brownianTubeArea W hmu.compactAttractor r omega) ^ q) P ∧
        Integrable
          (fun omega =>
            (tubeMass r (brownianImage W hmu.compactAttractor omega)) ^ q) P ∧
        (∫ omega, (brownianTubeArea W hmu.compactAttractor r omega) ^ q ∂P) +
            (∫ omega,
              (tubeMass r (brownianImage W hmu.compactAttractor omega)) ^ q ∂P)
          ≤ Cq * r ^ (q * tubeExponent s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable
        (fun omega => tubeMass r (brownianImage W hmu.compactAttractor omega)) P ∧
      c * r ^ tubeExponent s ≤
        ∫ omega, tubeMass r (brownianImage W hmu.compactAttractor omega) ∂P := by
  obtain ⟨C1, hC1, hupper1⟩ := hupper 1 le_rfl
  have hint : ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable
        (fun omega => tubeMass r (brownianImage W hmu.compactAttractor omega)) P := by
    intro r hr hr1
    simpa using (hupper1 r hr hr1).2.1
  obtain ⟨c, hc, hlower⟩ :=
    hmu.exists_expected_tubeMass_lower_of_integrable S hsep hdim hs0 hs1 hW hint
  exact ⟨c, hc, fun r hr hr1 => ⟨hint r hr hr1, hlower r hr hr1⟩⟩

/-- Once the upper moments are available, the complete statement of
`thm:neighbourhood-moments` is obtained by pairing them with the preceding bridge. -/
theorem IsNatural.tubeMoments_of_upper
    [Nonempty iota] (S : System iota) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    (hmu : S.IsNatural K s mu) (hs0 : 0 < s) (hs1 : s < 1)
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (hupper : ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        Integrable
          (fun omega => (brownianTubeArea W hmu.compactAttractor r omega) ^ q) P ∧
        Integrable
          (fun omega =>
            (tubeMass r (brownianImage W hmu.compactAttractor omega)) ^ q) P ∧
        (∫ omega, (brownianTubeArea W hmu.compactAttractor r omega) ^ q ∂P) +
            (∫ omega,
              (tubeMass r (brownianImage W hmu.compactAttractor omega)) ^ q ∂P)
          ≤ Cq * r ^ (q * tubeExponent s)) :
    (∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        Integrable
          (fun omega => (brownianTubeArea W hmu.compactAttractor r omega) ^ q) P ∧
        Integrable
          (fun omega =>
            (tubeMass r (brownianImage W hmu.compactAttractor omega)) ^ q) P ∧
        (∫ omega, (brownianTubeArea W hmu.compactAttractor r omega) ^ q ∂P) +
            (∫ omega,
              (tubeMass r (brownianImage W hmu.compactAttractor omega)) ^ q ∂P)
          ≤ Cq * r ^ (q * tubeExponent s)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
        Integrable
          (fun omega => tubeMass r (brownianImage W hmu.compactAttractor omega)) P ∧
        c * r ^ tubeExponent s ≤
          ∫ omega, tubeMass r (brownianImage W hmu.compactAttractor omega) ∂P :=
  ⟨hupper,
    hmu.exists_expected_tubeMass_lower_of_tubeMomentUpper S hsep hdim hs0 hs1 hW hupper⟩

end System

end

end BrownianImages
