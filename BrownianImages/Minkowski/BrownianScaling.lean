import BrownianImages.Defs

namespace BrownianImages

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ### Brownian scaling on an affine time interval -/

/-- The planar version of `intervalRescaleReal`. -/
noncomputable def intervalRescale (W : NNReal -> Omega -> Plane) (a r : NNReal) :
    NNReal -> Omega -> Plane :=
  fun t omega => (Real.sqrt (r : Real))⁻¹ • (W (a + r * t) omega - W a omega)

/-- The coordinate processes of the affine rescaling of a planar Brownian motion are real
Brownian motions. -/
theorem IsPlanarBrownian.coord_intervalRescale {W : NNReal -> Omega -> Plane}
    {P : Measure Omega} (hW : IsPlanarBrownian W P) (a : NNReal) {r : NNReal}
    (hr : r ≠ 0) (i : Fin 2) :
    IsBrownianReal (fun t omega => intervalRescale W a r t omega i) P := by
  change IsBrownianReal
    (fun t omega => (Real.sqrt (r : Real))⁻¹ *
      (W (a + r * t) omega i - W a omega i)) P
  exact (hW.coord i).shift a |>.smul hr

/-- Resampling and normalising a real path is measurable for the product measurable
structure on path space. -/
theorem measurable_intervalRescalePathReal (a r : NNReal) :
    Measurable (fun x : NNReal -> Real =>
      fun t => (Real.sqrt (r : Real))⁻¹ * (x (a + r * t) - x a)) := by
  apply Measurable.of_eval
  intro t
  fun_prop

/-- Restriction of a real path to finitely many times is measurable for product measurable
spaces. -/
theorem measurable_restrictRealPath (I : Finset NNReal) :
    Measurable (fun x : NNReal -> Real => I.restrict x) := by
  apply Measurable.of_eval
  intro t
  fun_prop

/-- Assemble two coordinate vectors into a finite planar path. -/
def packFinitePlanarPath (I : Finset NNReal) (x : Fin 2 -> I -> Real) : I -> Plane :=
  fun t => WithLp.toLp 2 (fun i => x i t)

/-- `packFinitePlanarPath` is measurable for the finite product Borel structures. -/
theorem measurable_packFinitePlanarPath (I : Finset NNReal) :
    Measurable (packFinitePlanarPath I) := by
  apply Measurable.of_eval
  intro t
  change Measurable (fun x : Fin 2 -> I -> Real =>
    WithLp.toLp 2 (fun i => x i t))
  exact (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin 2 => Real)).symm.continuous.measurable.comp
    (Measurable.of_eval (fun i => by fun_prop))

/-- The canonical finite-dimensional law of planar Brownian motion, obtained by taking the
product of the two real Brownian projective laws and reassembling their coordinates. -/
noncomputable def planarBrownianProjectiveFamily (I : Finset NNReal) : Measure (I -> Plane) :=
  (Measure.pi (fun _ : Fin 2 => ProbabilityTheory.BrownianReal.projectiveFamily I)).map
    (packFinitePlanarPath I)

/-- Every finite restriction of a planar Brownian motion has the canonical planar Brownian
projective law. -/
theorem IsPlanarBrownian.hasLaw_restrict {W : NNReal -> Omega -> Plane}
    {P : Measure Omega} (hW : IsPlanarBrownian W P) (I : Finset NNReal) :
    HasLaw (fun omega => I.restrict (W · omega)) (planarBrownianProjectiveFamily I) P := by
  let X : Fin 2 -> Omega -> (I -> Real) :=
    fun i omega => I.restrict (fun t => W t omega i)
  have hX_law : forall i, HasLaw (X i)
      (ProbabilityTheory.BrownianReal.projectiveFamily I) P := by
    intro i
    simpa only [X] using (hW.coord i).toIsPreBrownianReal.hasLaw I
  have hX_indep : iIndepFun X P := by
    have h := hW.indep.comp (fun _ x => I.restrict x)
      (fun _ => measurable_restrictRealPath I)
    change iIndepFun X P at h
    exact h
  have hX : HasLaw (fun omega i => X i omega)
      (Measure.pi (fun _ : Fin 2 => ProbabilityTheory.BrownianReal.projectiveFamily I)) P :=
    hX_indep.hasLaw_pi hX_law
  have hpack : HasLaw (packFinitePlanarPath I) (planarBrownianProjectiveFamily I)
      (Measure.pi (fun _ : Fin 2 => ProbabilityTheory.BrownianReal.projectiveFamily I)) := {
    aemeasurable := (measurable_packFinitePlanarPath I).aemeasurable
    map_eq := rfl }
  have h := hpack.comp hX
  refine h.congr (Filter.Eventually.of_forall fun omega => ?_)
  funext t
  apply PiLp.ext
  intro i
  rfl

/-- Affine time rescaling and Brownian spatial normalisation preserve planar Brownian motion.
In particular, this packages both the finite-dimensional Brownian laws of the two coordinates
and their independence as whole coordinate paths. -/
theorem IsPlanarBrownian.intervalRescale {W : NNReal -> Omega -> Plane}
    {P : Measure Omega} (hW : IsPlanarBrownian W P) (a : NNReal) {r : NNReal}
    (hr : r ≠ 0) : IsPlanarBrownian (intervalRescale W a r) P where
  coord := hW.coord_intervalRescale a hr
  indep := by
    have h := hW.indep.comp
      (fun _ x t => (Real.sqrt (r : Real))⁻¹ * (x (a + r * t) - x a))
      (fun _ => measurable_intervalRescalePathReal a r)
    change iIndepFun (fun i omega => fun t => (Real.sqrt (r : Real))⁻¹ *
      (W (a + r * t) omega i - W a omega i)) P
    change iIndepFun (fun i omega => fun t => (Real.sqrt (r : Real))⁻¹ *
      (W (a + r * t) omega i - W a omega i)) P at h
    exact h

/-! ### Time reversal -/

section TimeReversal

/-- The reversed time `(b - t)⁺`. -/
noncomputable def revTime (b t : NNReal) : NNReal := ((b : Real) - t).toNNReal

/-- Time reversal is continuous. -/
theorem continuous_revTime (b : NNReal) : Continuous (revTime b) :=
  continuous_real_toNNReal.comp (continuous_const.sub NNReal.continuous_coe)

/-- Before time `b` the reversed time is `b - t`. -/
theorem coe_revTime_of_le {b t : NNReal} (h : t ≤ b) : (revTime b t : Real) = b - t :=
  Real.coe_toNNReal _ (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))

/-- After time `b` the reversed time is `0`. -/
theorem revTime_of_le {b t : NNReal} (h : b ≤ t) : revTime b t = 0 :=
  Real.toNNReal_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr h))

/-- The time reversal of a real process at time `b`: `t ↦ B(b - t) - B(b)` up to time
`b`, continued past `b` by the increments after `b`, `t ↦ B(0) - B(b) + (B(t) - B(b))`.
The one formula covers both ranges, since `(b - t)⁺ = 0` and `min t b = b` past `b`. -/
noncomputable def reverseReal (B : NNReal -> Omega -> Real) (b : NNReal) :
    NNReal -> Omega -> Real :=
  fun t omega => (B (revTime b t) omega - B b omega) + (B t omega - B (min t b) omega)

omit [MeasurableSpace Omega] in
/-- Before time `b`, the reversal is `B(b - t) - B(b)`. -/
theorem reverseReal_of_le {B : NNReal -> Omega -> Real} {b t : NNReal} (h : t ≤ b)
    (omega : Omega) : reverseReal B b t omega = B (revTime b t) omega - B b omega := by
  simp [reverseReal, min_eq_left h]

omit [MeasurableSpace Omega] in
/-- After time `b`, the reversal is `B(0) - B(b) + (B(t) - B(b))`. -/
theorem reverseReal_of_ge {B : NNReal -> Omega -> Real} {b t : NNReal} (h : b ≤ t)
    (omega : Omega) :
    reverseReal B b t omega = (B 0 omega - B b omega) + (B t omega - B b omega) := by
  simp [reverseReal, min_eq_right h, revTime_of_le h]

/-- **Time reversal of a pre-Brownian motion is pre-Brownian.**  The reversed process
is a Gaussian process, each value being a linear combination of four values of `B`, it
is centred, and its covariance is `min s t`: before `b` this is the covariance of
`B(b - s) - B(b)` and `B(b - t) - B(b)`, after `b` the increments past `b` are
uncorrelated with the reversed initial segment. -/
theorem _root_.ProbabilityTheory.IsPreBrownianReal.reverse {B : NNReal -> Omega -> Real}
    {P : Measure Omega} (hB : IsPreBrownianReal B P) (b : NNReal) :
    IsPreBrownianReal (reverseReal B b) P := by
  have hP := hB.isGaussianProcess.isProbabilityMeasure
  have h2 : ∀ r, MemLp (B r) 2 P := fun r =>
    (hB.isGaussianProcess.hasGaussianLaw_eval r).memLp_two
  have hsub : ∀ r r', MemLp (fun omega => B r omega - B r' omega) 2 P := fun r r' =>
    (h2 r).sub (h2 r')
  have hcov : ∀ r r', cov[B r, B r'; P] = min (r : Real) r' := fun r r' => by
    rw [hB.covariance_eval, NNReal.coe_min]
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_)
    (fun s t hst => ?_)
  · apply hB.isGaussianProcess.of_isGaussianProcess
    intro t
    classical
    let J : Finset NNReal := {revTime b t, b, t, min t b}
    let L : (J -> Real) →ₗ[Real] Real :=
      { toFun := fun x => (x ⟨revTime b t, by simp [J]⟩ - x ⟨b, by simp [J]⟩) +
          (x ⟨t, by simp [J]⟩ - x ⟨min t b, by simp [J]⟩)
        map_add' := by intro x y; simp; ring
        map_smul' := by intro c x; simp; ring }
    exact ⟨J, L.toContinuousLinearMap, fun omega => rfl⟩
  · have hint : ∀ r, Integrable (B r) P := fun r => hB.integrable_eval r
    have hsubint : ∀ r r', Integrable (fun omega => B r omega - B r' omega) P :=
      fun r r' => (hint r).sub (hint r')
    simp only [BrownianImages.reverseReal]
    rw [integral_add (hsubint (revTime b t) b) (hsubint t (min t b)),
      integral_sub (hint _) (hint _), integral_sub (hint _) (hint _)]
    simp [hB.integral_eval]
  · have hst' : (s : Real) ≤ t := NNReal.coe_le_coe.mpr hst
    have hb0 : (0 : Real) ≤ b := b.2
    have hs0 : (0 : Real) ≤ s := s.2
    have ht0 : (0 : Real) ≤ t := t.2
    rcases le_or_gt t b with htb | hbt
    · -- `s ≤ t ≤ b`
      have hsb : s ≤ b := hst.trans htb
      have htb' : (t : Real) ≤ b := NNReal.coe_le_coe.mpr htb
      have hXs : reverseReal B b s = fun omega => B (revTime b s) omega - B b omega :=
        funext (reverseReal_of_le hsb)
      have hXt : reverseReal B b t = fun omega => B (revTime b t) omega - B b omega :=
        funext (reverseReal_of_le htb)
      rw [hXs, hXt, covariance_fun_sub_fun_sub (h2 _) (h2 _) (h2 _) (h2 _)]
      simp only [hcov, coe_revTime_of_le hsb, coe_revTime_of_le htb]
      have e1 : min ((b : Real) - s) (b - t) = b - t := min_eq_right (by linarith)
      have e2 : min ((b : Real) - s) b = b - s := min_eq_left (by linarith)
      have e3 : min (b : Real) (b - t) = b - t := min_eq_right (by linarith)
      simp only [e1, e2, e3, min_self]
      ring
    · rcases le_or_gt s b with hsb | hbs
      · -- `s ≤ b < t`
        have hbt' : (b : Real) ≤ t := NNReal.coe_le_coe.mpr hbt.le
        have hsb' : (s : Real) ≤ b := NNReal.coe_le_coe.mpr hsb
        have hXs : reverseReal B b s = fun omega => B (revTime b s) omega - B b omega :=
          funext (reverseReal_of_le hsb)
        have hXt : reverseReal B b t =
            (fun omega => B 0 omega - B b omega) + (fun omega => B t omega - B b omega) :=
          funext (reverseReal_of_ge hbt.le)
        rw [hXs, hXt, covariance_add_right (hsub _ _) (hsub _ _) (hsub _ _),
          covariance_fun_sub_fun_sub (h2 _) (h2 _) (h2 _) (h2 _),
          covariance_fun_sub_fun_sub (h2 _) (h2 _) (h2 _) (h2 _)]
        simp only [hcov, coe_revTime_of_le hsb, NNReal.coe_zero]
        have e1 : min ((b : Real) - s) 0 = 0 := min_eq_right (by linarith)
        have e2 : min ((b : Real) - s) b = b - s := min_eq_left (by linarith)
        have e3 : min (b : Real) 0 = 0 := min_eq_right hb0
        have e4 : min ((b : Real) - s) t = b - s := min_eq_left (by linarith)
        have e5 : min (b : Real) t = b := min_eq_left hbt'
        simp only [e1, e2, e3, e4, e5, min_self]
        ring
      · -- `b < s ≤ t`
        have hbs' : (b : Real) ≤ s := NNReal.coe_le_coe.mpr hbs.le
        have hbt' : (b : Real) ≤ t := NNReal.coe_le_coe.mpr hbt.le
        have hXs : reverseReal B b s =
            (fun omega => B 0 omega - B b omega) + (fun omega => B s omega - B b omega) :=
          funext (reverseReal_of_ge hbs.le)
        have hXt : reverseReal B b t =
            (fun omega => B 0 omega - B b omega) + (fun omega => B t omega - B b omega) :=
          funext (reverseReal_of_ge hbt.le)
        rw [hXs, hXt, covariance_add_left (hsub _ _) (hsub _ _) ((hsub _ _).add (hsub _ _)),
          covariance_add_right (hsub _ _) (hsub _ _) (hsub _ _),
          covariance_add_right (hsub _ _) (hsub _ _) (hsub _ _),
          covariance_fun_sub_fun_sub (h2 _) (h2 _) (h2 _) (h2 _),
          covariance_fun_sub_fun_sub (h2 _) (h2 _) (h2 _) (h2 _),
          covariance_fun_sub_fun_sub (h2 _) (h2 _) (h2 _) (h2 _),
          covariance_fun_sub_fun_sub (h2 _) (h2 _) (h2 _) (h2 _)]
        simp only [hcov, NNReal.coe_zero]
        have e1 : min (0 : Real) b = 0 := min_eq_left hb0
        have e2 : min (b : Real) 0 = 0 := min_eq_right hb0
        have e3 : min (0 : Real) t = 0 := min_eq_left ht0
        have e4 : min (b : Real) t = b := min_eq_left hbt'
        have e5 : min (s : Real) 0 = 0 := min_eq_right hs0
        have e6 : min (s : Real) b = b := min_eq_right hbs'
        have e7 : min (s : Real) t = s := min_eq_left hst'
        simp only [e1, e2, e3, e4, e5, e6, e7, min_self]
        ring

/-- Time reversal of a Brownian motion is a Brownian motion: the paths stay continuous,
the two branches agreeing at time `b`. -/
theorem _root_.ProbabilityTheory.IsBrownianReal.reverse {B : NNReal -> Omega -> Real}
    {P : Measure Omega} (hB : IsBrownianReal B P) (b : NNReal) :
    IsBrownianReal (reverseReal B b) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.reverse b
  cont := by
    filter_upwards [hB.cont] with omega homega
    have h1 : Continuous (fun t => B (revTime b t) omega) :=
      homega.comp (continuous_revTime b)
    have h2 : Continuous (fun t : NNReal => B (min t b) omega) :=
      homega.comp (continuous_id.min continuous_const)
    exact ((h1.sub continuous_const).add (homega.sub h2))

/-- The time reversal of a planar process at time `b`, coordinatewise. -/
noncomputable def timeReversal (W : NNReal -> Omega -> Plane) (b : NNReal) :
    NNReal -> Omega -> Plane :=
  fun t omega => (W (revTime b t) omega - W b omega) + (W t omega - W (min t b) omega)

/-- Reversing a real path is measurable for the product measurable structure on path
space. -/
theorem measurable_reversePathReal (b : NNReal) :
    Measurable (fun x : NNReal -> Real =>
      fun t => (x (revTime b t) - x b) + (x t - x (min t b))) := by
  apply Measurable.of_eval
  intro t
  fun_prop

/-- **Time reversal preserves planar Brownian motion.**  Each coordinate is reversed, and
the reversed coordinate paths are measurable functions of the original ones, so their
independence is inherited. -/
theorem IsPlanarBrownian.timeReversal {W : NNReal -> Omega -> Plane}
    {P : Measure Omega} (hW : IsPlanarBrownian W P) (b : NNReal) :
    IsPlanarBrownian (timeReversal W b) P where
  coord i := by
    have h := (hW.coord i).reverse b
    change IsBrownianReal (fun t omega =>
      (W (revTime b t) omega i - W b omega i) + (W t omega i - W (min t b) omega i)) P at h
    exact h
  indep := by
    have h := hW.indep.comp
      (fun _ x => fun t => (x (revTime b t) - x b) + (x t - x (min t b)))
      (fun _ => measurable_reversePathReal b)
    change iIndepFun (fun i omega => fun t =>
      (W (revTime b t) omega i - W b omega i) + (W t omega i - W (min t b) omega i)) P at h
    change iIndepFun (fun i omega => fun t =>
      (W (revTime b t) omega i - W b omega i) + (W t omega i - W (min t b) omega i)) P
    exact h

omit [MeasurableSpace Omega] in
/-- On a continuous path the reversed path is continuous. -/
theorem continuous_timeReversal {W : NNReal -> Omega -> Plane} (b : NNReal) {omega : Omega}
    (homega : Continuous (fun t => W t omega)) :
    Continuous (fun t => timeReversal W b t omega) := by
  have h1 : Continuous (fun t => W (revTime b t) omega) := homega.comp (continuous_revTime b)
  have h2 : Continuous (fun t : NNReal => W (min t b) omega) :=
    homega.comp (continuous_id.min continuous_const)
  exact ((h1.sub continuous_const).add (homega.sub h2))

end TimeReversal

end BrownianImages
