import BrownianImages.Defs

namespace BrownianImages

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ### Brownian scaling on an affine time interval -/

/-- A real path, viewed from time `a` on the time scale `r` and the spatial scale
`sqrt r`.  The value at time `t` is
`(B (a + r * t) - B a) / sqrt r`. -/
noncomputable def intervalRescaleReal (B : NNReal -> Omega -> Real) (a r : NNReal) :
    NNReal -> Omega -> Real :=
  fun t omega => (Real.sqrt (r : Real))⁻¹ * (B (a + r * t) omega - B a omega)

/-- The planar version of `intervalRescaleReal`. -/
noncomputable def intervalRescale (W : NNReal -> Omega -> Plane) (a r : NNReal) :
    NNReal -> Omega -> Plane :=
  fun t omega => (Real.sqrt (r : Real))⁻¹ • (W (a + r * t) omega - W a omega)

/-- Brownian scaling after a deterministic shift preserves real pre-Brownian motion. -/
theorem IsPreBrownianReal.intervalRescale {B : NNReal -> Omega -> Real} {P : Measure Omega}
    (hB : IsPreBrownianReal B P) (a : NNReal) {r : NNReal} (hr : r ≠ 0) :
    IsPreBrownianReal (intervalRescaleReal B a r) P := by
  change IsPreBrownianReal
    (fun t omega => (Real.sqrt (r : Real))⁻¹ * (B (a + r * t) omega - B a omega)) P
  exact (hB.shift a).smul hr

/-- Brownian scaling after a deterministic shift preserves real Brownian motion, including
almost-sure path continuity. -/
theorem IsBrownianReal.intervalRescale {B : NNReal -> Omega -> Real} {P : Measure Omega}
    (hB : IsBrownianReal B P) (a : NNReal) {r : NNReal} (hr : r ≠ 0) :
    IsBrownianReal (intervalRescaleReal B a r) P := by
  change IsBrownianReal
    (fun t omega => (Real.sqrt (r : Real))⁻¹ * (B (a + r * t) omega - B a omega)) P
  exact (hB.shift a).smul hr

/-- Explicitly, every finite-dimensional distribution of the rescaled real path is the
standard Brownian projective law. -/
theorem IsPreBrownianReal.hasLaw_intervalRescale {B : NNReal -> Omega -> Real}
    {P : Measure Omega} (hB : IsPreBrownianReal B P) (a : NNReal) {r : NNReal}
    (hr : r ≠ 0) (I : Finset NNReal) :
    HasLaw (fun omega => I.restrict (intervalRescaleReal B a r · omega))
      (ProbabilityTheory.BrownianReal.projectiveFamily I) P :=
  (BrownianImages.IsPreBrownianReal.intervalRescale hB a hr).hasLaw I

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
  apply measurable_pi_lambda
  intro t
  fun_prop

/-- The pure Brownian scaling operation on real path space is measurable. -/
theorem measurable_scaleRealPath (r : NNReal) :
    Measurable (fun x : NNReal -> Real =>
      fun t => (Real.sqrt (r : Real))⁻¹ * x (r * t)) := by
  apply measurable_pi_lambda
  intro t
  fun_prop

/-- The entire rescaled future real path is independent of the path up to its left endpoint.
This is the weak Markov property transported through the measurable scaling map.  No positivity
assumption on `r` is needed for this independence statement. -/
theorem IsPreBrownianReal.indepFun_intervalRescale_past
    {B : NNReal -> Omega -> Real} {P : Measure Omega} (hB : IsPreBrownianReal B P)
    (a r : NNReal) :
    IndepFun (fun omega t => intervalRescaleReal B a r t omega)
      (fun omega (t : Set.Iic a) => B t omega) P := by
  have h := (hB.indepFun_shift a).comp (measurable_scaleRealPath r) measurable_id
  change IndepFun
    (fun omega => fun t => (Real.sqrt (r : Real))⁻¹ *
      (B (a + r * t) omega - B a omega))
    (fun omega (t : Set.Iic a) => B t omega) P at h
  exact h

/-- Restriction of a real path to finitely many times is measurable for product measurable
spaces. -/
theorem measurable_restrictRealPath (I : Finset NNReal) :
    Measurable (fun x : NNReal -> Real => I.restrict x) := by
  apply measurable_pi_lambda
  intro t
  fun_prop

/-- Assemble two coordinate vectors into a finite planar path. -/
def packFinitePlanarPath (I : Finset NNReal) (x : Fin 2 -> I -> Real) : I -> Plane :=
  fun t => WithLp.toLp 2 (fun i => x i t)

/-- `packFinitePlanarPath` is measurable for the finite product Borel structures. -/
theorem measurable_packFinitePlanarPath (I : Finset NNReal) :
    Measurable (packFinitePlanarPath I) := by
  apply measurable_pi_lambda
  intro t
  change Measurable (fun x : Fin 2 -> I -> Real =>
    WithLp.toLp 2 (fun i => x i t))
  exact (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin 2 => Real)).symm.continuous.measurable.comp
    (measurable_pi_lambda _ (fun i => by fun_prop))

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

/-- The finite-dimensional law of the affine rescaling is exactly the standard planar
Brownian law, independently of the left endpoint and the positive time scale. -/
theorem IsPlanarBrownian.hasLaw_intervalRescale {W : NNReal -> Omega -> Plane}
    {P : Measure Omega} (hW : IsPlanarBrownian W P) (a : NNReal) {r : NNReal}
    (hr : r ≠ 0) (I : Finset NNReal) :
    HasLaw (fun omega => I.restrict (fun t => BrownianImages.intervalRescale W a r t omega))
      (planarBrownianProjectiveFamily I) P :=
  (hW.intervalRescale a hr).hasLaw_restrict I

/-- Equality of the finite-dimensional distributions of the affine rescaling and the original
planar Brownian motion.  This is the law identity used by self-similar tube recursions. -/
theorem IsPlanarBrownian.map_restrict_intervalRescale_eq
    {W : NNReal -> Omega -> Plane} {P : Measure Omega} (hW : IsPlanarBrownian W P)
    (a : NNReal) {r : NNReal} (hr : r ≠ 0) (I : Finset NNReal) :
    P.map (fun omega => I.restrict (fun t => BrownianImages.intervalRescale W a r t omega)) =
      P.map (fun omega => I.restrict (fun t => W t omega)) := by
  rw [(hW.hasLaw_intervalRescale a hr I).map_eq, (hW.hasLaw_restrict I).map_eq]

end BrownianImages
