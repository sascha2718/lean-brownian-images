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
  apply measurable_pi_lambda
  intro t
  fun_prop

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

end BrownianImages
