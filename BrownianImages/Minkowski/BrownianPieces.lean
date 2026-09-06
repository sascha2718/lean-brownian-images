import BrownianImages.CompactImage
import BrownianImages.Minkowski.BrownianScaling
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

/-! ### Passing laws and independence to almost-sure limits -/

/-- Equality in law passes to almost-sure limits in a space where weak limits of probability
measures are unique.  The approximating variables may live on different probability spaces. -/
theorem map_eq_of_ae_tendsto_of_map_eq
    {Omega Omega' E : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E]
    {P : Measure Omega} {Q : Measure Omega'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {X : Nat -> Omega -> E} {Y : Nat -> Omega' -> E}
    {x : Omega -> E} {y : Omega' -> E}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) Q)
    (hx : AEMeasurable x P) (hy : AEMeasurable y Q)
    (hXlim : ∀ᵐ omega ∂P, Tendsto (fun n => X n omega) atTop (nhds (x omega)))
    (hYlim : ∀ᵐ omega ∂Q, Tendsto (fun n => Y n omega) atTop (nhds (y omega)))
    (hlaw : ∀ n, P.map (X n) = Q.map (Y n)) :
    P.map x = Q.map y := by
  have hdistX := tendstoInDistribution_of_ae_tendsto hX hx hXlim
  have hdistY := tendstoInDistribution_of_ae_tendsto hY hy hYlim
  have hdistY' : TendstoInDistribution X atTop y (fun _ => P) Q := {
    forall_aemeasurable := hX
    aemeasurable_limit := hy
    tendsto := by
      have heq :
          (fun n => (⟨P.map (X n), Measure.isProbabilityMeasure_map (hX n)⟩ :
            ProbabilityMeasure E)) =
          (fun n => (⟨Q.map (Y n), Measure.isProbabilityMeasure_map (hY n)⟩ :
            ProbabilityMeasure E)) := by
        funext n
        exact Subtype.ext (hlaw n)
      rw [heq]
      exact hdistY.tendsto }
  exact tendstoInDistribution_unique X hdistX hdistY'

/-- Mutual independence of a finite family is closed under coordinatewise almost-sure
convergence.  The comparison family lives on the finite product of copies of the original
probability space. -/
theorem iIndepFun_of_ae_tendsto
    {Omega I E : Type*} [MeasurableSpace Omega] [Fintype I]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : Nat -> I -> Omega -> E} {x : I -> Omega -> E}
    (hX : ∀ n i, AEMeasurable (X n i) P)
    (hx : ∀ i, AEMeasurable (x i) P)
    (hlim : ∀ i, ∀ᵐ omega ∂P, Tendsto (fun n => X n i omega) atTop (nhds (x i omega)))
    (hindep : ∀ n, iIndepFun (X n) P) :
    iIndepFun x P := by
  let Q : Measure (I -> Omega) := Measure.pi (fun _ : I => P)
  let Xvec : Nat -> Omega -> (I -> E) := fun n omega i => X n i omega
  let Xprod : Nat -> (I -> Omega) -> (I -> E) := fun n omega i => X n i (omega i)
  let xvec : Omega -> (I -> E) := fun omega i => x i omega
  let xprod : (I -> Omega) -> (I -> E) := fun omega i => x i (omega i)
  have hXvec : ∀ n, AEMeasurable (Xvec n) P := fun n =>
    aemeasurable_pi_lambda _ (hX n)
  have hXprod : ∀ n, AEMeasurable (Xprod n) Q := fun n => by
    apply aemeasurable_pi_lambda
    intro i
    exact (hX n i).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : I => P) i)
  have hxvec : AEMeasurable xvec P := aemeasurable_pi_lambda _ hx
  have hxprod : AEMeasurable xprod Q := by
    apply aemeasurable_pi_lambda
    intro i
    exact (hx i).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : I => P) i)
  have hXveclim : ∀ᵐ omega ∂P,
      Tendsto (fun n => Xvec n omega) atTop (nhds (xvec omega)) := by
    filter_upwards [ae_all_iff.mpr hlim] with omega homega
    exact tendsto_pi_nhds.mpr homega
  have hcoordlim_prod : ∀ i, ∀ᵐ omega ∂Q,
      Tendsto (fun n => X n i (omega i)) atTop (nhds (x i (omega i))) := by
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ : I => P) i).tendsto_ae (hlim i)
  have hXprodlim : ∀ᵐ omega ∂Q,
      Tendsto (fun n => Xprod n omega) atTop (nhds (xprod omega)) := by
    filter_upwards [ae_all_iff.mpr hcoordlim_prod] with omega homega
    exact tendsto_pi_nhds.mpr homega
  have hmaps : ∀ n, P.map (Xvec n) = Q.map (Xprod n) := by
    intro n
    rw [(hindep n).map_fun_eq_pi_map (hX n)]
    exact (Measure.pi_map_pi (hX n)).symm
  have hlimitMap : P.map xvec = Q.map xprod :=
    map_eq_of_ae_tendsto_of_map_eq hXvec hXprod hxvec hxprod hXveclim hXprodlim hmaps
  apply (iIndepFun_iff_map_fun_eq_pi_map hx).2
  rw [show (fun omega i => x i omega) = xvec from rfl, hlimitMap]
  exact Measure.pi_map_pi hx

/-- Assemble coordinatewise independence into independence of two finite vectors.  Unlike the
earlier project-specific real-valued lemma, this version allows arbitrary coordinate codomains. -/
theorem indepFun_pi_of_pair_general
    {Omega I E F : Type*} [MeasurableSpace Omega] [Fintype I]
    [MeasurableSpace E] [MeasurableSpace F] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : I -> Omega -> E} {Y : I -> Omega -> F}
    (hX : ∀ i, AEMeasurable (X i) P) (hY : ∀ i, AEMeasurable (Y i) P)
    (hpair : iIndepFun (fun i omega => (X i omega, Y i omega)) P)
    (hcoord : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun omega i => X i omega) (fun omega i => Y i omega) P := by
  let mu : I -> Measure E := fun i => P.map (X i)
  let nu : I -> Measure F := fun i => P.map (Y i)
  letI (i : I) : IsProbabilityMeasure (mu i) := Measure.isProbabilityMeasure_map (hX i)
  letI (i : I) : IsProbabilityMeasure (nu i) := Measure.isProbabilityMeasure_map (hY i)
  have hXi : ∀ i, HasLaw (X i) (mu i) P := fun i => ⟨hX i, rfl⟩
  have hYi : ∀ i, HasLaw (Y i) (nu i) P := fun i => ⟨hY i, rfl⟩
  have hpairLaw : ∀ i, HasLaw (fun omega => (X i omega, Y i omega))
      ((mu i).prod (nu i)) P := fun i =>
    (indepFun_iff_hasLaw_prodMk_prod (hXi i) (hYi i)).1 (hcoord i)
  have hfamiliesLaw := hpair.hasLaw_pi hpairLaw
  have hallLaw :=
    (measurePreserving_arrowProdEquivProdArrow E F I mu nu).fun_comp_hasLaw hfamiliesLaw
  have hXind : iIndepFun X P :=
    hpair.comp (fun _ p => p.1) (fun _ => measurable_fst)
  have hYind : iIndepFun Y P :=
    hpair.comp (fun _ p => p.2) (fun _ => measurable_snd)
  have hXlaw := hXind.hasLaw_pi hXi
  have hYlaw := hYind.hasLaw_pi hYi
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (aemeasurable_pi_lambda _ hX) (aemeasurable_pi_lambda _ hY)).2
  have hmap := hallLaw.map_eq
  change P.map (fun omega => ((fun i => X i omega), fun i => Y i omega)) =
    (Measure.pi mu).prod (Measure.pi nu) at hmap
  rw [hmap, hXlaw.map_eq, hYlaw.map_eq]

/-! ### Finite Brownian images -/

/-- Two planar Brownian motions have the same law when sampled along any fixed finite family
of times.  Repeated times in the family are allowed. -/
theorem map_finite_planar_eval_eq
    {Omega Omega' A : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega'] [Fintype A]
    {P : Measure Omega} {Q : Measure Omega'} {W : NNReal -> Omega -> Plane}
    {V : NNReal -> Omega' -> Plane} (hW : IsPlanarBrownian W P)
    (hV : IsPlanarBrownian V Q) (tau : A -> NNReal) :
    P.map (fun omega i => W (tau i) omega) = Q.map (fun omega i => V (tau i) omega) := by
  let I : Finset NNReal := Finset.univ.image tau
  let pull : (I -> Plane) -> (A -> Plane) :=
    fun z i => z ⟨tau i, by simp [I]⟩
  have hpull : Measurable pull := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (⟨tau i, by simp [I]⟩ : I)
  let nu : Measure (A -> Plane) := (planarBrownianProjectiveFamily I).map pull
  have hpullLaw : HasLaw pull nu (planarBrownianProjectiveFamily I) := {
    aemeasurable := hpull.aemeasurable
    map_eq := rfl }
  have hWlaw := hpullLaw.comp (hW.hasLaw_restrict I)
  have hVlaw := hpullLaw.comp (hV.hasLaw_restrict I)
  have hWmap : P.map (fun omega i => W (tau i) omega) = nu := by
    have hfun : (fun omega i => W (tau i) omega) =
        pull ∘ (fun omega => I.restrict (fun t => W t omega)) := by
      funext omega i
      rfl
    rw [hfun, hWlaw.map_eq]
  have hVmap : Q.map (fun omega i => V (tau i) omega) = nu := by
    have hfun : (fun omega i => V (tau i) omega) =
        pull ∘ (fun omega => I.restrict (fun t => V t omega)) := by
      funext omega i
      rfl
    rw [hfun, hVlaw.map_eq]
  exact hWmap.trans hVmap.symm

/-- Consequently the compact ranges of the two finite samples have the same law. -/
theorem map_finiteRange_planar_eval_eq
    {Omega Omega' A : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [Fintype A] [Nonempty A] {P : Measure Omega} {Q : Measure Omega'}
    {W : NNReal -> Omega -> Plane} {V : NNReal -> Omega' -> Plane}
    (hW : IsPlanarBrownian W P) (hV : IsPlanarBrownian V Q) (tau : A -> NNReal) :
    P.map (fun omega => finiteRange (fun i => W (tau i) omega)) =
      Q.map (fun omega => finiteRange (fun i => V (tau i) omega)) := by
  have hWt : AEMeasurable (fun omega i => W (tau i) omega) P :=
    aemeasurable_pi_lambda _ fun i => JointMeasurability.aemeasurable_eval hW (tau i)
  have hVt : AEMeasurable (fun omega i => V (tau i) omega) Q :=
    aemeasurable_pi_lambda _ fun i => JointMeasurability.aemeasurable_eval hV (tau i)
  change P.map (finiteRange ∘ (fun omega i => W (tau i) omega)) =
    Q.map (finiteRange ∘ (fun omega i => V (tau i) omega))
  rw [← AEMeasurable.map_map_of_aemeasurable
    (measurable_finiteRange (I := A) (E := Plane)).aemeasurable hWt]
  rw [← AEMeasurable.map_map_of_aemeasurable
    (measurable_finiteRange (I := A) (E := Plane)).aemeasurable hVt]
  rw [map_finite_planar_eval_eq hW hV tau]

/-- A planar Brownian motion is a Gaussian process.  This packages the independent Gaussian
coordinate processes into the Euclidean plane. -/
theorem IsPlanarBrownian.isGaussianProcess
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P) :
    IsGaussianProcess W P := by
  refine ⟨fun I => ?_⟩
  let X : Fin 2 -> Omega -> (I -> Real) := fun i omega t => W t omega i
  have hXlaw : ∀ i, HasGaussianLaw (X i) P := by
    intro i
    exact (hW.coord i).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw I
  have hXind : iIndepFun X P := by
    have h := hW.indep.comp (fun _ x => I.restrict x)
      (fun _ => measurable_restrictRealPath I)
    change iIndepFun X P at h
    exact h
  have harray : HasGaussianLaw (fun omega i => X i omega) P :=
    hXind.hasGaussianLaw hXlaw
  let L : (Fin 2 -> I -> Real) →ₗ[Real] (I -> Plane) :=
    { toFun := fun x t => WithLp.toLp 2 (fun i => x i t)
      map_add' := by intro x y; ext t i; rfl
      map_smul' := by intro c x; ext t i; rfl }
  have hmap := harray.map L.toContinuousLinearMap
  have heq : (fun omega => I.restrict fun t => W t omega) =
      L.toContinuousLinearMap ∘ (fun omega i => X i omega) := by
    funext omega
    ext t i
    rfl
  rw [heq]
  exact hmap

/-! ### Independence of finite path pieces -/

/-- Reassemble coordinate arrays into planar samples. -/
def packPlanarSamples (A : Type*) (x : Fin 2 -> A -> Real) : A -> Plane :=
  fun t => WithLp.toLp 2 (fun i => x i t)

/-- Reassembling coordinate arrays is measurable for product measurable structures. -/
theorem measurable_packPlanarSamples (A : Type*) : Measurable (packPlanarSamples A) := by
  apply measurable_pi_lambda
  intro t
  change Measurable (fun x : Fin 2 -> A -> Real => WithLp.toLp 2 (fun i => x i t))
  exact (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin 2 => Real)).symm.continuous.measurable.comp
    (measurable_pi_lambda _ fun i => by fun_prop)

/-- Finite centered planar path pieces before and after a cut time are independent.  The first
family is sampled at `a + tau t`, all assumed at or before `c`; the second is sampled at
`c + upsilon u`. -/
theorem IsPlanarBrownian.indepFun_centered_finite_pieces
    {Omega A B : Type*} [MeasurableSpace Omega] [Fintype A] [Fintype B]
    {P : Measure Omega} [IsProbabilityMeasure P] {W : NNReal -> Omega -> Plane}
    (hW : IsPlanarBrownian W P) (a c : NNReal) (tau : A -> NNReal)
    (upsilon : B -> NNReal) (hac : a ≤ c) (htau : ∀ t, a + tau t ≤ c) :
    IndepFun
      (fun omega t => W (a + tau t) omega - W a omega)
      (fun omega u => W (c + upsilon u) omega - W c omega) P := by
  let X : Fin 2 -> Omega -> (A -> Real) := fun i omega t =>
    W (a + tau t) omega i - W a omega i
  let Y : Fin 2 -> Omega -> (B -> Real) := fun i omega u =>
    W (c + upsilon u) omega i - W c omega i
  have hX : ∀ i, AEMeasurable (X i) P := by
    intro i
    apply aemeasurable_pi_lambda
    intro t
    exact ((hW.coord i).toIsPreBrownianReal.aemeasurable (a + tau t)).sub
      ((hW.coord i).toIsPreBrownianReal.aemeasurable a)
  have hY : ∀ i, AEMeasurable (Y i) P := by
    intro i
    apply aemeasurable_pi_lambda
    intro u
    exact ((hW.coord i).toIsPreBrownianReal.aemeasurable (c + upsilon u)).sub
      ((hW.coord i).toIsPreBrownianReal.aemeasurable c)
  have mearly : Measurable (fun path : Set.Iic c -> Real =>
      fun t : A => path ⟨a + tau t, htau t⟩ - path ⟨a, hac⟩) := by
    apply measurable_pi_lambda
    intro t
    fun_prop
  have mlate : Measurable (fun path : NNReal -> Real =>
      fun u : B => path (upsilon u)) := by
    apply measurable_pi_lambda
    intro u
    fun_prop
  have hcoord : ∀ i, IndepFun (X i) (Y i) P := by
    intro i
    have h := ((hW.coord i).toIsPreBrownianReal.indepFun_shift c).comp mlate mearly
    change IndepFun (Y i) (X i) P at h
    exact h.symm
  have mpair : Measurable (fun path : NNReal -> Real =>
      ((fun t : A => path (a + tau t) - path a),
        fun u : B => path (c + upsilon u) - path c)) := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro t
      fun_prop
    · apply measurable_pi_lambda
      intro u
      fun_prop
  have hpair := hW.indep.comp
    (fun _ path => ((fun t : A => path (a + tau t) - path a),
      fun u : B => path (c + upsilon u) - path c))
    (fun _ => mpair)
  change iIndepFun (fun i omega => (X i omega, Y i omega)) P at hpair
  have hcoords := indepFun_pi_of_pair_general hX hY hpair hcoord
  have hpacked := hcoords.comp (measurable_packPlanarSamples A) (measurable_packPlanarSamples B)
  change IndepFun
    (packPlanarSamples A ∘ fun omega i => X i omega)
    (packPlanarSamples B ∘ fun omega i => Y i omega) P at hpacked
  convert hpacked using 1 <;> funext omega t <;> apply PiLp.ext <;> intro i <;> rfl

/-- Centered Brownian path samples belonging to a finite family of pairwise disjoint host
intervals are mutually independent.  Each compact parameter set is required to lie in
`[0,1]`, so its affine image lies inside the corresponding host interval. -/
theorem IsPlanarBrownian.iIndepFun_centered_compact_piece_processes
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P)
    (a r : I -> NNReal) (K : I -> NonemptyCompacts Real)
    (hK : ∀ i, (K i : Set Real) ⊆ Set.Icc 0 1)
    (hdisjoint : ∀ ⦃i j : I⦄, i ≠ j ->
      a i + r i ≤ a j ∨ a j + r j ≤ a i) :
    iIndepFun (fun i omega (t : K i) =>
      W (a i + r i * t.1.toNNReal) omega - W (a i) omega) P := by
  let Y : ((i : I) × K i) -> Omega -> Plane := fun p omega =>
    W (a p.1 + r p.1 * p.2.1.toNNReal) omega - W (a p.1) omega
  have hGaussian : IsGaussianProcess Y P := by
    apply hW.isGaussianProcess.of_isGaussianProcess
    intro p
    let J : Finset NNReal := {a p.1, a p.1 + r p.1 * p.2.1.toNNReal}
    let L : (J -> Plane) →ₗ[Real] Plane :=
      { toFun := fun x =>
          x ⟨a p.1 + r p.1 * p.2.1.toNNReal, by simp [J]⟩ - x ⟨a p.1, by simp [J]⟩
        map_add' := by intro x y; simp; abel
        map_smul' := by intro c x; simp; module }
    exact ⟨J, L.toContinuousLinearMap, fun omega => rfl⟩
  have hm : ∀ i (t : K i), AEMeasurable
      (fun omega => W (a i + r i * t.1.toNNReal) omega - W (a i) omega) P := by
    intro i t
    exact hGaussian.aemeasurable ⟨i, t⟩
  apply hGaussian.iIndepFun_of_covariance_inner hm
  intro i j hij t u x y
  have ht : t.1.toNNReal ≤ 1 := Real.toNNReal_le_one.mpr (hK i t.2).2
  have hu : u.1.toNNReal ≤ 1 := Real.toNNReal_le_one.mpr (hK j u.2).2
  have hi0 : a i ≤ a i + r i * t.1.toNNReal := by simp
  have hj0 : a j ≤ a j + r j * u.1.toNNReal := by simp
  have hiend : a i + r i * t.1.toNNReal ≤ a i + r i := by
    gcongr
    simpa using mul_le_mul_of_nonneg_left ht (show 0 ≤ r i from bot_le)
  have hjend : a j + r j * u.1.toNNReal ≤ a j + r j := by
    gcongr
    simpa using mul_le_mul_of_nonneg_left hu (show 0 ≤ r j from bot_le)
  have hplane : IndepFun
      (fun omega => W (a i + r i * t.1.toNNReal) omega - W (a i) omega)
      (fun omega => W (a j + r j * u.1.toNNReal) omega - W (a j) omega) P := by
    rcases hdisjoint hij with h | h
    · have hai : a i ≤ a j := hi0.trans (hiend.trans h)
      have hv := hW.indepFun_centered_finite_pieces (A := Unit) (B := Unit)
        (a i) (a j) (fun _ => r i * t.1.toNNReal) (fun _ => r j * u.1.toNNReal)
        hai (fun _ => hiend.trans h)
      exact hv.comp (measurable_pi_apply ()) (measurable_pi_apply ())
    · have haj : a j ≤ a i := hj0.trans (hjend.trans h)
      have hv := hW.indepFun_centered_finite_pieces (A := Unit) (B := Unit)
        (a j) (a i) (fun _ => r j * u.1.toNNReal) (fun _ => r i * t.1.toNNReal)
        haj (fun _ => hjend.trans h)
      exact (hv.comp (measurable_pi_apply ()) (measurable_pi_apply ())).symm
  have hscalar := hplane.comp
    (show Measurable (fun z : Plane => inner Real x z) by fun_prop)
    (show Measurable (fun z : Plane => inner Real y z) by fun_prop)
  exact hscalar.covariance_eq_zero
    ((hGaussian.hasGaussianLaw_eval ⟨i, t⟩).memLp_two.const_inner x)
    ((hGaussian.hasGaussianLaw_eval ⟨j, u⟩).memLp_two.const_inner y)

/-! ### Compact Brownian images have a canonical law -/

/-- Any two planar Brownian motions, possibly on different probability spaces, give the same
law to their compact image of a fixed compact time set.  This upgrades equality of all finite
dimensional laws by finite Hausdorff approximation and almost-sure path continuity. -/
theorem IsPlanarBrownian.map_brownianImage_eq
    {Omega Omega' : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    {P : Measure Omega} {Q : Measure Omega'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {W : NNReal -> Omega -> Plane} {V : NNReal -> Omega' -> Plane}
    (hW : IsPlanarBrownian W P) (hV : IsPlanarBrownian V Q)
    (K : NonemptyCompacts Real) :
    P.map (brownianImage W K) = Q.map (brownianImage V K) := by
  let FW : Nat -> Omega -> NonemptyCompacts Plane := fun n omega =>
    finiteImage (finiteCompactApprox (T := K) n)
      (finite_finiteCompactApprox (T := K) n)
      (fun t : K => W t.1.toNNReal omega)
  let FV : Nat -> Omega' -> NonemptyCompacts Plane := fun n omega =>
    finiteImage (finiteCompactApprox (T := K) n)
      (finite_finiteCompactApprox (T := K) n)
      (fun t : K => V t.1.toNNReal omega)
  have hFW : ∀ n, AEMeasurable (FW n) P := by
    intro n
    exact aemeasurable_finiteImage_process P _ _ _
      (fun t => JointMeasurability.aemeasurable_eval hW t.1.toNNReal)
  have hFV : ∀ n, AEMeasurable (FV n) Q := by
    intro n
    exact aemeasurable_finiteImage_process Q _ _ _
      (fun t => JointMeasurability.aemeasurable_eval hV t.1.toNNReal)
  have hFWlim : ∀ᵐ omega ∂P,
      Tendsto (fun n => FW n omega) atTop (nhds (brownianImage W K omega)) := by
    filter_upwards [hW.ae_continuous] with omega homega
    exact tendsto_finiteImage_compactImageOfFunction (0 : Plane)
      (homega.comp (continuous_real_toNNReal.comp continuous_subtype_val))
  have hFVlim : ∀ᵐ omega ∂Q,
      Tendsto (fun n => FV n omega) atTop (nhds (brownianImage V K omega)) := by
    filter_upwards [hV.ae_continuous] with omega homega
    exact tendsto_finiteImage_compactImageOfFunction (0 : Plane)
      (homega.comp (continuous_real_toNNReal.comp continuous_subtype_val))
  have hmaps : ∀ n, P.map (FW n) = Q.map (FV n) := by
    intro n
    let L := finiteCompactApprox (T := K) n
    let hL : (L : Set K).Finite := finite_finiteCompactApprox (T := K) n
    letI : Fintype L := hL.fintype
    change P.map (fun omega => finiteImage L hL (fun t : K => W t.1.toNNReal omega)) =
      Q.map (fun omega => finiteImage L hL (fun t : K => V t.1.toNNReal omega))
    simp_rw [finiteImage_eq_finiteRange]
    exact map_finiteRange_planar_eval_eq hW hV (fun t : L => t.1.1.toNNReal)
  exact map_eq_of_ae_tendsto_of_map_eq hFW hFV
    (hW.aemeasurable_brownianImage K) (hV.aemeasurable_brownianImage K)
    hFWlim hFVlim hmaps

/-- The Brownian image of a compact parameter set after affine time rescaling and Brownian
spatial normalisation.  The intended use has `K ⊆ [0,1]`. -/
noncomputable def rescaledBrownianCompactPiece
    {Omega : Type*} [MeasurableSpace Omega] (W : NNReal -> Omega -> Plane)
    (a r : NNReal) (K : NonemptyCompacts Real) (omega : Omega) : NonemptyCompacts Plane :=
  brownianImage (BrownianImages.intervalRescale W a r) K omega

/-- The unit interval bundled as a nonempty compact time set. -/
noncomputable def unitIntervalCompact : NonemptyCompacts Real :=
  ⟨⟨Set.Icc 0 1, isCompact_Icc⟩, ⟨0, by simp⟩⟩

/-- The unit interval as a nonempty compact set has underlying set `[0,1]`. -/
@[simp]
theorem coe_unitIntervalCompact : (unitIntervalCompact : Set Real) = Set.Icc 0 1 := rfl

/-- The centered image of the Brownian path over `[a, a + r]`, divided by `sqrt r`, with the
usual singleton fallback away from continuous paths. -/
noncomputable def rescaledBrownianPiece
    {Omega : Type*} [MeasurableSpace Omega] (W : NNReal -> Omega -> Plane)
    (a r : NNReal) (omega : Omega) : NonemptyCompacts Plane :=
  brownianImage (BrownianImages.intervalRescale W a r) unitIntervalCompact omega

/-- The reference Brownian image over `[0,1]`. -/
noncomputable def standardBrownianPiece
    {Omega : Type*} [MeasurableSpace Omega] (W : NNReal -> Omega -> Plane)
    (omega : Omega) : NonemptyCompacts Plane :=
  brownianImage W unitIntervalCompact omega

/-- Scalar multiplication of a nonempty compact planar set. -/
noncomputable def smulCompact (q : Real) (K : NonemptyCompacts Plane) :
    NonemptyCompacts Plane :=
  K.map (fun x => q • x) (by fun_prop)

/-- Scalar multiplication is measurable on the compact Hausdorff hyperspace. -/
theorem measurable_smulCompact (q : Real) : Measurable (smulCompact q) := by
  exact (show Continuous (fun x : Plane => q • x) by fun_prop).nonemptyCompacts_map.measurable

/-- The centered, spatially unnormalised image of an arbitrary compact parameter set inside
an affine host interval. -/
noncomputable def centeredBrownianCompactPiece
    {Omega : Type*} [MeasurableSpace Omega] (W : NNReal -> Omega -> Plane)
    (a r : NNReal) (K : NonemptyCompacts Real) (omega : Omega) : NonemptyCompacts Plane :=
  smulCompact (Real.sqrt (r : Real)) (rescaledBrownianCompactPiece W a r K omega)

/-- Brownian scaling for a whole compact path piece: the centered image over `[a,a+r]`, divided
by `sqrt r`, has exactly the law of the Brownian image over `[0,1]`. -/
theorem IsPlanarBrownian.map_rescaledBrownianPiece_eq
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P) (a : NNReal)
    {r : NNReal} (hr : r ≠ 0) :
    P.map (rescaledBrownianPiece W a r) = P.map (standardBrownianPiece W) := by
  exact (hW.intervalRescale a hr).map_brownianImage_eq hW unitIntervalCompact

/-! ### Independence of disjoint compact path pieces -/

/-- Rescaled compact Brownian images over a finite family of pairwise disjoint host intervals
are mutually independent.  The compact parameter set `K i` may vary with `i`, provided it is
contained in `[0,1]`. -/
theorem IsPlanarBrownian.iIndepFun_rescaledBrownianCompactPieces
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P)
    (a r : I -> NNReal) (K : I -> NonemptyCompacts Real)
    (hr : ∀ i, r i ≠ 0)
    (hK : ∀ i, (K i : Set Real) ⊆ Set.Icc 0 1)
    (hdisjoint : ∀ ⦃i j : I⦄, i ≠ j ->
      a i + r i ≤ a j ∨ a j + r j ≤ a i) :
    iIndepFun (fun i => rescaledBrownianCompactPiece W (a i) (r i) (K i)) P := by
  let F : Nat -> I -> Omega -> NonemptyCompacts Plane := fun n i omega =>
    finiteImage (finiteCompactApprox (T := K i) n)
      (finite_finiteCompactApprox (T := K i) n)
      (fun t : K i => BrownianImages.intervalRescale W (a i) (r i) t.1.toNNReal omega)
  have hF : ∀ n i, AEMeasurable (F n i) P := by
    intro n i
    exact aemeasurable_finiteImage_process P _ _ _
      (fun t => JointMeasurability.aemeasurable_eval
        (hW.intervalRescale (a i) (hr i)) t.1.toNNReal)
  have hx : ∀ i, AEMeasurable
      (rescaledBrownianCompactPiece W (a i) (r i) (K i)) P := by
    intro i
    exact (hW.intervalRescale (a i) (hr i)).aemeasurable_brownianImage (K i)
  have hlim : ∀ i, ∀ᵐ omega ∂P,
      Tendsto (fun n => F n i omega) atTop
        (nhds (rescaledBrownianCompactPiece W (a i) (r i) (K i) omega)) := by
    intro i
    filter_upwards [(hW.intervalRescale (a i) (hr i)).ae_continuous] with omega homega
    exact tendsto_finiteImage_compactImageOfFunction (0 : Plane)
      (homega.comp (continuous_real_toNNReal.comp continuous_subtype_val))
  have hfinite : ∀ n, iIndepFun (F n) P := by
    intro n
    have hproc := hW.iIndepFun_centered_compact_piece_processes a r K hK hdisjoint
    let g : (i : I) -> (K i -> Plane) -> NonemptyCompacts Plane := fun i z =>
      finiteImage (finiteCompactApprox (T := K i) n)
        (finite_finiteCompactApprox (T := K i) n)
        (fun t : K i => (Real.sqrt (r i : Real))⁻¹ • z t)
    have hg : ∀ i, Measurable (g i) := by
      intro i
      let L := finiteCompactApprox (T := K i) n
      let hL : (L : Set (K i)).Finite := finite_finiteCompactApprox (T := K i) n
      letI : Fintype L := hL.fintype
      have hsamples : Measurable (fun z : K i -> Plane => fun t : L =>
          (Real.sqrt (r i : Real))⁻¹ • z t.1) := by
        apply measurable_pi_lambda
        intro t
        fun_prop
      have hrange := (measurable_finiteRange (I := L) (E := Plane)).comp hsamples
      change Measurable (fun z : K i -> Plane =>
        finiteImage L hL (fun t : K i => (Real.sqrt (r i : Real))⁻¹ • z t))
      simpa only [finiteImage_eq_finiteRange, Function.comp_def] using hrange
    have hind := hproc.comp g hg
    change iIndepFun (F n) P at hind
    exact hind
  exact iIndepFun_of_ae_tendsto hF hx hlim hfinite

/-- The corresponding centered, spatially unnormalised compact images are mutually independent. -/
theorem IsPlanarBrownian.iIndepFun_centeredBrownianCompactPieces
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P)
    (a r : I -> NNReal) (K : I -> NonemptyCompacts Real)
    (hr : ∀ i, r i ≠ 0)
    (hK : ∀ i, (K i : Set Real) ⊆ Set.Icc 0 1)
    (hdisjoint : ∀ ⦃i j : I⦄, i ≠ j ->
      a i + r i ≤ a j ∨ a j + r j ≤ a i) :
    iIndepFun (fun i => centeredBrownianCompactPiece W (a i) (r i) (K i)) P := by
  have h := hW.iIndepFun_rescaledBrownianCompactPieces a r K hr hK hdisjoint |>.comp
    (fun i => smulCompact (Real.sqrt (r i : Real)))
    (fun i => measurable_smulCompact (Real.sqrt (r i : Real)))
  change iIndepFun (fun i => centeredBrownianCompactPiece W (a i) (r i) (K i)) P at h
  exact h

end BrownianImages
