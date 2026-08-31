/-
Axiom check for `BrownianImages`. Every endpoint below must report
`propext`, `Classical.choice`, `Quot.sound` or a subset of them; anything else
means an axiom has crept in.

The groups follow the module order of the library root.
-/
import BrownianImages.Defs
import BrownianImages.Occupation
import BrownianImages.Empirical
import BrownianImages.Frostman
import BrownianImages.Kernel
import BrownianImages.SelfSimilar
import BrownianImages.Renewal
import BrownianImages.RenewalBridge
import BrownianImages.Periodic
import BrownianImages.Cantor
import BrownianImages.Homometric
import BrownianImages.FourPoint
import BrownianImages.Multiplier
import BrownianImages.GaussianFourPoint
import BrownianImages.WeakBorel
import BrownianImages.Profile
import BrownianImages.Recursion
import BrownianImages.Asymptotics
import BrownianImages.FourierMultiplier
import BrownianImages.Smoothing
import BrownianImages.UniformContinuity
import BrownianImages.JointMeasurability
import BrownianImages.Reduction
import BrownianImages.AhlforsRegular
import BrownianImages.Hutchinson
import BrownianImages.CantorValues
import BrownianImages.Rescaling
import BrownianImages.FourPointBound
import BrownianImages.BlockMass
import BrownianImages.FourPointIntegral
import BrownianImages.Concentration
import BrownianImages.Endpoints
import BrownianImages.VarianceCovariance
import BrownianImages.MainTheorem
import BrownianImages.HomometricMeasures
import BrownianImages.KeyRenewal
import BrownianImages.TailHarmonic
import BrownianImages.KeyRenewalFourier
import BrownianImages.ProfileAsymptotics
import BrownianImages.Separation
import BrownianImages.CantorApplication
import BrownianImages.NonLattice
import BrownianImages.MinkowskiIntervalGap
import BrownianImages.MinkowskiCorrelationLower
import BrownianImages.MinkowskiBrownianPieces
import BrownianImages.MinkowskiCylinderConvergence
import BrownianImages.MinkowskiOverlapTranslation
import BrownianImages.MinkowskiGaussianIncrement
import BrownianImages.MinkowskiOverlapProbability
import BrownianImages.MinkowskiBrownianOverlapGeometry
import BrownianImages.MinkowskiDefectExpectation
import BrownianImages.MinkowskiOverlapAssembly
import BrownianImages.MinkowskiTubeMeanLower
import BrownianImages.MinkowskiTubeUpper
import BrownianImages.MinkowskiBrownianMaximalReduction
import BrownianImages.MinkowskiBrownianMaximalMoment
import BrownianImages.MinkowskiStopping
import BrownianImages.MinkowskiStoppingTubeUpper
import BrownianImages.MinkowskiTubeMeanContinuity
import BrownianImages.MinkowskiTubeMomentAssembly
import BrownianImages.MinkowskiTubeRenewal
import BrownianImages.MinkowskiOverlapSystem
import BrownianImages.MinkowskiTubeRenewalLimit
import BrownianImages.MinkowskiTubeRenewalAssembly
import BrownianImages.MinkowskiL2Recurrence
import BrownianImages.MinkowskiDefectL2
import BrownianImages.MinkowskiContraction
import BrownianImages.MinkowskiAlmostSure
import BrownianImages.MinkowskiRatio
import BrownianImages.MinkowskiTubeConcentrationAssembly
import BrownianImages.MinkowskiTubeEndpointAssembly
import BrownianImages.MinkowskiTubeArithmeticRenewal
import BrownianImages.MinkowskiTubeDiscreteRenewal
import BrownianImages.MinkowskiReconstruction
import BrownianImages.MinkowskiGeneration
import BrownianImages.MinkowskiGenerationScaling
import BrownianImages.MinkowskiGenerationRatio
import BrownianImages.MinkowskiReconstructionAssembly
import BrownianImages.MinkowskiHomogeneousReconstruction
import BrownianImages.MinkowskiFullEndpointAssembly
import BrownianImages.MinkowskiCantorSetApplication

-- the objects of `sec:introduction` and `sec:setup`
#print axioms BrownianImages.measurableSet_corrSet
#print axioms BrownianImages.measurableSet_phiSet

-- the occupation measure as a random point of `𝒫(ℝ²)`
#print axioms BrownianImages.occupationProb_toMeasure
#print axioms BrownianImages.continuous_plane_of_coord
#print axioms BrownianImages.IsPlanarBrownian.ae_continuous
#print axioms BrownianImages.measurable_pathMap
#print axioms BrownianImages.IsPlanarBrownian.ae_isProbabilityMeasure_occupation
#print axioms BrownianImages.IsPlanarBrownian.ae_occupationProb_toMeasure

-- the empirical profile and the grid monotonicity `eq:monotone-fill`
#print axioms BrownianImages.corr_mono
#print axioms BrownianImages.Yprofile_nonneg
#print axioms BrownianImages.Yprofile_le_of_le
#print axioms BrownianImages.monotone_fill
#print axioms BrownianImages.measurable_corr
#print axioms BrownianImages.measurable_Yprofile

-- the pair-distance distribution of a Frostman measure: `eq:phi-frostman`
#print axioms BrownianImages.phi_nonneg
#print axioms BrownianImages.phi_mono
#print axioms BrownianImages.mk_preimage_phiSet
#print axioms BrownianImages.phi_prod_eq
#print axioms BrownianImages.IsFrostman.isFrostmanOpen
#print axioms BrownianImages.IsFrostmanOpen.isFrostman
#print axioms BrownianImages.IsFrostman.measure_singleton
#print axioms BrownianImages.IsAhlforsClosed.isAhlfors
#print axioms BrownianImages.phi_eq_pairLaw
#print axioms BrownianImages.phi_le
#print axioms BrownianImages.mk_preimage_diffSet
#print axioms BrownianImages.pairLaw_measure_singleton
#print axioms BrownianImages.continuous_cdf_toReal
#print axioms BrownianImages.continuous_phi
#print axioms BrownianImages.continuous_G

-- the smoothing kernel of `eq:h-definition`
#print axioms BrownianImages.kern_pos
#print axioms BrownianImages.logKern_pos
#print axioms BrownianImages.logKern_eq
#print axioms BrownianImages.exp_neg_le_inv
#print axioms BrownianImages.logKern_le_of_nonneg
#print axioms BrownianImages.logKern_le_exp_mul
#print axioms BrownianImages.logKern_le_exp_neg_mul_abs
#print axioms BrownianImages.integrable_exp_neg_mul_abs
#print axioms BrownianImages.continuous_logKern
#print axioms BrownianImages.logKern_integrable
#print axioms BrownianImages.kern_le_rpow
#print axioms BrownianImages.kern_le_rpow_of_small
#print axioms BrownianImages.continuousOn_kern
#print axioms BrownianImages.kern_integrableOn
#print axioms BrownianImages.integral_kern_pos
#print axioms BrownianImages.smoothOp_pos

-- strongly separated self-similar systems and their natural measures
#print axioms BrownianImages.System.measurable_map
#print axioms BrownianImages.System.StronglySeparated.mono
#print axioms BrownianImages.System.IsNatural.support_Icc
#print axioms BrownianImages.System.IsNatural.isProbabilityMeasure
#print axioms BrownianImages.half_rpow
#print axioms BrownianImages.cantorSystem_isDimension
#print axioms BrownianImages.cantorSystem_stronglySeparated
#print axioms BrownianImages.pairRatio_pos
#print axioms BrownianImages.pairRatio_rpow
#print axioms BrownianImages.pairRatio_lt_half
#print axioms BrownianImages.pairSystem_isDimension
#print axioms BrownianImages.pairSystem_stronglySeparated
#print axioms BrownianImages.pairSystem_range_logRatio
#print axioms BrownianImages.pairSystem_nonArithmetic_iff
#print axioms BrownianImages.System.logRatio_pos
#print axioms BrownianImages.System.renewalLaw_apply
#print axioms BrownianImages.System.isProbabilityMeasure_renewalLaw
#print axioms BrownianImages.System.integral_id_renewalLaw
#print axioms BrownianImages.System.sum_ofReal_ratio_rpow
#print axioms BrownianImages.System.renewalMean_pos

-- the vendored renewal library, audited here rather than taken on trust
#print axioms AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm
#print axioms AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real

-- the part of it `thm:non-lattice-limit` can use: the renewal equation iterated,
-- which needs the exponential moment but no non-lattice hypothesis
#print axioms AbsorptionCutoff.Renewal.eq_tsum_integral_comp_sub_of_renewalEquation
#print axioms AbsorptionCutoff.Renewal.tendsto_integral_comp_sub_convPow_zero

-- its hypotheses, discharged for `F = ∑ p_i δ_{a_i}`, and the one that is refuted
#print axioms BrownianImages.System.expTransform_renewalLaw
#print axioms BrownianImages.System.exists_expTransform_lt_one
#print axioms BrownianImages.System.not_nonlattice_renewalLaw
#print axioms BrownianImages.cantorSystem
#print axioms BrownianImages.pairSystem

-- the continuous periodic extension `G̃_A` of `sec:renewal`
#print axioms BrownianImages.exists_period_representative
#print axioms BrownianImages.exists_nat_sub_mem_Ico
#print axioms BrownianImages.shift_add_nsmul
#print axioms BrownianImages.exists_periodic_extension
#print axioms BrownianImages.exists_periodic_extension_of_shift

-- `thm:cantor-values`: the middle-thirds constants and the non-constancy
#print axioms BrownianImages.rpow_three_sCantor
#print axioms BrownianImages.sCantor_lt_two_thirds
#print axioms BrownianImages.sCantor_lt_one
#print axioms BrownianImages.two_rpow_two_thirds_lt
#print axioms BrownianImages.three_fifths_two_rpow_lt_one
#print axioms BrownianImages.halfMass_eq
#print axioms BrownianImages.G_log_three
#print axioms BrownianImages.G_log_six
#print axioms BrownianImages.G_log_six_lt_G_log_three
#print axioms BrownianImages.G_add_nsmul_period
#print axioms BrownianImages.G_nonconstant_on_period

-- `thm:homometric-example`: the two digit sets and the common dimension
#print axioms BrownianImages.card_digitsA
#print axioms BrownianImages.card_digitsB
#print axioms BrownianImages.digitsA_ne_digitsB
#print axioms BrownianImages.diffMultiset_eq
#print axioms BrownianImages.diffCount_eq
#print axioms BrownianImages.strong_separation
#print axioms BrownianImages.tHom_mem_Ioo
#print axioms BrownianImages.six_mul_rpow_tHom
#print axioms BrownianImages.digitFunA_injective
#print axioms BrownianImages.digitFunB_injective
#print axioms BrownianImages.range_digitFunA
#print axioms BrownianImages.range_digitFunB
#print axioms BrownianImages.homSystem
#print axioms BrownianImages.homSystem_map
#print axioms BrownianImages.homSystem_stronglySeparated
#print axioms BrownianImages.conv_reflect_eq_map_sub

-- `sec:variance`: the determinants of the two overlapping pairings
#print axioms BrownianImages.crossing_det
#print axioms BrownianImages.crossing_det_ge
#print axioms BrownianImages.nested_det
#print axioms BrownianImages.det_ge_block
#print axioms BrownianImages.length_ge_block
#print axioms BrownianImages.tendsto_rpow_nhdsGT_zero
#print axioms BrownianImages.varScale_div_tendsto_zero

-- `thm:smoothing-injective`: the Fourier multipliers do not vanish
#print axioms BrownianImages.freq_re
#print axioms BrownianImages.gammaMult_ne_zero
#print axioms BrownianImages.smoothOp_periodic
#print axioms BrownianImages.fourierCoeffP_eq_fourierCoeffOn
#print axioms BrownianImages.eq_zero_of_fourierCoeffP_eq_zero
#print axioms BrownianImages.mellin_expNeg
#print axioms BrownianImages.mellin_expNegHalfInv
#print axioms BrownianImages.multInt_eq_gammaMult
#print axioms BrownianImages.multInt_ne_zero

-- `thm:renewal-recursion`: the self-similar recursion
#print axioms BrownianImages.measurable_measure_closedBall
#print axioms BrownianImages.System.IsNatural.measure_eq_sum
#print axioms BrownianImages.System.IsNatural.lintegral_eq_sum
#print axioms BrownianImages.System.StronglySeparated.measure_closedBall_map
#print axioms BrownianImages.phi_recursion
#print axioms BrownianImages.g_recursion

-- the smoothing operator: extrema, continuity, linearity, and the reductions
#print axioms BrownianImages.exists_extrema_of_periodic
#print axioms BrownianImages.exists_bound_of_continuous_periodic
#print axioms BrownianImages.continuous_smoothOp
#print axioms BrownianImages.smoothOp_integrableOn
#print axioms BrownianImages.smoothOp_const
#print axioms BrownianImages.smoothOp_sub
#print axioms BrownianImages.kernel_trivial_of_multiplier
#print axioms BrownianImages.injective_of_multiplier
#print axioms BrownianImages.nonconstant_of_multiplier
#print axioms BrownianImages.exists_measure_closedBall_pos
#print axioms BrownianImages.phi_pos
#print axioms BrownianImages.G_pos
#print axioms BrownianImages.exists_periodic_profile_of_shift
#print axioms BrownianImages.smoothOp_gap

-- `sec:variance`: the block mass, the increments, and the return probability
#print axioms BrownianImages.block_inner_le
#print axioms BrownianImages.block_mid_le
#print axioms BrownianImages.block_relaxed_le
#print axioms BrownianImages.endpoint_block_mass_le
#print axioms BrownianImages.indepFun_pi_of_pair
#print axioms BrownianImages.indepFun_pi_of_pair₀
#print axioms BrownianImages.IsPlanarBrownian.indepFun_coord_increments
#print axioms BrownianImages.IsPlanarBrownian.indepFun_increments
#print axioms BrownianImages.disjoint_increments_indep
#print axioms BrownianImages.IsPlanarBrownian.map_increment
#print axioms BrownianImages.IsPlanarBrownian.return_eq_gaussian
#print axioms BrownianImages.integral_radial
#print axioms BrownianImages.gaussianPDFReal_polar
#print axioms BrownianImages.gaussian_prod_disc
#print axioms BrownianImages.IsPlanarBrownian.return_prob

-- the ambient σ-algebra on `𝒫(ℝ²)`
#print axioms BrownianImages.piBasis_isPiSystem
#print axioms BrownianImages.piBasis_nhds
#print axioms BrownianImages.measurable_evalPi
#print axioms BrownianImages.lowerSemicontinuous_apply
#print axioms BrownianImages.measurable_borel_apply
#print axioms BrownianImages.isOpen_induced_of_isOpen
#print axioms BrownianImages.borel_probabilityMeasure_eq_giry

-- bounds on `G`, and `thm:profile-asymptotics`
#print axioms BrownianImages.phi_le_one
#print axioms BrownianImages.G_nonneg
#print axioms BrownianImages.G_le_exp
#print axioms BrownianImages.measurable_Phi
#print axioms BrownianImages.measurable_G
#print axioms BrownianImages.abs_G_le
#print axioms BrownianImages.profile_asymptotics_nonLattice
#print axioms BrownianImages.exists_nonneg_bound_of_periodic
#print axioms BrownianImages.exists_lattice_bound
#print axioms BrownianImages.profile_asymptotics_lattice
#print axioms BrownianImages.profile_asymptotics_lattice_bigO

-- `eq:fourier-multiplier` and `thm:smoothing-injective`
#print axioms BrownianImages.chr_log
#print axioms BrownianImages.chr_shift
#print axioms BrownianImages.chr_double
#print axioms BrownianImages.fourierCoeffP_smoothOp
#print axioms BrownianImages.smoothOp_eq_zero
#print axioms BrownianImages.smoothOp_injective
#print axioms BrownianImages.smoothOp_nonconstant

-- `thm:profile-uniform-continuity`
#print axioms BrownianImages.H_eq_Hlog
#print axioms BrownianImages.tendsto_integral_logKern_sub
#print axioms BrownianImages.abs_H_sub_le
#print axioms BrownianImages.profile_uniformContinuous

-- joint measurability of the process, and `thm:gaussian-reduction`
#print axioms BrownianImages.IsPlanarBrownian.exists_jointlyMeasurable
#print axioms BrownianImages.JointMeasurability.measurable_occupation
#print axioms BrownianImages.IsPlanarBrownian.aemeasurable_occupationProb
#print axioms BrownianImages.IsPlanarBrownian.isProbabilityMeasure_occupationLaw
#print axioms BrownianImages.Reduction.exists_jointly_measurable_modification
#print axioms BrownianImages.expCorr_eq_integral_prod
#print axioms BrownianImages.expCorr_eq_integral_pairLaw
#print axioms BrownianImages.gaussian_reduction

-- `thm:ahlfors`, and the Frostman bound it yields
#print axioms BrownianImages.AhlforsRegular.measure_closedBall_le_of_isNatural
#print axioms BrownianImages.AhlforsRegular.exists_le_measure_closedBall_of_isNatural
#print axioms BrownianImages.AhlforsRegular.exists_isFrostman_of_isNatural
#print axioms BrownianImages.exists_isAhlforsClosed
#print axioms BrownianImages.exists_isAhlfors_cantor_pair

-- Hutchinson's theorem, and the two natural measures of `sec:setup`
#print axioms BrownianImages.Hutchinson.isCompact_attractorSet
#print axioms BrownianImages.Hutchinson.isNatural_naturalMeasure
#print axioms BrownianImages.Hutchinson.eq_attractorSet
#print axioms BrownianImages.Hutchinson.eq_of_selfSimilar
#print axioms BrownianImages.System.exists_unique_isNatural
#print axioms BrownianImages.exists_unique_isNatural_cantorSystem
#print axioms BrownianImages.exists_unique_isNatural_pairSystem

-- `thm:cantor-values`
#print axioms BrownianImages.phi_cantor_one_third
#print axioms BrownianImages.phi_cantor_half
#print axioms BrownianImages.phi_cantor_one_sixth
#print axioms BrownianImages.cantor_g_period
#print axioms BrownianImages.cantor_values
#print axioms BrownianImages.thm_cantor_values

-- `eq:smoothing`, and the conclusions about the correlation integral
#print axioms BrownianImages.Rescaling.integral_ret_pairLaw
#print axioms BrownianImages.smoothing_of_gaussian_reduction
#print axioms BrownianImages.non_lattice_correlation_limit_of_gaussian_reduction
#print axioms BrownianImages.lattice_correlation_oscillation_of_smoothing

-- `thm:gaussian-four-point`
#print axioms BrownianImages.gaussian_four_point
#print axioms BrownianImages.gaussian_four_point_ae
#print axioms BrownianImages.gaussian_four_point_bundled

-- `thm:endpoint-block-mass` and `thm:four-point-integral`
#print axioms BrownianImages.BlockMass.min_le_block
#print axioms BrownianImages.endpoint_block_mass_of_four_point
#print axioms BrownianImages.endpoint_block_mass_dyadic_of_four_point
#print axioms BrownianImages.FourPointIntegral.tsum_master_le
#print axioms BrownianImages.FourPointIntegral.measurePreserving_perm4
#print axioms BrownianImages.four_point_integral_of_block
#print axioms BrownianImages.variance_of_block
#print axioms BrownianImages.thm_variance_of_block

-- `sec:concentration`
#print axioms BrownianImages.Concentration.integral_Yprofile
#print axioms BrownianImages.Concentration.tailSet_subset_compl
#print axioms BrownianImages.y_variance_of_variance
#print axioms BrownianImages.grid_convergence_of_y_variance
#print axioms BrownianImages.uniform_concentration_of_grid_convergence
#print axioms BrownianImages.main_of_uniform_concentration

-- the composed endpoints
#print axioms BrownianImages.smoothing
#print axioms BrownianImages.non_lattice_correlation_limit
#print axioms BrownianImages.endpoint_block_mass
#print axioms BrownianImages.endpoint_block_mass_dyadic
#print axioms BrownianImages.four_point_integral
#print axioms BrownianImages.exists_periodic_profile
#print axioms BrownianImages.thm_smoothing_injective
#print axioms BrownianImages.lattice_correlation_oscillation

-- `eq:variance`, and `sec:concentration` to its end
#print axioms BrownianImages.variance_le_overlap_lintegral
#print axioms BrownianImages.variance_four_point
#print axioms BrownianImages.variance_bundled
#print axioms BrownianImages.y_variance
#print axioms BrownianImages.grid_convergence
#print axioms BrownianImages.uniform_concentration
#print axioms BrownianImages.main

-- `thm:homometric-example`
#print axioms BrownianImages.HomometricMeasures.homSystem_isDimension
#print axioms BrownianImages.HomometricMeasures.diffLaw_selfSimilar
#print axioms BrownianImages.HomometricMeasures.diffLaw_eq
#print axioms BrownianImages.homometric_example

-- `thm:non-lattice-limit`: the reduction, Choquet-Deny, and the convergence of `G`
#print axioms BrownianImages.KeyRenewal.integral_renewalDefect_eq
#print axioms BrownianImages.KeyRenewal.exists_net
#print axioms BrownianImages.KeyRenewal.const_of_harmonic
#print axioms BrownianImages.const_of_g_recursion
#print axioms BrownianImages.renewalConstant_pos
#print axioms BrownianImages.nonLatticeLimit_of_tendsto
#print axioms BrownianImages.TailHarmonic.uc_of_continuousOn
#print axioms BrownianImages.TailHarmonic.exists_tendsto_atTop_of_continuousOn
#print axioms BrownianImages.exists_tendsto_G
#print axioms BrownianImages.nonLatticeLimit

-- the results that rest on it
#print axioms BrownianImages.Separation.exists_separation_of_tendsto
#print axioms BrownianImages.CantorApplication.exists_profile_oscillation
#print axioms BrownianImages.ProfileAsymptotics.non_lattice_correlation_limit_const
#print axioms BrownianImages.gb_limit
#print axioms BrownianImages.thm_profile_asymptotics
#print axioms BrownianImages.non_lattice_separation
#print axioms BrownianImages.cantor_application
#print axioms BrownianImages.cantor_application_pair

-- `thm:non-lattice-limit` by the paper's route: the vendored theorem under the
-- hypothesis its proof actually consumes
#print axioms BrownianImages.System.nonArithmetic_iff_charFun_ne_one
#print axioms BrownianImages.System.exists_norm_charFun_renewalLaw_eq_one
#print axioms BrownianImages.System.countable_norm_charFun_renewalLaw_eq_one
#print axioms BrownianImages.fellerNonlattice_of_nonlattice
#print axioms BrownianImages.System.fellerNonlattice_renewalLaw
#print axioms AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real
#print axioms BrownianImages.System.tendsto_of_renewalEquation
#print axioms BrownianImages.driNorm_renewalDefect_ne_top
#print axioms BrownianImages.phi_recursion_le
#print axioms BrownianImages.non_lattice_limit

-- `thm:minkowski-reconstruction`: compact images, weak tube limits, Borel
-- reconstruction, and descent of occupation-law singularity
#print axioms BrownianImages.IsPlanarBrownian.aemeasurable_brownianImage
#print axioms BrownianImages.IsPlanarBrownian.isGaussianProcess
#print axioms BrownianImages.IsPlanarBrownian.iIndepFun_centered_compact_piece_processes
#print axioms BrownianImages.IsPlanarBrownian.iIndepFun_rescaledBrownianCompactPieces
#print axioms BrownianImages.IsPlanarBrownian.iIndepFun_centeredBrownianCompactPieces
#print axioms BrownianImages.continuous_tubeProbabilitySeq
#print axioms BrownianImages.measurable_tubeProbabilitySeq
#print axioms BrownianImages.tendsto_tubeRadius
#print axioms BrownianImages.System.sum_sq_tubeWeight_lt_one
#print axioms BrownianImages.tendsto_tubeProbability_of_cylinder_approximation
#print axioms BrownianImages.corr_eq_lintegral_ballMass
#print axioms BrownianImages.lintegral_ballMass_volume
#print axioms BrownianImages.lintegral_ballMass_sq_le_corr
#print axioms BrownianImages.sq_lintegral_le_measure_mul_lintegral_sq
#print axioms BrownianImages.discArea_le_tubeVolume_mul_corr
#print axioms BrownianImages.corr_two_mul_pos_of_support
#print axioms BrownianImages.tubeArea_ge_discArea_div_corr
#print axioms BrownianImages.integral_tubeOverlapArea_translate
#print axioms BrownianImages.integral_density_mul_tubeOverlapArea_translate_le
#print axioms BrownianImages.measurePreserving_planeProdMeasurableEquiv
#print axioms BrownianImages.planarGaussianDensity_le
#print axioms BrownianImages.prod_gaussian_eq_map_planarGaussianDensity
#print axioms BrownianImages.IsPlanarBrownian.map_increment_eq_withDensity
#print axioms BrownianImages.integral_tubeOverlapArea_translate_le_of_indep_boundedDensity
#print axioms BrownianImages.IsPlanarBrownian.indepFun_compactPieces_gapIncrement
#print axioms BrownianImages.IsPlanarBrownian.ae_tubeOverlapArea_affineCompactPieces_eq_gap
#print axioms BrownianImages.IsPlanarBrownian.integral_tubeOverlapArea_compactPieces_gap_le_rpow
#print axioms BrownianImages.IsPlanarBrownian.integrable_and_integral_tubeOverlapArea_affineCompactPieces_gap_le_rpow
#print axioms BrownianImages.System.StronglySeparated.firstLevel_interval_order
#print axioms BrownianImages.System.IntervalSeparated.exists_gap_and_pair_order
#print axioms BrownianImages.continuous_tubeDefect
#print axioms BrownianImages.aemeasurable_tubeDefect_of_forall
#print axioms BrownianImages.integrable_tubeDefect_of_pairwise_overlap
#print axioms BrownianImages.integral_tubeDefect_le_half_sum_pairwise
#print axioms BrownianImages.integral_tubeDefect_le_card_sq_mul
#print axioms BrownianImages.exists_pairwise_overlap_and_defect_bound
#print axioms BrownianImages.System.IsNatural.tubeOverlap_of_pairwise
#print axioms BrownianImages.half_tubeArea_le_tubeMass_two_mul
#print axioms BrownianImages.IsPlanarBrownian.ae_occupation_compl_brownianImage_eq_zero
#print axioms BrownianImages.exists_expected_tubeMass_lower_of_frostman
#print axioms BrownianImages.System.IsNatural.exists_expected_tubeMass_lower_of_tubeMomentUpper
#print axioms BrownianImages.System.IsNatural.tubeMoments_of_upper
#print axioms BrownianImages.IsPlanarBrownian.intervalOscillation_moment_le_of_standard
#print axioms BrownianImages.System.IsPlanarBrownian.stopping_tube_moments_card_bound
#print axioms BrownianImages.System.IsNatural.tubeMomentUpper_of_standardRadiusMoments
#print axioms BrownianImages.System.IsNatural.integrable_brownianTubeProfile_of_standardRadiusSecondMoment
#print axioms BrownianImages.continuousAt_tubeMass_radius
#print axioms BrownianImages.IsPlanarBrownian.continuous_meanBrownianTubeProfile_of_integrable
#print axioms BrownianImages.System.IsNatural.tubeMoments_of_standardRadiusMoments
#print axioms BrownianImages.System.IsNatural.meanTubeProfile_data_of_standardRadiusMoments
#print axioms BrownianImages.System.IsNatural.exists_pairwise_tubeOverlap_of_tubeArea_mean_upper
#print axioms BrownianImages.System.IsNatural.tubeOverlap_of_tubeMomentsUpper
#print axioms BrownianImages.IsPlanarBrownian.identDistrib_normalizedTubeMass_brownianFirstLevelPiece
#print axioms BrownianImages.IsPlanarBrownian.integrable_brownianTubeProfile_and_mean_renewal_eq
#print axioms BrownianImages.System.IsNatural.meanBrownianTubeDefectProfile_le_of_tubeDefect_mean_le
#print axioms BrownianImages.IsPlanarBrownian.mean_tube_renewal_of_pairwise_overlap
#print axioms BrownianImages.System.tubeNonArithmetic_iff_nonArithmetic
#print axioms BrownianImages.System.IsNatural.meanBrownianTubeProfile_tendsto_of_pairwise_overlap
#print axioms BrownianImages.System.IsNatural.meanBrownianTubeProfile_tendsto_of_standardRadiusMoments
#print axioms BrownianImages.MinkowskiL2Recurrence.centeredL2Norm_weighted_sum
#print axioms BrownianImages.MinkowskiL2Recurrence.centeredL2Norm_recurrence_of_iIndepFun_identDistrib_le
#print axioms BrownianImages.MinkowskiContraction.exists_exponential_decay_of_delayed_sqrt_recurrence
#print axioms BrownianImages.MinkowskiAlmostSure.ae_tendsto_zero_of_summable_deviations
#print axioms BrownianImages.MinkowskiAlmostSure.ae_tendsto_zero_of_exponential_deviation_bound
#print axioms BrownianImages.MinkowskiAlmostSure.ae_tendsto_zero_of_exponential_eLpNorm_sq_bound
#print axioms BrownianImages.MinkowskiAlmostSure.ae_tendsto_zero_of_exponential_eLpNorm_bound
#print axioms BrownianImages.MinkowskiAlmostSure.ae_tendsto_zero_along_phase_of_exponential_eLpNorm_bound
#print axioms BrownianImages.MinkowskiAlmostSure.tubeGridConcentration_of_exponential_eLpNorm
#print axioms BrownianImages.MinkowskiRatio.tendsto_weight_mul_div_of_centered_errors
#print axioms BrownianImages.MinkowskiTransfer.mutuallySingular_of_map
#print axioms BrownianImages.MinkowskiTransfer.mutuallySingular_laws_of_ae_reconstruction
#print axioms BrownianImages.MinkowskiTransfer.rangeLaw_mutuallySingular_of_reconstructs_occupation
#print axioms BrownianImages.MinkowskiLimit.exists_common_measurable_reconstruction_of_ae_hasLimit
#print axioms BrownianImages.MinkowskiLimit.exists_common_measurable_reconstruction_of_ae_tendsto
#print axioms BrownianImages.MinkowskiLimitClassifier.exists_measurableSet_limit_classifier
#print axioms BrownianImages.MinkowskiTubeConvergence.measurableSet_tubeCauchySet
#print axioms BrownianImages.MinkowskiTubeConvergence.tubeProbabilitySeq_compl_cthickening_one
#print axioms BrownianImages.MinkowskiTubeConvergence.isCompact_tubeSupportSet
#print axioms BrownianImages.MinkowskiTubeConvergence.mem_tubeCauchySet_iff_exists_tendsto
#print axioms BrownianImages.MinkowskiTubeConvergence.ae_tube_hasLimit_brownianImageLaw_of_ae_tendsto
#print axioms BrownianImages.MinkowskiReconstruction.tubeReconstructsOccupation_of_ae_cylinder_approximation
#print axioms BrownianImages.MinkowskiReconstruction.TubeReconstructsOccupation.imageLaw
#print axioms BrownianImages.MinkowskiReconstruction.exists_common_borel_reconstruction_of_pathwise
#print axioms BrownianImages.MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise
#print axioms BrownianImages.MinkowskiReconstruction.brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction
#print axioms BrownianImages.MinkowskiReconstruction.homogeneous_brownianImage_application_pair_of_pathwise
#print axioms BrownianImages.System.sum_generationWeight
#print axioms BrownianImages.System.IsAttractor.generationCompactUnion_eq
#print axioms BrownianImages.System.IsNatural.tendsto_generationQuadrature
#print axioms BrownianImages.System.IsAttractor.tendsto_weighted_diam_brownianGenerationCylinder
#print axioms BrownianImages.System.IsNatural.tubeReconstructsOccupation_of_generation_tubeMassRatio
#print axioms BrownianImages.MinkowskiReconstruction.brownianImageLaw_mutuallySingular_of_generation_tubeMassRatio
#print axioms BrownianImages.MinkowskiReconstruction.homogeneous_brownianImage_application_pair_of_generation_tubeMassRatio

-- the unconditional Brownian tube estimates and reconstruction quotient
#print axioms BrownianImages.IsPlanarBrownian.integrable_one_add_standardBrownianRadius_rpow
#print axioms BrownianImages.System.IsNatural.exists_normalizedTubeDefect_lpNorm_decay_of_tubeMomentsUpper
#print axioms BrownianImages.System.IsNatural.tubeConcentration_of_standardRadiusMoments
#print axioms BrownianImages.System.IsNatural.tubeMoments
#print axioms BrownianImages.System.IsNatural.tubeOverlap
#print axioms BrownianImages.System.IsNatural.meanBrownianTubeProfile_tendsto
#print axioms BrownianImages.System.IsNatural.tubeConcentration
#print axioms BrownianImages.System.IsNatural.meanBrownianTubeProfile_periodic_limit_of_discrete_renewal
#print axioms BrownianImages.DiscreteRenewal.FiniteDelayLaw.tendsto_renewalMass
#print axioms BrownianImages.DiscreteRenewal.FiniteDelayLaw.tendsto_intRenewalMass_shift
#print axioms BrownianImages.DiscreteRenewal.FiniteDelayLaw.renewal_convolution_identity
#print axioms BrownianImages.System.exists_eventual_profile_eq_latticeSection
#print axioms BrownianImages.System.IsNatural.meanBrownianTubeProfile_periodic_limit_of_tubeArithmetic
#print axioms BrownianImages.IsPlanarBrownian.identDistrib_normalizedTubeMass_brownianGenerationCylinder
#print axioms BrownianImages.IsPlanarBrownian.ae_tendsto_centeredBrownianGenerationTubeProfile
#print axioms BrownianImages.System.IsNatural.ae_generation_tubeMassRatio_of_exponential_concentration
#print axioms BrownianImages.System.IsNatural.tubeReconstructsOccupation_of_nonArithmetic_mean_limit
#print axioms BrownianImages.System.IsNatural.tubeReconstructsOccupation_of_arithmetic_periodic_limit
#print axioms BrownianImages.System.IsNatural.tubeReconstructsOccupation_of_tubeNonArithmetic
#print axioms BrownianImages.System.IsNatural.meanBrownianTubeProfile_periodic_limit
#print axioms BrownianImages.System.IsNatural.tubeRenewal
#print axioms BrownianImages.System.IsNatural.tubeReconstructsOccupation
#print axioms BrownianImages.System.IsNatural.minkowskiReconstruction
#print axioms BrownianImages.System.IsNatural.tubeReconstructsOccupation_homogeneousSystem
#print axioms BrownianImages.System.IsNatural.exists_borel_reconstruction_homogeneousSystem
#print axioms BrownianImages.MinkowskiReconstruction.homogeneous_brownianImage_application_pair_unconditional
