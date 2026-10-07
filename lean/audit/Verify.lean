module

public import LogTwo

@[expose] public section

#print axioms LogTwo.Analysis.column_y_degree_le
#print axioms LogTwo.Analysis.log_center_factor_le
#print axioms LogTwo.Analysis.leibniz_center_growth_le
#print axioms LogTwo.Analysis.center_growth_tendsto

/-! Audit the actual theorems, including their transitive axiom dependencies. -/
#check LogTwo.logTwoExponentTwo_of_sequentialLowerBound
#check LogTwo.Interpolation.FullRowMinor

#print axioms LogTwo.sequentialLowerBound_iff
#print axioms LogTwo.irrational_of_eventualLowerBound
#print axioms LogTwo.exponent_eq_two_of_sequentialLowerBound
#print axioms LogTwo.logTwoExponentTwo_of_sequentialLowerBound
#print axioms LogTwo.Parameters.explicit_shape
#print axioms LogTwo.Parameters.gap_before_eta
#print axioms LogTwo.Parameters.gap_after_eta
#print axioms LogTwo.Parameters.epsilon_eq
#print axioms LogTwo.Parameters.nu_div_factor
#print axioms LogTwo.Parameters.scalarConditions
#print axioms LogTwo.Parameters.growth_ratios
#print axioms LogTwo.Parameters.dimension_growth
#print axioms LogTwo.Parameters.volume_ratio_half
#print axioms LogTwo.Geometry.complex_centerY_injective
#print axioms LogTwo.Geometry.logTwo_constant_fiber_card_le_one
#print axioms LogTwo.Geometry.sum_contact_le_of_constant_fiber
#print axioms LogTwo.Interpolation.coefficient_oneColumn
#print axioms LogTwo.Interpolation.coefficient_yColumn
#print axioms LogTwo.Interpolation.FullRowMinor.matrix_det_ne_zero
#print axioms LogTwo.Determinant.det_scale
#print axioms LogTwo.Determinant.scaled_integer_det_ne_zero
#print axioms LogTwo.Determinant.scaled_integer_lower_bound
#print axioms LogTwo.Determinant.contradiction_of_scaled_upper_bound

#check LogTwo.Arithmetic.fullRowMinor_bound_of_ceilLogWeights
#print axioms LogTwo.Polynomial.coeff_rescale
#print axioms LogTwo.Arithmetic.lcmBelow_ne_zero
#print axioms LogTwo.Arithmetic.map_integerLog
#print axioms LogTwo.Arithmetic.map_integerFactor
#print axioms LogTwo.Arithmetic.map_integerColumnExpansion
#print axioms LogTwo.Arithmetic.integerMatrix_cast
#print axioms LogTwo.Arithmetic.fullRowMinor_arithmetic_bound
#print axioms LogTwo.Arithmetic.fullRowMinor_logarithmic_bound
#print axioms LogTwo.Arithmetic.alpha_le_floor
#print axioms LogTwo.Arithmetic.fullRowMinor_uniform_log_bound
#print axioms LogTwo.Arithmetic.log_lcmBelow_le
#print axioms LogTwo.Arithmetic.truncation_denominatorBudget_le
#print axioms LogTwo.Arithmetic.ceilLogWeight_bounds
#print axioms LogTwo.Arithmetic.rowLogSaving_lower
#print axioms LogTwo.Arithmetic.averageRowWeight_bounds
#print axioms LogTwo.Arithmetic.fullRowMinor_normalized_arithmetic_bound
#print axioms LogTwo.Arithmetic.fullRowMinor_bound_of_ceilLogWeights

#check LogTwo.exists_small_arithmetic_parameters
#print axioms LogTwo.exists_unbounded_of_not_sequential
#print axioms LogTwo.Parameters.centerCount_bounds
#print axioms LogTwo.Parameters.count_over_horizontal_tendsto
#print axioms LogTwo.Parameters.verticalWeight_tendsto
#print axioms LogTwo.Parameters.dimension_over_vertical_tendsto
#print axioms LogTwo.Parameters.exists_dimension
#print axioms LogTwo.Parameters.chosen_volume_ratio
#print axioms LogTwo.exists_large_log_approximation
#print axioms LogTwo.exists_sequential_approximations
#print axioms LogTwo.arithmeticError_le_uniform
#print axioms LogTwo.exists_small_arithmetic_parameters

#check LogTwo.Geometry.logWord_order_lower_at
#print axioms LogTwo.Geometry.coeff_scaleY
#print axioms LogTwo.Geometry.scaleY_preserves_weightedDegree
#print axioms LogTwo.Geometry.scaleY_polynomialFrameWord
#print axioms LogTwo.Geometry.aeval_normalizeY_scaled_word
#print axioms LogTwo.Geometry.logTwo_formalJet_frameMonomial
#print axioms LogTwo.Geometry.formalJetAt_polynomialFrameWord
#print axioms LogTwo.Geometry.formalJetAt_word_vanishing
#print axioms LogTwo.Geometry.coordinateOrder_div_constant
#print axioms LogTwo.Geometry.coordinatePole_normalizeY
#print axioms LogTwo.Geometry.weightedDegree_normalizeY
#print axioms LogTwo.Geometry.valuation_normalizeY_sub_center
#print axioms LogTwo.Geometry.normalized_centered_iff
#print axioms LogTwo.Geometry.normalized_nonconstant
#print axioms LogTwo.Geometry.logContactAt_pos
#print axioms LogTwo.Geometry.logWord_order_lower_at
#print axioms LogTwo.Geometry.logContactAt_fiber

#print axioms LogTwo.Geometry.shiftMap_truncatedJetAt
#print axioms LogTwo.Geometry.formalJetAt_surjective_iff_truncated

#print axioms LogTwo.Arithmetic.truncation_weight_lower

#print axioms LogTwo.Geometry.center_index_unique_of_constantY

#check LogTwo.Geometry.constant_fiber_family_contact_sum_le
#check LogTwo.Geometry.coefficientMatrix_eq_truncatedJetAt
#print axioms LogTwo.Geometry.weightedDegree_constant_fiber
#print axioms LogTwo.Geometry.constant_fiber_contact_sum_le
#print axioms LogTwo.Geometry.constant_fiber_family_contact_sum_le
#print axioms LogTwo.Geometry.rationalJetEmbedding_C
#print axioms LogTwo.Geometry.rationalJetEmbedding_X
#print axioms LogTwo.Geometry.coeff_rationalJetEmbedding
#print axioms LogTwo.Geometry.rationalJetEmbedding_truncatedLog
#print axioms LogTwo.Geometry.truncatedJetAt_frameMonomial
#print axioms LogTwo.Geometry.rationalJetEmbedding_columnExpansion
#print axioms LogTwo.Geometry.coefficientMatrix_eq_truncatedJetAt

#check LogTwo.Geometry.fullRowMinor_of_formal_packets
#check LogTwo.Geometry.eventually_exists_auxiliary_words_at_centers
#print axioms LogTwo.Geometry.columnWeight_pos
#print axioms LogTwo.Geometry.jetWeight_pos
#print axioms LogTwo.Geometry.cast_jetWeight
#print axioms LogTwo.Geometry.columnOfIndex_valid
#print axioms LogTwo.Geometry.rowOfIndex_valid
#print axioms LogTwo.Geometry.columnOfIndex_injective
#print axioms LogTwo.Geometry.rowOfIndex_injective
#print axioms LogTwo.Geometry.exists_rowIndex
#print axioms LogTwo.Geometry.rowExponent_index
#print axioms LogTwo.Geometry.monomial_eq_C_mul_frameMonomial
#print axioms LogTwo.Geometry.indexedMatrix_mulVec_eq_coeff
#print axioms LogTwo.Geometry.indexedMatrix_surjective_of_truncated_packets
#print axioms LogTwo.Geometry.indexedMatrix_surjective_of_formal_packets
#print axioms LogTwo.Geometry.fullRowMinor_of_indexedMatrix_surjective
#print axioms LogTwo.Geometry.fullRowMinor_of_formal_packets
#print axioms LogTwo.Geometry.eventually_exists_auxiliary_at_centers
#print axioms LogTwo.Geometry.eventually_exists_auxiliary_at_centers_nat
#print axioms LogTwo.Geometry.eventually_exists_auxiliary_words_at_centers

#check LogTwo.Geometry.curve_words_vanish_of_excess
#print axioms LogTwo.Geometry.curve_words_vanish_of_excess

#check LogTwo.Geometry.chosenWeights_geometric_margins
#check LogTwo.Geometry.rigidity_data_of_excess
#print axioms LogTwo.Geometry.ContactFamilyAt.mem_places
#print axioms LogTwo.Geometry.ContactFamilyAt.centered
#print axioms LogTwo.Geometry.ContactFamilyAt.nonconstant
#print axioms LogTwo.Geometry.ContactFamilyAt.contact_eq
#print axioms LogTwo.Geometry.ContactFamilyAt.contact_pos
#print axioms LogTwo.Geometry.ContactFamilyAt.contact_nonneg
#print axioms LogTwo.Geometry.ContactFamilyAt.words_vanish_of_excess
#print axioms LogTwo.Geometry.ContactFamilyAt.eventually_exists_annihilator_of_excess
#print axioms LogTwo.Geometry.rationalColumnWeight_pos
#print axioms LogTwo.Geometry.cast_rationalColumnWeight
#print axioms LogTwo.Geometry.weighted_volume_ratio
#print axioms LogTwo.Geometry.curveSigma_pos
#print axioms LogTwo.Geometry.curveSigma_contact_margin
#print axioms LogTwo.Geometry.pow_mul_one_sub_mul_le_one
#print axioms LogTwo.Geometry.curveSigma_power_bound
#print axioms LogTwo.Geometry.curveSigma_volume_lt_one
#print axioms LogTwo.Geometry.chosenWeights_half_volume
#print axioms LogTwo.Geometry.chosenWeights_geometric_margins
#print axioms LogTwo.Geometry.ContactFamilyAt.contact_sum_le_of_constantY
#print axioms LogTwo.Geometry.ContactFamilyAt.no_excess_of_constantY
#print axioms LogTwo.Geometry.weights_no_excess_of_constantY
#print axioms LogTwo.Geometry.chosenWeights_annihilator_of_excess
#print axioms LogTwo.Geometry.mem_coordinateKernel
#print axioms LogTwo.Geometry.eval_center_eq_zero_of_aeval_eq_zero
#print axioms LogTwo.Geometry.coordinateKernel_lt_pointKernel
#print axioms LogTwo.Geometry.coordinateKernel_height_le
#print axioms LogTwo.Geometry.coordinateKernel_X_zero_not_mem
#print axioms LogTwo.Geometry.cast_word_cost
#print axioms LogTwo.Geometry.rigidity_data_of_excess

#check LogTwo.Geometry.EventualKernelComparison
#print axioms LogTwo.Geometry.separatedProducts_of_growth
#print axioms LogTwo.Geometry.normalizedLogWeights_one_le
#print axioms LogTwo.Geometry.normalizedLogWeights_prod
#print axioms LogTwo.Geometry.chosenWeights_separatedProducts
#print axioms LogTwo.Geometry.exists_small_arithmetic_separated_parameters
#print axioms LogTwo.Geometry.rigidityComparisonConstant_pos
#print axioms LogTwo.Geometry.eventually_uniformRectangles_nat
#print axioms LogTwo.Geometry.coordinate_constant_of_persistent_comparison
#print axioms LogTwo.Geometry.coordinate_eq_center_of_persistent_comparison
#print axioms LogTwo.Geometry.constantY_of_excess_of_comparison
#print axioms LogTwo.Geometry.contact_bound_of_comparison
#print axioms LogTwo.Geometry.chosenWeights_contact_bound_of_comparison

#check LogTwo.Geometry.exists_small_arithmetic_separated_parameters
#check LogTwo.Geometry.chosenWeights_contact_bound_of_comparison

#print axioms LogTwo.Geometry.logarithmic_normal_comparison
#print axioms LogTwo.Geometry.logarithmic_persistent_comparison
#print axioms LogTwo.Geometry.eventualKernelComparison
#print axioms LogTwo.Geometry.contact_bound
#print axioms LogTwo.Geometry.chosenComparisonConstant_pos
#print axioms LogTwo.Geometry.chosenWeights_contact_bound
#print axioms LogTwo.Geometry.nonconstant_coordinates_of_trdeg_one
#print axioms LogTwo.Geometry.chosenWeights_intrinsic_contact_bound
#print axioms LogTwo.Geometry.logTwo_intrinsic_contact_bound

#check LogTwo.Geometry.eventualKernelComparison
#check LogTwo.Geometry.logTwo_intrinsic_contact_bound
#print axioms LogTwo.Analysis.scaled_log_monomial_identity
#print axioms LogTwo.Analysis.exp_logTwo_center
#print axioms LogTwo.Analysis.logTwo_scaled_log_monomial_identity

#print axioms LogTwo.Geometry.scaleY_comp
#print axioms LogTwo.Geometry.scaleY_one
#print axioms LogTwo.Geometry.aeval_comp_scaleY
#print axioms LogTwo.Geometry.jetIdealAt_eq_map_inverse
#print axioms LogTwo.Geometry.radical_jetIdealAt
#print axioms LogTwo.Geometry.zeroLocus_jetIdealAt
#print axioms LogTwo.Geometry.centerPrime_injective_of_Y
#print axioms LogTwo.Geometry.logTwo_centerPrime_injective
#print axioms LogTwo.Geometry.zeroLocus_finset_prod_jetIdealAt
#print axioms LogTwo.Geometry.zeroLocus_jetProductIdeal
#print axioms LogTwo.Geometry.formalJetAt_mem_weighted_of_mem_pow
#print axioms LogTwo.Geometry.jetProductIdeal_pow_le
#print axioms LogTwo.Geometry.formalJetAt_packet_zero_of_mem_product_pow
#print axioms LogTwo.Geometry.map_jetIdealAt_aeval
#print axioms LogTwo.Geometry.lift_normalizeY
#print axioms LogTwo.Geometry.localJetIdealAt_eq
#print axioms LogTwo.Geometry.localJetIdealAt_colength_eq_contact
#print axioms LogTwo.Geometry.localJetIdealAt_colength_ne_top
#print axioms LogTwo.Geometry.jetIdealAt_pairwise_coprime
#print axioms LogTwo.Geometry.jetIdealAt_residue_surjective

#check LogTwo.Geometry.localJetIdealAt_colength_eq_contact
#check LogTwo.Geometry.formalJetAt_packet_zero_of_mem_product_pow
#check LogTwo.Geometry.jetIdealAt_residue_surjective

#print axioms LogTwo.Geometry.isUnit_of_residueAugmentation_ne_zero
#print axioms LogTwo.Geometry.map_jetIdealAt_eq_top_of_residue_ne
#print axioms LogTwo.Geometry.map_jetProductIdeal_eq_factor
#print axioms LogTwo.Geometry.localJetProductIdeal_eq
#print axioms LogTwo.Geometry.localJetProductIdeal_colength_eq_contact
#print axioms LogTwo.Geometry.localJetProductIdeal_colength_ne_top
#print axioms LogTwo.Geometry.CompactJetIdealAt.point_section
#print axioms LogTwo.Geometry.CompactJetIdealAt.range_point
#print axioms LogTwo.Geometry.CompactJetIdealAt.support_affineIdeal
#print axioms LogTwo.Geometry.CompactJetIdealAt.restrict_compactIdeal
#print axioms LogTwo.Geometry.CompactJetIdealAt.comap_compactIdeal_spec
#print axioms LogTwo.Geometry.CompactJetIdealAt.support_compactIdeal
#print axioms LogTwo.Geometry.CompactJetIdealAt.compactIdeal_isFinitePresentation
#print axioms LogTwo.Geometry.CompactJetIdealAt.comap_compactIdeal_eq_top_of_avoids_centers
#print axioms LogTwo.Geometry.truncation_weight_strict
#print axioms LogTwo.Geometry.chosen_truncation_weight_strict

#check LogTwo.Geometry.localJetProductIdeal_colength_eq_contact
#check LogTwo.Geometry.CompactJetIdealAt.comap_compactIdeal_spec
#check LogTwo.Geometry.CompactJetIdealAt.support_compactIdeal
#check LogTwo.Geometry.chosen_truncation_weight_strict

#print axioms LogTwo.Geometry.IntegralProj.homogeneous_isReduced
#print axioms LogTwo.Geometry.IntegralProj.proj_isReduced
#print axioms LogTwo.Geometry.IntegralProj.genericPoint_dense
#print axioms LogTwo.Geometry.IntegralProj.proj_irreducible
#print axioms LogTwo.Geometry.IntegralProj.proj_isIntegral
#print axioms LogTwo.Geometry.MatrixCompactification.index_nonempty
#print axioms LogTwo.Geometry.MatrixCompactification.structureMap_proper
#print axioms LogTwo.Geometry.MatrixCompactification.affineChart_isOpenImmersion
#print axioms LogTwo.Geometry.MatrixCompactification.space_nonempty
#print axioms LogTwo.Geometry.MatrixCompactification.space_isIntegral
#print axioms LogTwo.Geometry.MatrixCompactification.space_isLocallyNoetherian
#print axioms LogTwo.Geometry.MatrixCompactification.space_compact
#print axioms LogTwo.Geometry.MatrixCompactification.space_isNoetherian
#print axioms LogTwo.Geometry.MatrixCompactification.affineChart_quasiCompact
#print axioms LogTwo.Geometry.MatrixCompactification.affineChart_over
#print axioms LogTwo.Geometry.MatrixCompactification.affineChart_denseRange
#print axioms LogTwo.Geometry.MatrixCompactification.degree_balance
#print axioms LogTwo.Geometry.MatrixCompactification.jet_balance
#print axioms LogTwo.Geometry.MatrixCompactification.monomial_budget
#print axioms LogTwo.Geometry.MatrixCompactification.centerIdeal_restrict
#print axioms LogTwo.Geometry.MatrixCompactification.centerIdeal_support
#print axioms LogTwo.Geometry.MatrixCompactification.centerIdeal_support_finite
#print axioms LogTwo.Geometry.MatrixCompactification.centerIdeal_support_subset_chart
#print axioms LogTwo.Geometry.MatrixCompactification.centerIdeal_coherent
#print axioms LogTwo.Geometry.MatrixCompactification.centerIdeal_affine_pullback
#print axioms LogTwo.Geometry.MatrixCompactification.center_points_injective
#print axioms LogTwo.Geometry.MatrixCompactification.origin_ne_center
#print axioms LogTwo.Geometry.MatrixCompactification.origin_avoids_centers
#print axioms LogTwo.Geometry.MatrixCompactification.centerIdeal_support_ne_top
#print axioms LogTwo.Geometry.MatrixCompactification.formalJet_packet_zero
#print axioms LogTwo.Geometry.MatrixCompactification.logTwoIdeal_support_finite
#print axioms LogTwo.Geometry.MatrixCompactification.logTwoIdeal_support_ne_top
#print axioms LogTwo.Geometry.MatrixCompactification.logTwo_centers_injective
#print axioms LogTwo.Geometry.MatrixCompactification.branchMap_over
#print axioms LogTwo.Geometry.MatrixCompactification.branchMap_generic
#print axioms LogTwo.Geometry.MatrixCompactification.centerIdeal_branch_pullback
#print axioms LogTwo.Geometry.MatrixCompactification.branchIdeal_eq
#print axioms LogTwo.Geometry.MatrixCompactification.branch_colength_eq_contact
#print axioms LogTwo.Geometry.MatrixCompactification.branch_colength_ne_top
#check LogTwo.Geometry.MatrixCompactification.structureMap_proper
#check LogTwo.Geometry.MatrixCompactification.centerIdeal_coherent
#check LogTwo.Geometry.MatrixCompactification.centerIdeal_branch_pullback
#check LogTwo.Geometry.MatrixCompactification.branch_colength_eq_contact
#check LogTwo.Geometry.MatrixCompactification.branchMap_generic

-- Constructed global normalization map and actual DVR pullback.
#print axioms LogTwo.Geometry.MatrixCompactification.space_isSeparated
#print axioms LogTwo.Geometry.MatrixCompactification.exists_curveMap
#print axioms LogTwo.Geometry.MatrixCompactification.curveMap_over
#print axioms LogTwo.Geometry.MatrixCompactification.curveMap_generic
#print axioms LogTwo.Geometry.MatrixCompactification.curveMap_center
#print axioms LogTwo.Geometry.MatrixCompactification.curve_center_stalk_isIso
#print axioms LogTwo.Geometry.MatrixCompactification.curveMap_stalk
#print axioms LogTwo.Geometry.MatrixCompactification.curveIdeal_center_pullback
#print axioms LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_eq_branchIdeal
#print axioms LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_colength_eq_contact
#print axioms LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_colength_ne_top
#check LogTwo.Geometry.MatrixCompactification.exists_curveMap
#check LogTwo.Geometry.MatrixCompactification.curveMap_stalk
#check LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_colength_eq_contact

-- Nonzero global pullback, off-center vanishing, and actual finite colength cycle.
#print axioms LogTwo.Geometry.centeredAt_of_closedPoint_eq
#print axioms LogTwo.Geometry.map_jetIdealAt_eq_top_of_nonconstant
#print axioms LogTwo.Geometry.map_jetProductIdeal_eq_top_of_transcendental
#print axioms LogTwo.Geometry.MatrixCompactification.curveIdeal_generic_pullback
#print axioms LogTwo.Geometry.MatrixCompactification.curveIdeal_ne_bot
#print axioms LogTwo.Geometry.MatrixCompactification.curveMap_centered_of_mem_support
#print axioms LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_eq_top_of_not_mem_support
#print axioms LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_eq_top_of_not_mem_places
#print axioms LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_colength_zero_off_places
#print axioms LogTwo.Geometry.MatrixCompactification.curveColengthCycle_apply
#print axioms LogTwo.Geometry.MatrixCompactification.curveColengthCycle_support_subset
#print axioms LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_colength_finite_all
#print axioms LogTwo.Geometry.MatrixCompactification.curveColengthCycle_eq_contact
#print axioms LogTwo.Geometry.MatrixCompactification.curveColengthCycle_sum_eq_contact
#print axioms LogTwo.Geometry.MatrixCompactification.curveColengthCycle_natCast_eq_length
#print axioms LogTwo.Geometry.MatrixCompactification.curveColengthCycle_support_eq_places
#check LogTwo.Geometry.MatrixCompactification.curveIdeal_ne_bot
#check LogTwo.Geometry.MatrixCompactification.curveLocalIdeal_colength_finite_all
#check LogTwo.Geometry.MatrixCompactification.curveColengthCycle_natCast_eq_length
#check LogTwo.Geometry.MatrixCompactification.curveColengthCycle_sum_eq_contact

-- Actual section divisor and Euler degree, under an explicit ideal presentation.
#print axioms LogTwo.Geometry.SectionIdealBridge.inverseSection_zeroIdeal
#print axioms LogTwo.Geometry.SectionIdealBridge.inverseSection_zeroIdeal_eq_comap
#print axioms LogTwo.Geometry.SectionIdealBridge.zeroIdeal_pullback
#print axioms LogTwo.Geometry.SectionIdealBridge.zeroIdeal_zero
#print axioms LogTwo.Geometry.SectionIdealBridge.pullback_inverseSection_zeroIdeal
#print axioms LogTwo.Geometry.SectionIdealBridge.pullback_inverseSection_ne_zero
#print axioms LogTwo.Geometry.SectionIdealBridge.zeroIdeal_spec_top
#print axioms LogTwo.Geometry.SectionIdealBridge.divisor_eq_localIdeal_length
#print axioms LogTwo.Geometry.SectionIdealBridge.idealDivisor_apply
#print axioms LogTwo.Geometry.SectionIdealBridge.degree_eq_neg_idealDivisor_sum
#print axioms LogTwo.Geometry.MatrixCompactification.parameterCurveGenericPoint_isDominant
#print axioms LogTwo.Geometry.MatrixCompactification.curveMap_eq_of_generic
#print axioms LogTwo.Geometry.MatrixCompactification.presented_curveIdeal_ne_bot
#print axioms LogTwo.Geometry.MatrixCompactification.presentedDivisor_eq_curveColengthCycle
#print axioms LogTwo.Geometry.MatrixCompactification.euler_degree_eq_neg_curveColengthCycle_sum
#print axioms LogTwo.Geometry.MatrixCompactification.euler_degree_eq_neg_contact_sum
#check LogTwo.Geometry.MatrixCompactification.curveMap_eq_of_generic
#check LogTwo.Geometry.MatrixCompactification.presentedDivisor_eq_curveColengthCycle
#check LogTwo.Geometry.MatrixCompactification.euler_degree_eq_neg_contact_sum

-- Constructed blowup, actual degrees and intrinsic numerical inequality.
#print axioms LogTwo.Geometry.MatrixBlowup.hyperplane_ample
#print axioms LogTwo.Geometry.MatrixBlowup.projection_proper
#print axioms LogTwo.Geometry.MatrixBlowup.structureMap_proper
#print axioms LogTwo.Geometry.MatrixBlowup.space_isIntegral
#print axioms LogTwo.Geometry.MatrixBlowup.space_isLocallyNoetherian
#print axioms LogTwo.Geometry.MatrixBlowup.space_compact
#print axioms LogTwo.Geometry.MatrixBlowup.space_isNoetherian
#print axioms LogTwo.Geometry.MatrixBlowup.exceptional_presents
#print axioms LogTwo.Geometry.MatrixBlowup.isBlowup
#print axioms LogTwo.Geometry.MatrixBlowup.exceptional_degree_eq_neg_contact_sum
#print axioms LogTwo.Geometry.MatrixBlowup.hyperplane_degree_eq_weightedDegree
#print axioms LogTwo.Geometry.MatrixBlowup.curveMap_hyperplane_degree
#print axioms LogTwo.Geometry.MatrixBlowup.A_degree_eq_weightedDegree
#print axioms LogTwo.Geometry.MatrixBlowup.chosenWeights_degree_nonnegative
#print axioms LogTwo.Geometry.MatrixBlowup.logTwo_degree_nonnegative
#check LogTwo.Geometry.MatrixBlowup.exceptional_presents
#check LogTwo.Geometry.MatrixBlowup.exceptional_degree_eq_neg_contact_sum
#check LogTwo.Geometry.MatrixBlowup.A_degree_eq_weightedDegree
#check LogTwo.Geometry.MatrixBlowup.chosenWeights_degree_nonnegative
#check LogTwo.Geometry.MatrixBlowup.logTwo_degree_nonnegative

-- Constructed integral-curve models and actual curve degree transfer.
#print axioms LogTwo.Geometry.MatrixBlowup.exists_ampleExponent
#print axioms LogTwo.Geometry.MatrixBlowup.ampleExponent_gt_one
#print axioms LogTwo.Geometry.MatrixBlowup.H_ample
#print axioms LogTwo.Geometry.MatrixBlowup.Image.center_point_isClosed
#print axioms LogTwo.Geometry.MatrixBlowup.Image.meets_center_complement
#print axioms LogTwo.Geometry.MatrixBlowup.Image.projection_restrict_isIso
#print axioms LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso_generic
#print axioms LogTwo.Geometry.MatrixBlowup.Image.image_meets_chart
#print axioms LogTwo.Geometry.MatrixBlowup.Coordinates.chart_nonempty
#print axioms LogTwo.Geometry.MatrixBlowup.Coordinates.field_properties
#print axioms LogTwo.Geometry.MatrixBlowup.Coordinates.coordinates_generic_map
#print axioms LogTwo.Geometry.MatrixBlowup.CurveModel.existsModelData
#print axioms LogTwo.Geometry.MatrixBlowup.curveDegree_eq_modelDegree
#print axioms LogTwo.Geometry.MatrixBlowup.chosenWeights_integralCurve_degree_nonnegative
#print axioms LogTwo.Geometry.MatrixBlowup.logTwo_integralCurve_degree_nonnegative
#check LogTwo.Geometry.MatrixBlowup.H_ample
#check LogTwo.Geometry.MatrixBlowup.CurveModel.existsModelData
#check LogTwo.Geometry.MatrixBlowup.curveDegree_eq_modelDegree
#check LogTwo.Geometry.MatrixBlowup.logTwo_integralCurve_degree_nonnegative

-- Uniform margin on all integral curves and ampleness of the actual bundle.
#print axioms LogTwo.Geometry.CurveMarginLemmas.curve_degree_laws
#print axioms LogTwo.Geometry.CurveMarginLemmas.marginCoefficient_pos
#print axioms LogTwo.Geometry.CurveMarginLemmas.margin_of_nonnegative_degree
#print axioms LogTwo.Geometry.CurveMarginLemmas.curveDegree_zero_of_frame
#print axioms LogTwo.Geometry.CurveMarginLemmas.margin_of_exceptional_frame
#print axioms LogTwo.Geometry.CurveMarginLemmas.margin_of_avoids_center
#print axioms LogTwo.Geometry.CurveMarginLemmas.margin_of_image_outside_chart
#print axioms LogTwo.Geometry.CurveMarginLemmas.margin_of_contracted
#print axioms LogTwo.Geometry.MatrixBlowup.degreeMargin_pos
#print axioms LogTwo.Geometry.MatrixBlowup.contracted_curve_margin
#print axioms LogTwo.Geometry.MatrixBlowup.outside_chart_curve_margin
#print axioms LogTwo.Geometry.MatrixBlowup.chosenWeights_uniform_curve_margin
#print axioms LogTwo.Geometry.MatrixBlowup.logTwo_exists_positive_uniform_curve_margin
#print axioms LogTwo.Geometry.MatrixBlowup.chosenWeights_interpolationBundle_ample
#print axioms LogTwo.Geometry.MatrixBlowup.logTwo_interpolationBundle_ample
#check LogTwo.Geometry.MatrixBlowup.degreeMargin_pos
#check LogTwo.Geometry.MatrixBlowup.logTwo_exists_positive_uniform_curve_margin
#check LogTwo.Geometry.MatrixBlowup.logTwo_interpolationBundle_ample

-- Actual sheaf jets, bounded sections, varying-center CRT and rational full-row minors.
#print axioms LogTwo.Geometry.MatrixBlowup.blowupBundle_ample_of_interpolationBundle
#print axioms LogTwo.Geometry.MatrixBlowup.chosenWeights_eventual_jetRestriction_surjective
#print axioms LogTwo.Geometry.MatrixBlowup.logTwo_eventual_jetRestriction_surjective
#print axioms LogTwo.Geometry.WeightedAffineFrame.frame_nonempty_of_isoOpen_eq
#print axioms LogTwo.Geometry.WeightedAffineFrame.affineChart_isoOpen
#print axioms LogTwo.Geometry.WeightedAffineFrame.affineFrame_nonempty
#print axioms LogTwo.Geometry.WeightedHomogeneousSubstitution.supportBound_substitution
#print axioms LogTwo.Geometry.WeightedHomogeneousSubstitution.dehomogenize_substitution
#print axioms LogTwo.Geometry.WeightedPullbackDegree.pullback_supportBound
#print axioms LogTwo.Geometry.WeightedGlobalSectionBound.eventual_supportBound
#print axioms LogTwo.Geometry.formalJetAt_packet_surjective
#print axioms LogTwo.Geometry.formalJetAt_packet_eq_of_sub_mem_pow
#print axioms LogTwo.Geometry.formalJetAt_packets_surjective
#print axioms LogTwo.Geometry.formalJetAt_packets_surjective_of_quotient
#print axioms LogTwo.Geometry.MatrixCompactification.frame_exists
#print axioms LogTwo.Geometry.MatrixCompactification.exponent_budget
#print axioms LogTwo.Geometry.MatrixCompactification.eventual_supportBound
#print axioms LogTwo.Geometry.MatrixCompactification.formalPackets_surjective_of_jetRestriction
#print axioms LogTwo.Geometry.MatrixCompactification.logTwo_eventual_fullRowMinor
#print axioms LogTwo.Geometry.MatrixCompactification.logTwo_cofinally_fullRowMinor
#check LogTwo.Geometry.MatrixBlowup.logTwo_eventual_jetRestriction_surjective
#check LogTwo.Geometry.MatrixCompactification.logTwo_eventual_fullRowMinor
#check LogTwo.Geometry.MatrixCompactification.logTwo_cofinally_fullRowMinor

-- Exact actual rational-matrix / nonperiodic analytic rows and Taylor interfaces.
#print axioms LogTwo.Analysis.rowTest_logTwo_exponentialMonomial_eq_coeff
#print axioms LogTwo.Analysis.scaled_periodMonomial_coeff_eq_rowTest
#print axioms LogTwo.Analysis.logTwo_center_radius
#print axioms LogTwo.Analysis.hasSum_logTwo_column_row
#print axioms LogTwo.Analysis.norm_logTwo_rowTest_power_le
#print axioms LogTwo.Analysis.actual_taylor_coefficient_collision
#print axioms LogTwo.Analysis.optionEquivRight_monomial
#print axioms LogTwo.Analysis.optionEquivRight_coeff_coeff
#print axioms LogTwo.Analysis.splitRationalPolynomial_C
#print axioms LogTwo.Analysis.splitRationalPolynomial_X
#print axioms LogTwo.Analysis.splitRationalPolynomial_truncatedLog
#print axioms LogTwo.Analysis.splitRationalPolynomial_columnExpansion
#print axioms LogTwo.Analysis.coefficientMatrix_eq_scaled_entry
#print axioms LogTwo.Analysis.coefficientMatrix_eq_analytic_rows
#print axioms LogTwo.Analysis.actual_minor_analytic_expansion
#print axioms LogTwo.Analysis.actual_minor_support_subset
#print axioms LogTwo.Analysis.actual_minor_analytic_expansion_weighted
#print axioms LogTwo.Analysis.actual_minor_row_hasSum
#check LogTwo.Analysis.coefficientMatrix_eq_scaled_entry
#check LogTwo.Analysis.actual_minor_analytic_expansion_weighted
#check LogTwo.Analysis.actual_minor_row_hasSum

-- Actual-center quantitative collision, logarithmic tails and normalized same-minor bound.
#print axioms LogTwo.Analysis.actual_analytic_summand_exp_bound
#print axioms LogTwo.Analysis.norm_logTwo_center_error_exp
#print axioms LogTwo.Analysis.truncationOrders_analytic_budget
#print axioms LogTwo.Analysis.actual_row_order_le
#print axioms LogTwo.Analysis.norm_actualRowScalar_le
#print axioms LogTwo.Analysis.actualRowScalar_ne_zero_beta_le
#print axioms LogTwo.Analysis.norm_choiceScalar_le
#print axioms LogTwo.Analysis.lowIndexCount_pos
#print axioms LogTwo.Analysis.low_transverse_capacity
#print axioms LogTwo.Analysis.choiceScalar_ne_zero_weight_sum
#print axioms LogTwo.Analysis.norm_analyticSummand_le
#print axioms LogTwo.Analysis.card_minorChoice_le
#print axioms LogTwo.Analysis.actual_minor_complex_det
#print axioms LogTwo.Analysis.actual_minor_log_analytic_bound
#print axioms LogTwo.Analysis.actual_minor_log_bound_of_approximations
#check LogTwo.Analysis.actual_analytic_summand_exp_bound
#check LogTwo.Analysis.norm_choiceScalar_le
#check LogTwo.Analysis.actual_minor_log_bound_of_approximations

-- Counting, remainder decay, same-minor contradiction and unconditional completion.
#print axioms LogTwo.Analysis.fullRowMinor_size_eq_card
#print axioms LogTwo.Analysis.fullRowMinor_size_eq_rowCount
#print axioms LogTwo.Analysis.rowDensity_pos
#print axioms LogTwo.Analysis.lowDensity_pos
#print axioms LogTwo.Analysis.tendsto_rowCount_normalized
#print axioms LogTwo.Analysis.tendsto_lowCount_normalized
#print axioms LogTwo.Analysis.tendsto_collisionRate
#print axioms LogTwo.Analysis.tendsto_analyticRemainder
#print axioms LogTwo.Analysis.combinedAnalyticBudget_eq
#print axioms LogTwo.Analysis.actual_minor_log_bound_with_remainder
#print axioms LogTwo.Analysis.eventual_analytic_errors
#print axioms LogTwo.Analysis.eventual_actual_minor_log_bound
#print axioms LogTwo.Analysis.normalized_bounds_inconsistent
#print axioms LogTwo.Analysis.eventual_no_fullRowMinor
#print axioms LogTwo.Analysis.logTwo_contradiction_of_budgets
#print axioms LogTwo.totalError_le_uniform
#print axioms LogTwo.chosen_collisionLimit_eq
#print axioms LogTwo.exists_dimension_total_budget
#print axioms LogTwo.exists_small_total_parameters
#print axioms LogTwo.not_unbounded_logTwo
#print axioms LogTwo.logTwo_sequentialLowerBound
#print axioms LogTwo.logTwo_eventualLowerBound
#print axioms LogTwo.logTwo_irrational
#print axioms LogTwo.logTwo_exponent_eq_two

-- These exact typed witnesses reject a remaining theorem argument or a changed target.
example : LogTwo.SequentialLowerBound (Real.log 2) := LogTwo.logTwo_sequentialLowerBound
example : OAI.PiExponent.irrationalityExponent (Real.log 2) = 2 := LogTwo.logTwo_exponent_eq_two
-- The comparison definition uses a real sSup, so also check boundedness and
-- the Dirichlet exponent directly; this avoids relying on sSup of an unbounded set.
example : BddAbove (OAI.PiExponent.ApproximationExponents (Real.log 2)) := by
  refine ⟨2, ?_⟩
  intro ν hν
  by_contra h
  exact (OAI.PiExponent.finite_goodRationalApproximations_of_eventualLowerBound
    LogTwo.logTwo_eventualLowerBound (by linarith : 2 < ν)).not_infinite hν.2
example : (2 : ℝ) ∈ OAI.PiExponent.ApproximationExponents (Real.log 2) :=
  OAI.PiExponent.two_mem_approximationExponents LogTwo.logTwo_irrational
#check LogTwo.logTwo_exponent_eq_two
#check LogTwo.logTwo_sequentialLowerBound
#check LogTwo.exists_small_total_parameters

-- Final public target is stated with this project's independent definition.
#print axioms LogTwo.approximationExponents_eq_comparison
#print axioms LogTwo.log_two_approximationExponents_bddAbove
#print axioms LogTwo.two_mem_log_two_approximationExponents
example : LogTwo.irrationalityExponent (Real.log 2) = 2 :=
  LogTwo.irrationalityExponent_log_two
example : BddAbove ({μ : ℝ | 0 < μ ∧ Set.Infinite
      {r : ℚ | 1 < r.den ∧ 0 < |Real.log 2 - (r : ℝ)| ∧
        |Real.log 2 - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}}) :=
  LogTwo.log_two_approximationExponents_bddAbove
example : (2 : ℝ) ∈ {μ : ℝ | 0 < μ ∧ Set.Infinite
      {r : ℚ | 1 < r.den ∧ 0 < |Real.log 2 - (r : ℝ)| ∧
        |Real.log 2 - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}} :=
  LogTwo.two_mem_log_two_approximationExponents
#print axioms LogTwo.irrationalityExponent_log_two
