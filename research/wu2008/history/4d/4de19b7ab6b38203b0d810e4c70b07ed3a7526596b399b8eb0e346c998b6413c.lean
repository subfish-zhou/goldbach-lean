import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableEndpoint

set_option pp.maxSteps 1000000

#check Wu2008DoubleSieve.truncatedSixthTable_B_continuous
#print axioms Wu2008DoubleSieve.truncatedSixthTable_B_continuous
#check Wu2008DoubleSieve.truncatedSixthTable_B_bound
#print axioms Wu2008DoubleSieve.truncatedSixthTable_B_bound
#check Wu2008DoubleSieve.truncatedSixthTableRegular
#print axioms Wu2008DoubleSieve.truncatedSixthTableRegular
#check Wu2008DoubleSieve.truncatedSixthTable_regular_continuous
#print axioms Wu2008DoubleSieve.truncatedSixthTable_regular_continuous
#check Wu2008DoubleSieve.truncatedSixthTable_regular_eq
#print axioms Wu2008DoubleSieve.truncatedSixthTable_regular_eq
#check Wu2008DoubleSieve.truncatedSixthTable_regular_nonneg
#print axioms Wu2008DoubleSieve.truncatedSixthTable_regular_nonneg
#check Wu2008DoubleSieve.truncatedSixthTable_regular_bound
#print axioms Wu2008DoubleSieve.truncatedSixthTable_regular_bound
#check Wu2008DoubleSieve.truncatedSixthTableBeta
#print axioms Wu2008DoubleSieve.truncatedSixthTableBeta
#check Wu2008DoubleSieve.truncatedSixthTableKernel
#print axioms Wu2008DoubleSieve.truncatedSixthTableKernel
#check Wu2008DoubleSieve.truncatedSixthTableRectangle
#print axioms Wu2008DoubleSieve.truncatedSixthTableRectangle
#check Wu2008DoubleSieve.truncatedSixthTable_kernel_measurable
#print axioms Wu2008DoubleSieve.truncatedSixthTable_kernel_measurable
#check Wu2008DoubleSieve.truncatedSixthTable_kernel_nonneg
#print axioms Wu2008DoubleSieve.truncatedSixthTable_kernel_nonneg
#check Wu2008DoubleSieve.truncatedSixthTable_kernel_support
#print axioms Wu2008DoubleSieve.truncatedSixthTable_kernel_support
#check Wu2008DoubleSieve.truncatedSixthTable_kernel_dominator
#print axioms Wu2008DoubleSieve.truncatedSixthTable_kernel_dominator
#check Wu2008DoubleSieve.truncatedSixthTable_kernel_integrable
#print axioms Wu2008DoubleSieve.truncatedSixthTable_kernel_integrable
#check Wu2008DoubleSieve.truncatedSixthTable_kernel_literal
#print axioms Wu2008DoubleSieve.truncatedSixthTable_kernel_literal
#check Wu2008DoubleSieve.truncatedSixthTable_beta_integral
#print axioms Wu2008DoubleSieve.truncatedSixthTable_beta_integral
#check Wu2008DoubleSieve.truncatedSixthTable_beta_nonneg
#print axioms Wu2008DoubleSieve.truncatedSixthTable_beta_nonneg
#check Wu2008DoubleSieve.truncatedSixthTable_kernel_actual_le
#print axioms Wu2008DoubleSieve.truncatedSixthTable_kernel_actual_le
#check Wu2008DoubleSieve.truncatedSixthTable_actual_gain_le
#print axioms Wu2008DoubleSieve.truncatedSixthTable_actual_gain_le
#check Wu2008DoubleSieve.truncatedSixthTable_fixed_delta_count
#print axioms Wu2008DoubleSieve.truncatedSixthTable_fixed_delta_count
#check Wu2008DoubleSieve.truncatedSixthTable_classical_count
#print axioms Wu2008DoubleSieve.truncatedSixthTable_classical_count
#check Wu2008DoubleSieve.truncatedSixthTable_cut_stable
#print axioms Wu2008DoubleSieve.truncatedSixthTable_cut_stable
#check Wu2008DoubleSieve.truncatedSixthTable_boundaries_null
#print axioms Wu2008DoubleSieve.truncatedSixthTable_boundaries_null
#check Wu2008DoubleSieve.truncatedSixthTable_region_stable
#print axioms Wu2008DoubleSieve.truncatedSixthTable_region_stable
#check Wu2008DoubleSieve.truncatedSixthTable_kernel_ae_limit
#print axioms Wu2008DoubleSieve.truncatedSixthTable_kernel_ae_limit
#check Wu2008DoubleSieve.truncatedSixthTable_beta_right_limit
#print axioms Wu2008DoubleSieve.truncatedSixthTable_beta_right_limit
#check Wu2008DoubleSieve.truncatedSixthTable_beta_close
#print axioms Wu2008DoubleSieve.truncatedSixthTable_beta_close
#check Wu2008DoubleSieve.truncatedSixthTable_actual_vector_bounds
#print axioms Wu2008DoubleSieve.truncatedSixthTable_actual_vector_bounds
#check Wu2008DoubleSieve.truncatedSixthTable_coefficient_payment
#print axioms Wu2008DoubleSieve.truncatedSixthTable_coefficient_payment
#check Wu2008DoubleSieve.truncatedSixthTable_actual_count
#print axioms Wu2008DoubleSieve.truncatedSixthTable_actual_count
#check Wu2008DoubleSieve.truncatedSixthTable_certified_seed_count
#print axioms Wu2008DoubleSieve.truncatedSixthTable_certified_seed_count

#print Wu2008DoubleSieve.truncatedSixthTable_beta_integral
#print Wu2008DoubleSieve.truncatedSixthTable_kernel_actual_le
#print Wu2008DoubleSieve.truncatedSixthTable_actual_gain_le
#print Wu2008DoubleSieve.truncatedSixthTable_fixed_delta_count
#print Wu2008DoubleSieve.truncatedSixthTable_classical_count
#print Wu2008DoubleSieve.truncatedSixthTable_beta_right_limit
#print Wu2008DoubleSieve.truncatedSixthTable_coefficient_payment
#print Wu2008DoubleSieve.truncatedSixthTable_actual_count

run_cmd do
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableContinuous,
    `MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableIntegral,
    `MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableComparison,
    `MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableCount,
    `MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableBoundary,
    `MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableLimit,
    `MathlibNt.Wu2008DoubleSieve.TruncatedSixthTablePayment,
    `MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableEndpoint]
  let env ← Lean.getEnv
  let mut seen : Array Lean.Name := #[]
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if modules.contains modName then
      let data := env.header.moduleData[idx]!
      for k in [:data.constNames.size] do
        let name := data.constNames[k]!
        Lean.logInfo m!"MODULE-MEMBER {modName} {name}"
        unless seen.contains name do
          let info := data.constants[k]!
          Lean.logInfo m!"COMPILED-TYPE {name} : {info.type}"
          let axioms ← Lean.collectAxioms name
          Lean.logInfo m!"COMPILED-AXIOMS {name} : {axioms}"
          unless axioms.all (fun a =>
              a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
            throwError "Nonstandard axiom in {name}"
          seen := seen.push name
  Lean.logInfo m!"COMPILED-COUNT {seen.size}"
