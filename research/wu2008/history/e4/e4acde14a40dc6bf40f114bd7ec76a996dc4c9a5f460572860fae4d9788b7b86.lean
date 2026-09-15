import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedUpper

set_option pp.maxSteps 1000000
set_option pp.deepTerms true
set_option pp.proofs true

#print Wu2008DoubleSieve.fourthRowTripleGated_ceil_gate
#print Wu2008DoubleSieve.fourthRowTripleGated_fibre_profile
#print Wu2008DoubleSieve.fourthRowTripleGated_geometry
#print Wu2008DoubleSieve.fourthRowTripleGated_AP_profile
#print Wu2008DoubleSieve.fourthRowTripleGated_output_test
#print Wu2008DoubleSieve.fourthRowTripleGated_remainder
#print Wu2008DoubleSieve.fourthRowTripleGated_upper_finite
#print Wu2008DoubleSieve.fourthRowTripleGated_original_sum
#print Wu2008DoubleSieve.fourthRowTripleGated_switched_reorder
#print Wu2008DoubleSieve.fourthRowTripleGated_switching_finite
#print Wu2008DoubleSieve.fourthRowTripleGated_R1_layers
#print Wu2008DoubleSieve.fourthRowTripleGated_R1_log
#print Wu2008DoubleSieve.fourthRowTripleGated_R2_relative
#print Wu2008DoubleSieve.fourthRowTripleGated_upper_density
#print Wu2008DoubleSieve.fourthRowTripleGated_X_reorder
#print Wu2008DoubleSieve.fourthRowTripleGated_X_buchstab
#print Wu2008DoubleSieve.fourthRowTripleGated_integrable
#print Wu2008DoubleSieve.fourthRowTripleGated_integral_bounds
#print Wu2008DoubleSieve.fourthRowTripleGated_quadrature
#print Wu2008DoubleSieve.fourthRowTripleGated_prime_mass
#print Wu2008DoubleSieve.fourthRowTripleGated_source_quadrature
#print Wu2008DoubleSieve.fourthRowTripleGated_X_main
#print Wu2008DoubleSieve.fourthRowTripleGated_integral_scaled
#print Wu2008DoubleSieve.fourthRowTripleGated_X_scaled
#print Wu2008DoubleSieve.fourthRowTripleGated_prefix_upper
#print Wu2008DoubleSieve.fourthRowTripleGated_gamma10_upper
#print Wu2008DoubleSieve.fourthRowTripleGated_gamma13_upper
#print Wu2008DoubleSieve.fourthRowTripleGated_joint_upper
#print Wu2008DoubleSieve.fourthRowTripleGated_natural_card
#print Wu2008DoubleSieve.fourthRowTripleGated_natural_card_upper
#print Wu2008DoubleSieve.omega3_balanced_interval_distribution
#print Wu2008DoubleSieve.sum_omega3ProfileError_eq_primeCenteredAPSum_sub
#print Wu2004MeanValue.primeCenteredAPSum_eq_actual_sub_principal
#print Wu2004MeanValue.balanced_common_profile_primeCentered_natural

run_cmd do
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedProfiles,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedFamily,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedCounts,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedSwitching,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedDistribution,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedSieve,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedIntegral,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedQuadrature,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedRough,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedPrimeMass,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedMain,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedNormalization,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedUpper]
  let env ← Lean.getEnv
  let mut seen : Array Lean.Name := #[]
  let mut found : Array Lean.Name := #[]
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if modules.contains modName then
      found := found.push modName
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
  unless found.size == modules.size do
    throwError "Missing gated mathematical modules: found {found.size} of {modules.size}"
  Lean.logInfo m!"COMPILED-MODULE-COUNT {found.size}"
  Lean.logInfo m!"COMPILED-COUNT {seen.size}"
