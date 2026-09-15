import MathlibNt.Wu2008DoubleSieve.Gamma16FourthRow

set_option pp.maxSteps 1000000
set_option pp.deepTerms true
set_option pp.proofs true

#check Wu2008DoubleSieve.gamma16_directed_sums
#check Wu2008DoubleSieve.gamma16_forced_small_primes
#check Wu2008DoubleSieve.gamma16_raw_natural_card
#check Wu2008DoubleSieve.gamma16_switch_profile_mem
#check Wu2008DoubleSieve.gamma16_weighted_fibre_le
#check Wu2008DoubleSieve.gamma16_prefix_finite_switching
#check Wu2008DoubleSieve.gamma16_prefix_switching_paid
#check Wu2008DoubleSieve.gamma16_family_remainder
#check Wu2008DoubleSieve.gamma16_family_upper_finite
#check Wu2008DoubleSieve.gamma16_R1_log_saving
#check Wu2008DoubleSieve.gamma16_R2_relative
#check Wu2008DoubleSieve.gamma16_prefix_upper_density
#check Wu2008DoubleSieve.gamma16_X_le_rough_repeated
#check Wu2008DoubleSieve.gamma16_source_argument
#check Wu2008DoubleSieve.gamma16_buchstab_uniform
#check Wu2008DoubleSieve.gamma16_literal_fibres_integrable
#check Wu2008DoubleSieve.gamma16_exponent_region_fibres
#check Wu2008DoubleSieve.gamma16_fourth_integral_eq_outer
#check Wu2008DoubleSieve.gamma16_fourth_image_nonempty
#check Wu2008DoubleSieve.gamma16_fourth_image_bddAbove
#check Wu2008DoubleSieve.gamma16_fourth_envelope_bounds
#check Wu2008DoubleSieve.gamma16_fourfold_prime_quadrature
#check Wu2008DoubleSieve.gamma16_X_main
#check Wu2008DoubleSieve.gamma16_integral_scaled
#check Wu2008DoubleSieve.gamma16_fourth_row_prefix_upper
#check Wu2008DoubleSieve.gamma16_fourth_row_quotient_upper
#check Wu2008DoubleSieve.gamma16_fourth_row_raw_upper
#check Wu2008DoubleSieve.gamma16_fourth_row_raw_card_upper

#print Wu2008DoubleSieve.gamma16_family_upper_finite
#print Wu2008DoubleSieve.gamma16_R1_log_saving
#print Wu2008DoubleSieve.gamma16_R2_relative
#print Wu2008DoubleSieve.gamma16_prefix_upper_density
#print Wu2008DoubleSieve.gamma16_fourfold_prime_quadrature
#print Wu2008DoubleSieve.gamma16_mass_fibre_main
#print Wu2008DoubleSieve.gamma16_X_main
#print Wu2008DoubleSieve.gamma16_integral_scaled
#print Wu2008DoubleSieve.gamma16_fourth_row_prefix_upper

run_cmd do
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.Gamma16Carriers,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Profiles,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Quotient,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Multiplicity,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Geometry,
    `MathlibNt.Wu2008DoubleSieve.Gamma16FiniteSwitching,
    `MathlibNt.Wu2008DoubleSieve.Gamma16SwitchingPayment,
    `MathlibNt.Wu2008DoubleSieve.Gamma16SieveFamily,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Layers,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Distribution,
    `MathlibNt.Wu2008DoubleSieve.Gamma16MissingMass,
    `MathlibNt.Wu2008DoubleSieve.Gamma16SievePayment,
    `MathlibNt.Wu2008DoubleSieve.Gamma16MassCarrier,
    `MathlibNt.Wu2008DoubleSieve.Gamma16MassReorder,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Kernel,
    `MathlibNt.Wu2008DoubleSieve.Gamma16IntegralRegular,
    `MathlibNt.Wu2008DoubleSieve.Gamma16IntegralEnvelope,
    `MathlibNt.Wu2008DoubleSieve.Gamma16IntegralIntegrability,
    `MathlibNt.Wu2008DoubleSieve.Gamma16MassCoordinates,
    `MathlibNt.Wu2008DoubleSieve.Gamma16MassGeometry,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Quadrature,
    `MathlibNt.Wu2008DoubleSieve.Gamma16MassErrors,
    `MathlibNt.Wu2008DoubleSieve.Gamma16MainMass,
    `MathlibNt.Wu2008DoubleSieve.Gamma16Normalization,
    `MathlibNt.Wu2008DoubleSieve.Gamma16FourthRow]
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
    throwError "Missing Gamma16 mathematical modules: found {found.size} of {modules.size}"
  Lean.logInfo m!"COMPILED-MODULE-COUNT {found.size}"
  Lean.logInfo m!"COMPILED-COUNT {seen.size}"
