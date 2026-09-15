import MathlibNt.Wu2008DoubleSieve.FourthRowMotherSource

set_option pp.maxSteps 1000000
set_option pp.deepTerms true
set_option pp.proofs true

#check Wu2008DoubleSieve.fourthRowMother_prefix_card
#check Wu2008DoubleSieve.fourthRowMother_coloured_card
#check Wu2008DoubleSieve.fourthRowMother_band_formulas
#check Wu2008DoubleSieve.fourthRowMother_scalar
#check Wu2008DoubleSieve.fourthRowMother_mem_quadruple
#check Wu2008DoubleSieve.fourthRowMother_first_two_exact_card
#check Wu2008DoubleSieve.fourthRowMother_low_pairs_card
#check Wu2008DoubleSieve.fourthRowMother_cross_pairs_card
#check Wu2008DoubleSieve.fourthRowMother_label_weight_eq
#check Wu2008DoubleSieve.fourthRowMother_fixed_carrier
#check Wu2008DoubleSieve.fourthRowMother_pair_carrier
#check Wu2008DoubleSieve.fourthRowMother_triple_carrier
#check Wu2008DoubleSieve.fourthRowMother_quadruple_carrier
#check Wu2008DoubleSieve.fourthRowMother_prefix_mass
#check Wu2008DoubleSieve.fourthRowMother_gamma5_mass
#check Wu2008DoubleSieve.fourthRowMother_gamma6_mass
#check Wu2008DoubleSieve.fourthRowMother_gamma9_mass
#check Wu2008DoubleSieve.fourthRowMother_gamma16_output_bounds
#check Wu2008DoubleSieve.fourthRowMother_gamma16_mass
#check Wu2008DoubleSieve.fourthRowMother_masked_identity
#check Wu2008DoubleSieve.fourthRowMother_masked
#check Wu2008DoubleSieve.fourthRowMother_negative_split
#check Wu2008DoubleSieve.fourthRowMother_original_windows
#check Wu2008DoubleSieve.fourthRowMother_bad_prime_is_badD
#check Wu2008DoubleSieve.fourthRowMother_single_floor
#check Wu2008DoubleSieve.fourthRowMother_bad_prime_floor
#check Wu2008DoubleSieve.fourthRowMother_error_power
#check Wu2008DoubleSieve.fourthRowMother_error_relative
#check Wu2008DoubleSieve.fourthRowMother_weighted_identity
#check Wu2008DoubleSieve.fourthRowMother_source_finite
#check Wu2008DoubleSieve.fourthRowMother_source

#print Wu2008DoubleSieve.fourthRowMother_coloured_card
#print Wu2008DoubleSieve.fourthRowMother_mem_quadruple
#print Wu2008DoubleSieve.fourthRowMother_label_weight_eq
#print Wu2008DoubleSieve.fourthRowMother_quadruple_carrier
#print Wu2008DoubleSieve.fourthRowMother_prefix_mass
#print Wu2008DoubleSieve.fourthRowMother_gamma16_mass
#print Wu2008DoubleSieve.fourthRowMother_masked_identity
#print Wu2008DoubleSieve.fourthRowMother_original_windows
#print Wu2008DoubleSieve.fourthRowMother_single_floor
#print Wu2008DoubleSieve.fourthRowMother_bad_prime_floor
#print Wu2008DoubleSieve.fourthRowMother_error_power
#print Wu2008DoubleSieve.fourthRowMother_error_relative
#print Wu2008DoubleSieve.fourthRowMother_weighted_identity
#print Wu2008DoubleSieve.fourthRowMother_source_finite
#print Wu2008DoubleSieve.fourthRowMother_source

run_cmd do
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherLists,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherColourCounts,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherBandFormulas,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherPrefixMembers,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherCarriers,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherFourBridge,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherBandLabels,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherBadPrime,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherPairTriple,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherPrefixMass,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherPayment,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherSourceBands,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherPairMass,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherNine,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherMasked,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherOriginalWindows,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherGamma16,
    `MathlibNt.Wu2008DoubleSieve.FourthRowMotherSource]
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
    throwError "Missing FourthRowMother mathematical modules: found {found.size} of {modules.size}"
  Lean.logInfo m!"COMPILED-MODULE-COUNT {found.size}"
  Lean.logInfo m!"COMPILED-COUNT {seen.size}"
