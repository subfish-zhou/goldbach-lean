import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateUpper

set_option pp.maxSteps 1000000
set_option pp.deepTerms true
set_option pp.proofs true

#print Wu2008DoubleSieve.fourthRowTripleNoGate_original_sum
#print Wu2008DoubleSieve.fourthRowTripleNoGate_switched_reorder
#print Wu2008DoubleSieve.fourthRowTripleNoGate_switching_finite
#print Wu2008DoubleSieve.fourthRowTripleNoGate_R1_log
#print Wu2008DoubleSieve.fourthRowTripleNoGate_R2_relative
#print Wu2008DoubleSieve.fourthRowTripleNoGate_upper_density
#print Wu2008DoubleSieve.fourthRowTripleNoGate_X_reorder
#print Wu2008DoubleSieve.fourthRowTripleNoGate_X_buchstab
#print Wu2008DoubleSieve.fourthRowTripleNoGate_quadrature
#print Wu2008DoubleSieve.fourthRowTripleNoGate_prime_mass
#print Wu2008DoubleSieve.fourthRowTripleNoGate_source_quadrature
#print Wu2008DoubleSieve.fourthRowTripleNoGate_X_main
#print Wu2008DoubleSieve.fourthRowTripleNoGate_integral_scaled
#print Wu2008DoubleSieve.fourthRowTripleNoGate_prefix_upper
#print Wu2008DoubleSieve.fourthRowTripleNoGate_joint_upper
#print Wu2008DoubleSieve.fourthRowTripleNoGate_natural_card

run_cmd do
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateProfiles,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateSwitching,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateLayers,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateDistribution,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateSieve,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateIntegral,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateQuadrature,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateRough,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGatePrimeMass,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateMain,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateNormalization,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateCounts,
    `MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateUpper]
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
    throwError "Missing no-gate mathematical modules: found {found.size} of {modules.size}"
  Lean.logInfo m!"COMPILED-MODULE-COUNT {found.size}"
  Lean.logInfo m!"COMPILED-COUNT {seen.size}"
