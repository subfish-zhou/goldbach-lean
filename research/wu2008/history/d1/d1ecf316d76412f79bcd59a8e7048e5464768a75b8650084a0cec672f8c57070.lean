import MathlibNt.Wu2008DoubleSieve.TableGainComposition

set_option pp.maxSteps 1000000

#check Wu2008DoubleSieve.tableGainKernel
#print axioms Wu2008DoubleSieve.tableGainKernel
#check Wu2008DoubleSieve.tableGainKernel_nonneg
#print axioms Wu2008DoubleSieve.tableGainKernel_nonneg
#check Wu2008DoubleSieve.tableGainKernel_tail_continuousOn
#print axioms Wu2008DoubleSieve.tableGainKernel_tail_continuousOn
#check Wu2008DoubleSieve.tableGainKernel_mul_intervalIntegrable
#print axioms Wu2008DoubleSieve.tableGainKernel_mul_intervalIntegrable
#check Wu2008DoubleSieve.tableGainKernel_intervalIntegrable
#print axioms Wu2008DoubleSieve.tableGainKernel_intervalIntegrable
#check Wu2008DoubleSieve.tableGainKernel_actual_intervalIntegrable
#print axioms Wu2008DoubleSieve.tableGainKernel_actual_intervalIntegrable
#check Wu2008DoubleSieve.tableGainL
#print axioms Wu2008DoubleSieve.tableGainL
#check Wu2008DoubleSieve.tableGainL_nonneg
#print axioms Wu2008DoubleSieve.tableGainL_nonneg
#check Wu2008DoubleSieve.tableGain_actual_upper_tail
#print axioms Wu2008DoubleSieve.tableGain_actual_upper_tail
#check Wu2008DoubleSieve.tableGainKernel_five
#print axioms Wu2008DoubleSieve.tableGainKernel_five
#check Wu2008DoubleSieve.tableGainL_five
#print axioms Wu2008DoubleSieve.tableGainL_five
#check Wu2008DoubleSieve.tableGainR_last
#print axioms Wu2008DoubleSieve.tableGainR_last
#check Wu2008DoubleSieve.tableGainR_bounds
#print axioms Wu2008DoubleSieve.tableGainR_bounds
#check Wu2008DoubleSieve.tableGainR_tail_bounds
#print axioms Wu2008DoubleSieve.tableGainR_tail_bounds
#check Wu2008DoubleSieve.tableGainE
#print axioms Wu2008DoubleSieve.tableGainE
#check Wu2008DoubleSieve.tableGainE_nonneg
#print axioms Wu2008DoubleSieve.tableGainE_nonneg
#check Wu2008DoubleSieve.tableGain_actual_upper_endpoints
#print axioms Wu2008DoubleSieve.tableGain_actual_upper_endpoints
#check Wu2008DoubleSieve.tableGainClip
#print axioms Wu2008DoubleSieve.tableGainClip
#check Wu2008DoubleSieve.tableGainWeight
#print axioms Wu2008DoubleSieve.tableGainWeight
#check Wu2008DoubleSieve.tableGainClip_monotone
#print axioms Wu2008DoubleSieve.tableGainClip_monotone
#check Wu2008DoubleSieve.tableGainClip_pos
#print axioms Wu2008DoubleSieve.tableGainClip_pos
#check Wu2008DoubleSieve.tableGainClip_first
#print axioms Wu2008DoubleSieve.tableGainClip_first
#check Wu2008DoubleSieve.tableGainClip_last
#print axioms Wu2008DoubleSieve.tableGainClip_last
#check Wu2008DoubleSieve.tableGainClip_bounds
#print axioms Wu2008DoubleSieve.tableGainClip_bounds
#check Wu2008DoubleSieve.tableGainClip_cell_subset
#print axioms Wu2008DoubleSieve.tableGainClip_cell_subset
#check Wu2008DoubleSieve.tableGainWeight_nonneg
#print axioms Wu2008DoubleSieve.tableGainWeight_nonneg
#check Wu2008DoubleSieve.tableGainClip_collapse
#print axioms Wu2008DoubleSieve.tableGainClip_collapse
#check Wu2008DoubleSieve.tableGainWeight_collapse
#print axioms Wu2008DoubleSieve.tableGainWeight_collapse
#check Wu2008DoubleSieve.tableGainClip_reciprocal_intervalIntegrable
#print axioms Wu2008DoubleSieve.tableGainClip_reciprocal_intervalIntegrable
#check Wu2008DoubleSieve.tableGainWeight_integral
#print axioms Wu2008DoubleSieve.tableGainWeight_integral
#check Wu2008DoubleSieve.tableGain_actual_lower_cell
#print axioms Wu2008DoubleSieve.tableGain_actual_lower_cell
#check Wu2008DoubleSieve.tableGain_actual_lower_integral
#print axioms Wu2008DoubleSieve.tableGain_actual_lower_integral
#check Wu2008DoubleSieve.tableGain_actual_clipped_lower
#print axioms Wu2008DoubleSieve.tableGain_actual_clipped_lower
#check Wu2008DoubleSieve.tableGainWeight_six
#print axioms Wu2008DoubleSieve.tableGainWeight_six
#check Wu2008DoubleSieve.tableGainB
#print axioms Wu2008DoubleSieve.tableGainB
#check Wu2008DoubleSieve.tableGainB_nonneg
#print axioms Wu2008DoubleSieve.tableGainB_nonneg
#check Wu2008DoubleSieve.tableGainB_composition
#print axioms Wu2008DoubleSieve.tableGainB_composition
#check Wu2008DoubleSieve.tableGain_actual_lower
#print axioms Wu2008DoubleSieve.tableGain_actual_lower
#check Wu2008DoubleSieve.tableGain_certified_seed_lower
#print axioms Wu2008DoubleSieve.tableGain_certified_seed_lower
#check Wu2008DoubleSieve.tableGainB_six
#print axioms Wu2008DoubleSieve.tableGainB_six

#print Wu2008DoubleSieve.tableGain_actual_upper_tail
#print Wu2008DoubleSieve.tableGain_actual_upper_endpoints
#print Wu2008DoubleSieve.tableGain_actual_lower_cell
#print Wu2008DoubleSieve.tableGain_actual_lower_integral
#print Wu2008DoubleSieve.tableGain_actual_clipped_lower
#print Wu2008DoubleSieve.tableGain_actual_lower

run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if modName.toString.startsWith "MathlibNt.Wu2008DoubleSieve.TableGain" then
      for name in env.header.moduleData[idx]!.constNames do
        let info ← Lean.getConstInfo name
        Lean.logInfo m!"COMPILED-TYPE {name} : {info.type}"
        let axioms ← Lean.collectAxioms name
        Lean.logInfo m!"COMPILED-AXIOMS {name} : {axioms}"
        unless axioms.all (fun a =>
            a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "Nonstandard axiom in {name}"
        count := count + 1
  Lean.logInfo m!"COMPILED-COUNT {count}"
