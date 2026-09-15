import MathlibNt.Wu2008DoubleSieve.Gamma5GainMain

/-!
# Complete actual module-membership evidence

All stored members are checked, including generated constants whose names
do not start with Gamma5Gain. This command-only module adds no declarations.
-/

set_option pp.fullNames true
set_option pp.universes true

open Lean Elab Term

run_elab do
  let env ← getEnv
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainKernel,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainIntegral,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainCell,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainGeometry,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainGrid,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainAdmission,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainPacking,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainRectangleIntegral,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainMass,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainApproximation,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainSufficiency,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainAssembly,
    `MathlibNt.Wu2008DoubleSieve.Gamma5GainMain]
  let mut total := 0
  for modName in modules do
    let some idx := env.getModuleIdx? modName
      | throwError "Missing module: {modName}"
    let names := env.header.moduleData[idx.toNat]!.constNames
    logInfo (Json.mkObj [
      ("module", toJson modName.toString),
      ("constNames_count", toJson names.size)]).compress
    for name in names do
      let some ci := env.checked.get.find? name
        | throwError "Missing module member: {name}"
      if let .axiomInfo _ := ci then
        throwError "New axiom declaration: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Nonstandard axiom: {name}: {ax}"
      let type ← Meta.ppExpr ci.type
      logInfo (Json.mkObj [
        ("module", toJson modName.toString),
        ("name", toJson name.toString),
        ("type", toJson type.pretty),
        ("axioms", toJson (axioms.map Name.toString))]).compress
      total := total + 1
  let own ← mkModuleData env
  unless own.constNames.isEmpty do
    throwError "Command-only audit unexpectedly introduced declarations: {own.constNames}"
  logInfo (Json.mkObj [
    ("module", toJson env.mainModule.toString),
    ("constNames_count", toJson own.constNames.size)]).compress
  logInfo (Json.mkObj [("complete_module_member_total", toJson total)]).compress

open Wu2008DoubleSieve

#print gamma5GainIntegral
#print gamma5GainLiteral
#print gamma5GainLegal
#print gamma5GainV
#print gamma5GainInner
#print gamma5GainPacking
#print gamma5GainCell
#print gamma5ClassicalLabels
#print gamma5ClassicalCount
#print gamma5ClassicalMainMass
#print gamma5MassC5
#print boxTheta
#print AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral

#check @gamma5Gain_integral_bounds
#check @gamma5Gain_inner_integrable
#check @gamma5Gain_outer_integrable
#check @gamma5Gain_sorted_two
#check @gamma5Gain_cell_count_le_phi
#check @gamma5Gain_cell_theta
#check @gamma5Gain_grid_comparison
#check @gamma5Gain_sufficient_family
#check @gamma5Gain_approx_le_kernel
#check @gamma5Gain_inner_packings_disjoint
#check @gamma5Gain_packing_mass
#check @gamma5Gain_main_mass_partition
#check @gamma5Gain_full_count_upper
#check @gamma5Gain_full_count_literal
#check @gamma5Mass_rectangle_mass
#check @gamma5Mass_full_mass
#check @gamma5Classical_mask_upper
#check @wuImprovementLimit_sub_mem

#print axioms gamma5Gain_full_count_upper
#print axioms gamma5Gain_full_count_literal
#print axioms gamma5Gain_integral_bounds
#print axioms gamma5Gain_sufficient_family
#print axioms gamma5Gain_packing_mass
#print axioms gamma5Gain_main_mass_partition
