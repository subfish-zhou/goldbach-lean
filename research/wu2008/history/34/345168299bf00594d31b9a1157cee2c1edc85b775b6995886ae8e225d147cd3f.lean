import MathlibNt.Wu2008DoubleSieve.Gamma6GainMain
import Lean.Util.FoldConsts

/-! # Complete stored-member type, dependency and axiom-cone census -/

set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

open Lean Elab Term

run_elab do
  let env ← getEnv
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.Gamma6GainGeometry,
    `MathlibNt.Wu2008DoubleSieve.Gamma6GainCell,
    `MathlibNt.Wu2008DoubleSieve.Gamma6GainPacking,
    `MathlibNt.Wu2008DoubleSieve.Gamma6GainIntegral,
    `MathlibNt.Wu2008DoubleSieve.Gamma6GainMass,
    `MathlibNt.Wu2008DoubleSieve.Gamma6GainApproximation,
    `MathlibNt.Wu2008DoubleSieve.Gamma6GainSufficiency,
    `MathlibNt.Wu2008DoubleSieve.Gamma6GainMain]
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
      let mut deps : Array String := #[]
      for dep in ci.getUsedConstantsAsSet do
        deps := deps.push dep.toString
      logInfo (Json.mkObj [
        ("module", toJson modName.toString),
        ("name", toJson name.toString),
        ("type", toJson type.pretty),
        ("direct_dependencies", toJson deps),
        ("axioms", toJson (axioms.map Name.toString))]).compress
      total := total + 1
  let own ← mkModuleData env
  unless own.constNames.isEmpty do
    throwError "Command-only audit unexpectedly introduced declarations: {own.constNames}"
  logInfo (Json.mkObj [
    ("module", toJson env.mainModule.toString),
    ("constNames_count", toJson own.constNames.size)]).compress
  logInfo (Json.mkObj [("complete_module_member_total", toJson total)]).compress

set_option pp.explicit false
set_option pp.proofs false

open Wu2008DoubleSieve

#print gamma6GainIntegral
#print gamma6GainLiteral
#print gamma6GainRegion
#print gamma6GainInner
#print gamma6GainInnerRectangle
#print gamma6GainPacking
#print gamma6BaseLabels
#print gamma6BaseRectLabels
#print gamma6BaseC6
#print gamma6BaseIntegral
#print gamma5ClassicalCount
#print gamma5ClassicalMainMass
#print gamma5ClassicalProduct
#print sourceSieveCount
#print sourceSieveCarrier
#print boxTheta
#print gamma5MassAtom
#print gamma5GainSmooth
#print gamma5GainSample
#print AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral

#check @gamma6Gain_domain_bounds
#check @gamma6Gain_endpoint_admission
#check @gamma6Gain_coarse_label
#check @gamma6Gain_grid_comparison
#check @gamma6Gain_packing_actual
#check @gamma6Gain_packing_mass
#check @gamma6Gain_inner_integrable
#check @gamma6Gain_outer_integrable
#check @gamma6Gain_integral_bounds
#check @gamma6Gain_approx_integral_tendsto
#check @gamma6Gain_sufficient_family
#check @gamma6Gain_inner_packings_disjoint
#check @gamma6Gain_full_count_upper
#check @gamma6Gain_integral_literal
#check @gamma6Gain_full_count_literal
#check @gamma6Base_count_eq_nat
#check @gamma6Base_mask_upper
#check @gamma6Base_rectangle_mass
#check @gamma6Base_full_mass
#check @gamma5Gain_sorted_two
#check @gamma5Gain_cell_theta
#check @gamma5Gain_H_pullback_ae
#check @wuImprovementLimit_sub_mem
#check @gamma5Gain_count_partition
#check @gamma5Gain_main_mass_partition
#check @gamma5Gain_weighted_transport

#print axioms gamma6Gain_grid_comparison
#print axioms gamma6Gain_packing_mass
#print axioms gamma6Gain_sufficient_family
#print axioms gamma6Gain_full_count_upper
#print axioms gamma6Gain_full_count_literal
