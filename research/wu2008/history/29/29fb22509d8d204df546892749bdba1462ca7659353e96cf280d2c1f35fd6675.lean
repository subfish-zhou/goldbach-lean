import MathlibNt.Wu2008DoubleSieve.Gamma78GainMain
import Lean.Util.FoldConsts

/-! # Complete stored-member types, dependencies and axiom cones -/

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
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainFinite,
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainCell,
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainGeometry,
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainPacking,
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainIntegral,
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainApproximation,
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainSufficiency,
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainMass,
    `MathlibNt.Wu2008DoubleSieve.Gamma78GainMain]
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
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      let mut deps : Array String := #[]
      for dep in ci.getUsedConstantsAsSet do
        deps := deps.push dep.toString
      logInfo (Json.mkObj [
        ("module", toJson modName.toString),
        ("name", toJson name.toString),
        ("kind", toJson kind),
        ("type", toJson type.pretty),
        ("direct_dependencies", toJson deps),
        ("axioms", toJson (axioms.map Name.toString))]).compress
      total := total+1
  let own ← mkModuleData env
  unless own.constNames.isEmpty do
    throwError "Command-only audit introduced declarations: {own.constNames}"
  logInfo (Json.mkObj [
    ("module", toJson env.mainModule.toString),
    ("constNames_count", toJson own.constNames.size)]).compress
  logInfo (Json.mkObj [("complete_module_member_total", toJson total)]).compress

set_option pp.explicit false
set_option pp.proofs false

open Wu2008DoubleSieve

#print gamma78GainCount
#print gamma78GainLabels
#print gamma78GainLower
#print gamma78GainUpper
#print gamma78GainStart
#print gamma78GainV
#print gamma78GainRegion
#print gamma78GainIntegral
#print gamma78GainLiteral
#print gamma78GainC
#print gamma78GainInner
#print gamma78GainSample
#print gamma78GainInnerRectangle
#print Gamma78GainRectangle
#print gamma5GainPacking
#print gamma5GainCell
#print gamma5ClassicalLabels
#print gamma5ClassicalMainMass
#print gamma5ClassicalProduct
#print sourceSieveCount
#print sourceSieveCarrier
#print boxTheta
#print gamma5MassAtom
#print gamma5GainSmooth
#print AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral

#check @gamma78Gain_count_eq_nat
#check @gamma78Gain_mem_labels_iff
#check @gamma78Gain_count_le_classical
#check @gamma78Gain_count_partition
#check @gamma78Gain_region_bounds
#check @gamma78Gain_denominator_pos
#check @gamma78Gain_ratio_coordinates
#check @gamma78Gain_cutoff_le
#check @gamma78Gain_ratio_drift_identity
#check @gamma78Gain_ratio_drift
#check @gamma78Gain_rectangle_admission
#check @gamma78Gain_grid_comparison
#check @gamma78Gain_packing_actual
#check @gamma78Gain_H_pullback_ae
#check @gamma78Gain_inner_integrable
#check @gamma78Gain_outer_integrable
#check @gamma78Gain_C_inner_integrable
#check @gamma78Gain_C_outer_integrable
#check @gamma78Gain_integral_bounds
#check @gamma78Gain_approx_integral_tendsto
#check @gamma78Gain_sufficient_family
#check @gamma78Gain_inner_packings_disjoint
#check @gamma78Gain_full_mass_upper
#check @gamma78Gain_full_count_upper
#check @gamma78Gain_gamma7_full_count_upper
#check @gamma78Gain_gamma8_full_count_upper
#check @gamma78Gain_joint_full_count_upper
#check @gamma78Gain_C7_literal
#check @gamma78Gain_C8_literal
#check @gamma78Gain_G7_literal
#check @gamma78Gain_G8_literal
#check @gamma5Mass_two_insertions
#check @gamma5Mass_rectangle_mass
#check @gamma5Gain_packing_mass
#check @gamma5Gain_sorted_two
#check @gamma5Gain_cell_theta
#check @gamma5Classical_mask_upper
#check @wuImprovementLimit_sub_mem
#check @gamma5Gain_partition_sum
#check @gamma5Gain_main_mass_partition
#check @gamma5Gain_weighted_transport

#print axioms gamma78Gain_grid_comparison
#print axioms gamma78Gain_full_mass_upper
#print axioms gamma78Gain_sufficient_family
#print axioms gamma78Gain_gamma7_full_count_upper
#print axioms gamma78Gain_gamma8_full_count_upper
#print axioms gamma78Gain_joint_full_count_upper
