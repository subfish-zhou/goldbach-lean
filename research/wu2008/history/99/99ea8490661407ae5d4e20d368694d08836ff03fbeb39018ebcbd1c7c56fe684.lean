import MathlibNt.Wu2008DoubleSieve.Gamma6BaseCount
import Lean.Util.FoldConsts

/-! # Complete stored-member types, direct dependencies and axiom cones -/

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
    `MathlibNt.Wu2008DoubleSieve.Gamma6BaseFinite,
    `MathlibNt.Wu2008DoubleSieve.Gamma6BaseGeometry,
    `MathlibNt.Wu2008DoubleSieve.Gamma6BaseKernel,
    `MathlibNt.Wu2008DoubleSieve.Gamma6BaseUpper,
    `MathlibNt.Wu2008DoubleSieve.Gamma6BasePrimeFinite,
    `MathlibNt.Wu2008DoubleSieve.Gamma6BaseTransport,
    `MathlibNt.Wu2008DoubleSieve.Gamma6BaseLabels,
    `MathlibNt.Wu2008DoubleSieve.Gamma6BaseMain,
    `MathlibNt.Wu2008DoubleSieve.Gamma6BaseCount]
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

#print gamma6BaseLabels
#print gamma6BaseRectLabels
#print gamma6BasePairs
#print gamma6BaseH
#print gamma6BaseIntegral
#print gamma6BaseC6
#print gamma5ClassicalCount
#print gamma5ClassicalMainMass
#print gamma5MassAtom
#print gamma5MassOldWeight
#print boxTheta
#print sourceSieveCount
#print sourceSieveCarrier
#print AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral

#check @gamma6Base_mem_labels_iff
#check @gamma6Base_count_eq_nat
#check @gamma6Base_label_geometry
#check @gamma6Base_masked_bombieri_vinogradov
#check @gamma6Base_mask_upper
#check @gamma6Base_upper_atom
#check @gamma6Base_window_discrepancy
#check @gamma6Base_pair_quadrature_uniform
#check @gamma6Base_arithmetic_pair_uniform
#check @gamma6Base_main_rect_identity_eventually
#check @gamma6Base_rectangle_mass
#check @gamma6Base_full_mass
#check @gamma6Base_rectangle_count_upper
#check @gamma6Base_C6_literal
#check @gamma6Base_C6_integrable
#check @gamma6Base_C6_bounds
#check @gamma6Base_full_count_upper
#check @gamma6Base_full_count_literal
#check @gamma5Mass_two_insertions
#check @gamma5Mass_atoms_bilateral
#check @primeOrdered_weighted_uniform
#check @gamma5Classical_ratio2_cutoff_bridge
#check @convolution_bombieri_vinogradov

#print axioms gamma6Base_mask_upper
#print axioms gamma6Base_rectangle_mass
#print axioms gamma6Base_full_mass
#print axioms gamma6Base_full_count_literal
