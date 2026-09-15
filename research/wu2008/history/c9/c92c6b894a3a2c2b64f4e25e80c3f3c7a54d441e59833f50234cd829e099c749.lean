import MathlibNt.Wu2008DoubleSieve.Gamma5MassCount
import MathlibNt.Wu2008DoubleSieve.Gamma5MassIntegrability
import MathlibNt.Wu2008DoubleSieve.Gamma5MassMask

/-!
# Complete module-membership type and axiom evidence

Every name in each imported module's `moduleData.constNames` is inspected,
including generated proof auxiliaries and equations. There is no name-prefix
or current-owner filter. The command-only audit module is also checked via
its own private `mkModuleData`.
-/

set_option pp.fullNames true
set_option pp.universes true

open Lean Elab Term

run_elab do
  let env ← getEnv
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassArithmetic,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassKernel,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassPrimeFinite,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassQuadrature,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassTransport,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassLabels,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassMain,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassCount,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassIntegrability,
    `MathlibNt.Wu2008DoubleSieve.Gamma5MassMask]
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

#print gamma5MassC5
#print gamma5MassRectangleIntegral
#print gamma5MassRectLabels
#print gamma5MassReciprocalMask
#print gamma5ClassicalCount
#print gamma5ClassicalMainMass
#print boxTheta
#print AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral

#check @gamma5Mass_actual_label_identity
#check @gamma5Mass_actual_mask_bilateral
#check @gamma5Mass_pair_quadrature_uniform
#check @gamma5Mass_arithmetic_pair_uniform
#check @gamma5Mass_rectangle_mass
#check @gamma5Mass_full_mass
#check @gamma5Mass_rectangle_count_upper
#check @gamma5Mass_full_count_upper
#check @gamma5Mass_C5_integrable
#check @gamma5Mass_C5_bounds

#print axioms gamma5Mass_rectangle_mass
#print axioms gamma5Mass_full_mass
#print axioms gamma5Mass_rectangle_count_upper
#print axioms gamma5Mass_full_count_upper
#print axioms gamma5Classical_full_upper
#print axioms primeOrdered_weighted_uniform
