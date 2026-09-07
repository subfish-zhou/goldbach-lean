import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWF
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFRemainder
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetLogSaving
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGate
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGateSaving
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionSaving
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidC2Sieve
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`G12FlexibleWF.exists_rectangle_paid_C2_sieve, [`G12FlexibleWF.exists_rectangle_paid_sieve, `G12FlexibleWF.exists_rectangle_full_sieve, `G12FlexibleWF.exists_atom_sieve, `G12FlexibleWF.labels_test, `G12FlexibleWF.labels_card, `G12FlexibleWF.primeCount_eq_original, `G12FlexibleWF.smallOutput_le, `G12FlexibleWF.rectangle_image_subset, `G12FlexibleWF.rectangle_safe, `G12FlexibleWF.external_remainder_decomposition, `G12FlexibleWF.member_full_identity, `G12FlexibleWF.signed_corrections_paid, `G12FlexibleWF.outside_linked, `G12OutsideBudget.family_budget, `G12OutsideBudget.residue_majorant, `G12OutsideBudget.fibre_le_twenty, `G12OutsideBudget.divisibility_le, `G12OutsideBudget.mass_le, `G12RectangleGate.gate_wellFactorable, `G12RectangleGate.gate_le, `G12RectangleGate.atom_data, `G12RectangleGate.linked_mass_le, `G12FlexibleWF.family_C2_bound, `G12FlexibleRectangle.rectangle_signedError, `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeC2_goldbach_rectangle_kscale, `MathlibNt.SieveTheory.LiLiuPrereqWF.exists_external_sieve_common_family]),
    (`G12FlexibleWF.corrections_log_saving, [`G12OutsideBudget.family_log_saving, `G12OutsideBudget.scalar_log_saving, `G12OutsideBudget.denominator_lower, `G12RectangleGate.gate_log_saving, `G12RectangleGate.numerical_log_saving, `G12FlexibleWF.outside_linked, `MathlibNt.SieveTheory.LiLiuPrereqWF.externalTags_card_and_wellFactorable]),
    (`G12RectangleGate.rectangle_gate_normalized, [`G12RectangleGate.gate_normalized, `G12RectangleGate.gate_log_saving, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachBV_logCube_normalized]),
    (`G12FlexibleWF.sieve_rem, [`G12FlexibleWF.sieve_test, `G12FlexibleWF.sieve_totalMass])]
  for (root, targets) in checks do
    let mut todo := [root]
    let mut seen : Std.HashSet Name := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        todo := ci.type.getUsedConstants.toList ++ todo
        if let some v := ci.value? (allowOpaque := true) then
          todo := v.getUsedConstants.toList ++ todo
    for n in targets do
      unless seen.contains n do throwError "MISSING_PRODUCER {root} -> {n}"
      logInfo m!"REACHABLE_PRODUCER {n}"
      logInfo m!"ROOT_PRODUCER {root} -> {n}"
    for n in seen.toList do
      if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
        throwError "FORBIDDEN_TRUST {root} -> {n}"
    logInfo m!"QUADRATURE_CONE_PASS {root} {seen.size}"
