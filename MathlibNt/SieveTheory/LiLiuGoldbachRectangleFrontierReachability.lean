import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangleC2
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWF
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFRemainder
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSmall
import MathlibNt.SieveTheory.LiLiuGoldbachG12ThinCofactorMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12ThinIntegralBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleC2Sieve
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`G12RectangleWF.exists_rectangle_C2_sieve, [`G12RectangleWF.exists_rectangle_full_sieve, `G12RectangleWF.exists_rectangle_sieve, `G12RectangleWF.exists_local_dimension, `G12RectangleWF.density_eq, `G12RectangleWF.primeCount_eq_original, `G12RectangleWF.labels_test, `G12RectangleWF.labels_card, `G12RectangleWF.prime_le_sifted_small, `G12RectangleWF.external_remainder_decomposition, `G12RectangleWF.member_full_identity, `G12RectangleWF.repeated_remainder, `G12RectangleWF.residue_eq, `G12RectangleWF.output_dvd_iff, `G12RectangleWF.common_eq_discrepancy_sub_gate, `MathlibNt.SieveTheory.LiLiuPrereqWF.exists_external_sieve_common_family, `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeC2_goldbach_rectangle_kscale]),
    (`G12RectangleWF.smallOutput_le, [`G12RectangleWF.rectangle_image_subset, `G12RectangleWF.linked_small_test, `G12RectangleWF.smallOutput_eq_original, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12LinkedSmallOutputMass_le]),
    (`G12FlexibleRectangle.rectangle_C2_bound, [`G12FlexibleRectangle.rectangle_C2_input, `G12FlexibleRectangle.rectangle_signedError, `G12FlexibleRectangle.alpha_tau, `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeC2_goldbach_rectangle_kscale]),
    (`G12FlexibleRectangle.original_low_partition, [`G12FlexibleRectangle.weighted_partition, `G12FlexibleRectangle.mother_partition, `G12FlexibleRectangle.rectangle_subset_mother, `G12LowRectangle.original_low_count]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12ThinSum_integral_budget, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12ThinSum_le_kernel, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12Thin_cofactor_budget, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12Thin_canonical_endpoints, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12Thin_uniform_endpoint, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12Thin_buchstab_modulus, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12PrimeKernel_one_le_integral_eventually, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12PrimeKernel_le_integral_eventually, `LiLiuGoldbachG12BuchstabMajorant.buchstab_le_564383]),
    (`G12RectangleWF.sieve_rem, [`G12RectangleWF.sieve_test, `G12RectangleWF.sieve_nu, `G12RectangleWF.sieve_totalMass])]
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
