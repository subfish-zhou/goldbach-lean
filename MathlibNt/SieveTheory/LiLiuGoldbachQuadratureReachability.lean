import MathlibNt.SieveTheory.LiLiuGoldbachG67KernelQuadrature
import MathlibNt.SieveTheory.LiLiuGoldbachG12MainMassTransport
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name) := [
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.exists_goldbachG67_kernel_integral_lower, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.exists_goldbachG6_kernel_integral_lower, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.exists_goldbachG7_kernel_integral_lower, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG6Pairs_half_square_le, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG6Pairs_symmetric_sum, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.symmetric_sum_triangle, `MathlibNt.SieveTheory.LiuWeight.exists_coprimePrimeKernelRectangle_lower, `MathlibNt.SieveTheory.LiuWeight.weighted_coprime_grid_le_kernel, `MathlibNt.SieveTheory.LiuWeight.exists_abs_weighted_sum_coprimePrimeReciprocalLogRectangle_sub_lt, `MathlibNt.SieveTheory.LiuWeight.tendsto_coprimePrimeReciprocalLogInterval, `MathlibNt.SieveTheory.LiuWeight.badPrimeReciprocalLogInterval_le, `LiLiuGoldbachLogDarboux.exists_darboux, `LiLiuGoldbachLogDarboux.darboux_explicit, `LiLiuGoldbachLogDarboux.integral_eq_sum_cells, `MathlibNt.SieveTheory.PrimeReciprocalLogScale.tendsto_primeReciprocalLogInterval]),
    (`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12WindowWeightSum_le_buchstab, [`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12WindowWeightSum_le_fullRough, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12MainMassGood_le_fullRough, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12MainMass_good_pair_mem, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12GoodCross_sum_product, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12MainMassBad_le, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11_largePrimeDivisors_card_le_twenty_one, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12NormalizedCoefficient_bounds, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12FullRoughMass_le_buchstabUpper, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12_rough_upper_buchstab, `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG12_canonical_cofactor_lower_bound])]
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
