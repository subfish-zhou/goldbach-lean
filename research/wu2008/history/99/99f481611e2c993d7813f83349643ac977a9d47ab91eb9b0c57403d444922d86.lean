import Wu04BypassTargetBudget
import U8CanonicalMother

namespace WuTarget.W16

#check ArithmeticFunction.cardFactors_mul
#check ArithmeticFunction.cardFactors_apply_prime
#check ArithmeticFunction.cardFactors_eq_one_iff_prime
#check ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    let s := name.toString
    let has := fun t => (s.splitOn t).length > 1
    if (has "SingularSeries" && (has "lower" || has "pos" || has "tendsto")) ||
        has "original_scale" ||
        (has "RefinedLoss") then
      Lean.logInfo m!"{name} : {info.type}"

end WuTarget.W16
