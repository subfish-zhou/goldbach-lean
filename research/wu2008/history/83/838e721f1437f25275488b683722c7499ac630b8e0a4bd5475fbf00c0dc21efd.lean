import U8CanonicalMother
import MathlibNt.SieveTheory.LiLiuGoldbachOnePlusOneNineFinite

namespace WuTarget.W16

#check MathlibNt.ChensTheorem.semiprime_iff
#check Finset.card_filter_add_card_filter_not
#check Finset.card_le_one
#check Real.one_le_rpow
#check Real.rpow_le_rpow_of_exponent_le
#check Nat.sub_add_cancel
#print MathlibNt.Wu2008DoubleSieve.wuPrimeComplements

run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if (name.toString.splitOn "RefinedLoss").length > 1 ||
        (name.toString.splitOn "refinedGood").length > 1 ||
        (name.toString.splitOn "ordinaryP2").length > 1 then
      Lean.logInfo m!"{name}"

end WuTarget.W16
