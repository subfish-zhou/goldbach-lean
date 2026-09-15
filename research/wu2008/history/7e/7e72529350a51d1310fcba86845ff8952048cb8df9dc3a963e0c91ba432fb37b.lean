import W09PaidRowsV2
import WSourceClosureBudget
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledFeedback

namespace WuSource.SrcSingle
open Wu2008DoubleSieve
#check @secondFunctionalMother_finite
#check @secondFunctionalMother_source
end WuSource.SrcSingle

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Wu2008DoubleSieve" && !s.contains "_proof" &&
        !s.contains "._" && !s.contains "match_" then
      let cs := c.type.getUsedConstants
      if cs.contains `Wu2008DoubleSieve.wuOmega1 ||
          cs.contains `Wu2008DoubleSieve.wuOmega2 ||
          cs.contains `Wu2008DoubleSieve.secondFunctionalMotherGammaSum ||
          cs.contains `Wu2008DoubleSieve.secondFunctionalMotherGamma then
        logInfo m!"{n} : {c.type}"
