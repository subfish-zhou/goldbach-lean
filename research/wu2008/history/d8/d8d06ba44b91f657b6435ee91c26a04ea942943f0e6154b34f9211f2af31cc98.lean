import U8CanonicalMother

namespace WuTarget.W16

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    let s := name.toString
    let has := fun t => (s.splitOn t).length > 1
    if !has "_proof" && ((has "SingularSeries" && has "le_") ||
        (has "eventually" && (has "scale" || has "log" || has "constant")) ||
        (has "tendsto" && has "log" && (has "div" || has "rpow"))) then
      Lean.logInfo m!"{name} : {info.type}"

end WuTarget.W16
