import NodeTransfer

namespace WuSource.SrcGrid

run_elab do
  let env ← Lean.getEnv
  for (name, ci) in env.constants.toList do
    if (ci.type.find? fun e =>
        e.isConstOf ``NodeExtension.originalTransfer ||
        e.isConstOf ``NodeExtension.extendedNode ||
        e.isConstOf ``NodeExtension.rNode).isSome then
      Lean.logInfo m!"{name} : {ci.type}"

#check @NodeExtension.actual_nine_extension
#check @NodeExtension.start_bounds
#check @NodeExtension.start_degenerate
#check @NodeExtension.grid_cell_lower
#check @NodeExtension.grid_integral_sum
#check @NodeExtension.extendedNode_expansion
#check @Wu2008DoubleSieve.wuImprovementLimit_lower_cross
#check @Wu2008DoubleSieve.wuImprovementLimit_lower_antitone
#print Wu2008DoubleSieve.wuImprovementLimit
#print axioms NodeExtension.actual_twentyone_nat
#print axioms NodeExtension.extendedNode_expansion

end WuSource.SrcGrid
