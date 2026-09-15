import WSrcGridTables

namespace WuSource.SrcGrid
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension
open scoped Interval BigOperators

theorem actual_full_index_uniform :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ j : ℕ, j ≤ 29 →
      originalTransfer (actualNine δ) j ≤ wuImprovementLimit false δ (rNode j) :=
  fun _ hd hdhi _ hj => actual_all_nat hd hdhi hj

theorem source311_full_index {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (j : Fin 30) :
    actualNine δ 0 * log (rNode (max 2 (j.val - 10)) / (rNode j.val - 1)) +
      (∑ i ∈ Finset.Icc (max 3 (j.val - 9)) 29,
        extendedNode (actualNine δ) i * log (rNode i / rNode (i - 1))) ≤
      wuImprovementLimit false δ (rNode j.val) :=
  actual_all hd hdhi j

example : gridStart 0 = 2 ∧ gridStart 12 = 2 ∧ gridStart 21 = 11 ∧
    gridStart 22 = 12 ∧ gridStart 27 = 17 ∧ gridStart 29 = 19 := by
  norm_num [gridStart]

example (z : Fin 9 → ℝ) {j : ℕ} (hj : 12 ≤ j) :
    z 0 * log (rNode (gridStart j) / (rNode j - 1)) = 0 := by
  rw [start_log_zero hj, mul_zero]

example {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, z k ≤ actualNine δ k) :
    originalTransfer z 0 ≤ wuImprovementLimit false δ 2 := by
  simpa [rNode] using table_transfer_nat hd hdhi hz (j := 0) (by norm_num)

example {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, z k ≤ actualNine δ k) :
    originalTransfer z 22 ≤ wuImprovementLimit false δ (21 / 5) := by
  convert table_transfer_nat hd hdhi hz (j := 22) (by norm_num) using 1
  norm_num [rNode]

example {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, z k ≤ actualNine δ k) :
    originalTransfer z 27 ≤ wuImprovementLimit false δ (47 / 10) := by
  convert table_transfer_nat hd hdhi hz (j := 27) (by norm_num) using 1
  norm_num [rNode]

example {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, z k ≤ actualNine δ k) :
    originalTransfer z 29 ≤ wuImprovementLimit false δ (49 / 10) := by
  convert table_transfer_nat hd hdhi hz (j := 29) (by norm_num) using 1
  norm_num [rNode]

example (j : Fin 30) :
    (∑ k : Fin 9, transferMatrix30 j k * (0 : ℝ)) = originalTransfer (fun _ => 0) j.val :=
  (transferMatrix30_expansion _ j).symm

#check @WuTarget.W01Continuous.hContinuous_le_actual
#check @WuTarget.W01Continuous.hContinuous_node_nat
#check @WuTarget.W01Continuous.upperProfile_cell
#check @NodeExtension.extendedNode_le_actual
#check @NodeExtension.actual_twentyone_nat
#print NodeExtension.rNode
#print NodeExtension.gridStart
#print NodeExtension.extendedNode
#print NodeExtension.nineProfile
#print WuTarget.W01Continuous.upperProfile
#print Wu2008DoubleSieve.wuImprovementLimit
#print Wu2008DoubleSieve.wuImprovementAtInfinity
#print Wu2008DoubleSieve.wuEventualImprovements
#print Wu2008DoubleSieve.wuAdmissibleImprovements
#print Wu2008DoubleSieve.wuBoxPhi
#print Wu2008DoubleSieve.convolutionSieveCount
#print Wu2008DoubleSieve.sourceSieveCount
#print Wu2008DoubleSieve.sourceSieveCarrier

run_cmd do
  let env ← Lean.getEnv
  for (name, ci) in env.constants.toList do
    if name.getPrefix == `WuSource.SrcGrid then
      if ci.isTheorem then
        Lean.logInfo m!"DECLARATION {name} : {ci.type}"
        Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

end WuSource.SrcGrid
