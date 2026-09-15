import WSrcGridAccepted
import Lean
open Lean Elab Command

elab "#src_grid_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuSource.SrcGrid.source311_full_index, `WuSource.SrcGrid.full_tables_lower, `WuSource.SrcGrid.transferMatrix30_expansion, `WuSource.SrcGridAccepted.small_radius_tables] do
    let mut todo := #[root]
    let mut seen : Std.HashSet Name := {}
    let mut missing : Array Name := #[]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if !seen.contains n then
        seen := seen.insert n
        if seen.size == 200000 then logInfo "expanded consumer exceeds old diagnostic-size cutoff; continuing full finite visited-set traversal"
        match env.checked.get.find? n with
        | none => missing := missing.push n
        | some ci =>
          todo := todo ++ ci.type.getUsedConstants
          match ci with
          | .defnInfo v => todo := todo ++ v.value.getUsedConstants
          | .thmInfo v => todo := todo ++ v.value.getUsedConstants
          | .opaqueInfo v => todo := todo ++ v.value.getUsedConstants
          | .inductInfo v => todo := todo ++ v.ctors.toArray
          | _ => pure ()
    let names := seen.toArray.map Name.toString
    let watched := names.filter fun n =>
      n.endsWith ".Cinf" || n.endsWith ".Ainf" || n.endsWith ".originalH" ||
      n.endsWith ".Cinf_Hadm_payment" || n.endsWith ".C_tendsto" ||
      n.endsWith ".Ainf_le_supersolution" || n.endsWith ".subsolution_le_Ainf" ||
      n.endsWith ".actual_comparison_same_delta"
    let forbidden := names.filter fun n =>
      n.endsWith ".Cinf_Hadm_payment" || n.endsWith ".Ainf_le_supersolution" ||
      n.endsWith ".subsolution_le_Ainf" || n.endsWith ".actual_comparison_same_delta"
    let out ← IO.getStdout
    out.putStrLn <| (Json.mkObj [("root", toJson root.toString),
      ("visited", toJson seen.size), ("missing", toJson (missing.map Name.toString)),
      ("watched", toJson watched), ("forbidden", toJson forbidden)]).compress
    out.flush
    unless missing.isEmpty && forbidden.isEmpty do throwError "method audit failed"

#src_grid_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuSource.SrcGrid.start_bounds_all
#print axioms WuSource.SrcGrid.start_bounds_all
#check @WuSource.SrcGrid.initial_segment_lower_all
#print axioms WuSource.SrcGrid.initial_segment_lower_all
#check @WuSource.SrcGrid.actual_tail_nonneg
#print axioms WuSource.SrcGrid.actual_tail_nonneg
#check @WuSource.SrcGrid.actual_integral_lower_all
#print axioms WuSource.SrcGrid.actual_integral_lower_all
#check @WuSource.SrcGrid.actual_all_nat
#print axioms WuSource.SrcGrid.actual_all_nat
#check @WuSource.SrcGrid.actual_all
#print axioms WuSource.SrcGrid.actual_all
#check @WuSource.SrcGrid.upperProfile_initial_integral_all
#print axioms WuSource.SrcGrid.upperProfile_initial_integral_all
#check @WuSource.SrcGrid.hContinuous_node_all
#print axioms WuSource.SrcGrid.hContinuous_node_all
#check @WuSource.SrcGrid.initial_log_nonneg_all
#print axioms WuSource.SrcGrid.initial_log_nonneg_all
#check @WuSource.SrcGrid.cell_log_nonneg
#print axioms WuSource.SrcGrid.cell_log_nonneg
#check @WuSource.SrcGrid.originalTransfer_mono_all
#print axioms WuSource.SrcGrid.originalTransfer_mono_all
#check @WuSource.SrcGrid.originalTransfer_nonneg_all
#print axioms WuSource.SrcGrid.originalTransfer_nonneg_all
#check @WuSource.SrcGrid.originalTransfer_antitone_all
#print axioms WuSource.SrcGrid.originalTransfer_antitone_all
#check @WuSource.SrcGrid.upper_table_lower
#print axioms WuSource.SrcGrid.upper_table_lower
#check @WuSource.SrcGrid.table_transfer_nat
#print axioms WuSource.SrcGrid.table_transfer_nat
#check @WuSource.SrcGrid.full_tables_lower
#print axioms WuSource.SrcGrid.full_tables_lower
#check @WuSource.SrcGrid.full_tables_nonneg
#print axioms WuSource.SrcGrid.full_tables_nonneg
#check @WuSource.SrcGrid.full_tables_mono
#print axioms WuSource.SrcGrid.full_tables_mono
#check @WuSource.SrcGrid.transferMatrix30
#print axioms WuSource.SrcGrid.transferMatrix30
#check @WuSource.SrcGrid.transferMatrix30_nonneg
#print axioms WuSource.SrcGrid.transferMatrix30_nonneg
#check @WuSource.SrcGrid.transferMatrix30_old
#print axioms WuSource.SrcGrid.transferMatrix30_old
#check @WuSource.SrcGrid.transferMatrix30_expansion
#print axioms WuSource.SrcGrid.transferMatrix30_expansion
#check @WuSource.SrcGrid.transferMatrix30_lower
#print axioms WuSource.SrcGrid.transferMatrix30_lower
#check @WuSource.SrcGrid.transferMatrix30_mono
#print axioms WuSource.SrcGrid.transferMatrix30_mono
#check @WuSource.SrcGrid.transferMatrix30_antitone
#print axioms WuSource.SrcGrid.transferMatrix30_antitone
#check @WuSource.SrcGrid.full_tables_uniform
#print axioms WuSource.SrcGrid.full_tables_uniform
#check @WuSource.SrcGrid.actual_full_index_uniform
#print axioms WuSource.SrcGrid.actual_full_index_uniform
#check @WuSource.SrcGrid.source311_full_index
#print axioms WuSource.SrcGrid.source311_full_index
#check @WuSource.SrcGridAccepted.small_radius_tables
#print axioms WuSource.SrcGridAccepted.small_radius_tables
