import WSrcFourEnclosureAccepted

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut pending := #[``WuTarget.SourceFourAccepted.original_pair_enclosure,
    ``WuSource.SrcFourEnclosure.ordinary_P2_enclosed]
  let mut seen : Std.HashSet Name := {}
  let mut missing : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    match env.checked.get.find? name with
    | none => missing := missing.push name
    | some info =>
      pending := pending ++ info.type.getUsedConstants
      match info with
      | .defnInfo v => pending := pending ++ v.value.getUsedConstants
      | .thmInfo v => pending := pending ++ v.value.getUsedConstants
      | .opaqueInfo v => pending := pending ++ v.value.getUsedConstants
      | .inductInfo v => pending := pending ++ v.ctors.toArray
      | _ => pure ()
  let banned := #[`sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler]
  let forbidden := banned.filter (fun n => seen.contains n)
  let required := #[``WuSource.SrcFourEnclosure.mass_one_dimensional,
    ``WuSource.SrcFourEnclosure.midpoint_64,
    ``WuSource.SrcFourEnclosure.small_certificate,
    ``WuSource.SrcFourEnclosure.large_certificate,
    ``WuSource.SrcBuchstabLower.buchstab_lower56,
    ``WuSource.SrcBuchstab.buchstab_le_source_fine]
  let absent := required.filter (fun n => !seen.contains n)
  logInfo m!"SourceFour actual enclosure/count cone: constants={seen.size}; missing={missing}; forbidden={forbidden}; required_absent={absent}"
  unless missing.isEmpty && forbidden.isEmpty && absent.isEmpty do
    throwError "SourceFour actual enclosure/count dependency audit failed"
