import WSrcBuchstabRoot
import Lean
open Lean Elab Command

elab "#wsrcbuchstabparentaudit_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuSource.SrcBuchstab.buchstab_le_source_fine, `WuSource.SrcBuchstab.fixed_initial_window, `WuSource.SrcBuchstab.certified_prefix, `WuSource.SrcBuchstab.tail_of_unit_window] do
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

#wsrcbuchstabparentaudit_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuSource.SrcBuchstab.propagate_step
#print axioms WuSource.SrcBuchstab.propagate_step
#check @WuSource.SrcBuchstab.propagate_prefix
#print axioms WuSource.SrcBuchstab.propagate_prefix
#check @WuSource.SrcBuchstab.tail_of_unit_window
#print axioms WuSource.SrcBuchstab.tail_of_unit_window
#check @WuSource.SrcBuchstab.fine_tail_of_initial_window
#print axioms WuSource.SrcBuchstab.fine_tail_of_initial_window
#check @WuSource.SrcBuchstab.poly
#print axioms WuSource.SrcBuchstab.poly
#check @WuSource.SrcBuchstab.slope
#print axioms WuSource.SrcBuchstab.slope
#check @WuSource.SrcBuchstab.weightedCoeffs
#print axioms WuSource.SrcBuchstab.weightedCoeffs
#check @WuSource.SrcBuchstab.hasDerivAt_poly
#print axioms WuSource.SrcBuchstab.hasDerivAt_poly
#check @WuSource.SrcBuchstab.weighted_derivative
#print axioms WuSource.SrcBuchstab.weighted_derivative
#check @WuSource.SrcBuchstab.deficit
#print axioms WuSource.SrcBuchstab.deficit
#check @WuSource.SrcBuchstab.term_lower
#print axioms WuSource.SrcBuchstab.term_lower
#check @WuSource.SrcBuchstab.poly_nonneg
#print axioms WuSource.SrcBuchstab.poly_nonneg
#check @WuSource.SrcBuchstab.bernstein
#print axioms WuSource.SrcBuchstab.bernstein
#check @WuSource.SrcBuchstab.bernstein_cap
#print axioms WuSource.SrcBuchstab.bernstein_cap
#check @WuSource.SrcBuchstab.baseCoeffs
#print axioms WuSource.SrcBuchstab.baseCoeffs
#check @WuSource.SrcBuchstab.residual
#print axioms WuSource.SrcBuchstab.residual
#check @WuSource.SrcBuchstab.initial_enclosure
#print axioms WuSource.SrcBuchstab.initial_enclosure
#check @WuSource.SrcBuchstab.cell_enclosure
#print axioms WuSource.SrcBuchstab.cell_enclosure
#check @WuSource.SrcBuchstab.left
#print axioms WuSource.SrcBuchstab.left
#check @WuSource.SrcBuchstab.left_delay
#print axioms WuSource.SrcBuchstab.left_delay
#check @WuSource.SrcBuchstab.left_previous
#print axioms WuSource.SrcBuchstab.left_previous
#check @WuSource.SrcBuchstab.certified_prefix
#print axioms WuSource.SrcBuchstab.certified_prefix
#check @WuSource.SrcBuchstab.grid_cover
#print axioms WuSource.SrcBuchstab.grid_cover
#check @WuSource.SrcBuchstab.initial_window_covered
#print axioms WuSource.SrcBuchstab.initial_window_covered
#check @WuSource.SrcBuchstab.certified_fine_tail
#print axioms WuSource.SrcBuchstab.certified_fine_tail
#check @WuSource.SrcBuchstab.row00
#print axioms WuSource.SrcBuchstab.row00
#check @WuSource.SrcBuchstab.row01
#print axioms WuSource.SrcBuchstab.row01
#check @WuSource.SrcBuchstab.row02
#print axioms WuSource.SrcBuchstab.row02
#check @WuSource.SrcBuchstab.row03
#print axioms WuSource.SrcBuchstab.row03
#check @WuSource.SrcBuchstab.row04
#print axioms WuSource.SrcBuchstab.row04
#check @WuSource.SrcBuchstab.row05
#print axioms WuSource.SrcBuchstab.row05
#check @WuSource.SrcBuchstab.row06
#print axioms WuSource.SrcBuchstab.row06
#check @WuSource.SrcBuchstab.row07
#print axioms WuSource.SrcBuchstab.row07
#check @WuSource.SrcBuchstab.row08
#print axioms WuSource.SrcBuchstab.row08
#check @WuSource.SrcBuchstab.row09
#print axioms WuSource.SrcBuchstab.row09
#check @WuSource.SrcBuchstab.row10
#print axioms WuSource.SrcBuchstab.row10
#check @WuSource.SrcBuchstab.row11
#print axioms WuSource.SrcBuchstab.row11
#check @WuSource.SrcBuchstab.row12
#print axioms WuSource.SrcBuchstab.row12
#check @WuSource.SrcBuchstab.row13
#print axioms WuSource.SrcBuchstab.row13
#check @WuSource.SrcBuchstab.row14
#print axioms WuSource.SrcBuchstab.row14
#check @WuSource.SrcBuchstab.row15
#print axioms WuSource.SrcBuchstab.row15
#check @WuSource.SrcBuchstab.row16
#print axioms WuSource.SrcBuchstab.row16
#check @WuSource.SrcBuchstab.row17
#print axioms WuSource.SrcBuchstab.row17
#check @WuSource.SrcBuchstab.row18
#print axioms WuSource.SrcBuchstab.row18
#check @WuSource.SrcBuchstab.row19
#print axioms WuSource.SrcBuchstab.row19
#check @WuSource.SrcBuchstab.row20
#print axioms WuSource.SrcBuchstab.row20
#check @WuSource.SrcBuchstab.row21
#print axioms WuSource.SrcBuchstab.row21
#check @WuSource.SrcBuchstab.row22
#print axioms WuSource.SrcBuchstab.row22
#check @WuSource.SrcBuchstab.row23
#print axioms WuSource.SrcBuchstab.row23
#check @WuSource.SrcBuchstab.row24
#print axioms WuSource.SrcBuchstab.row24
#check @WuSource.SrcBuchstab.row25
#print axioms WuSource.SrcBuchstab.row25
#check @WuSource.SrcBuchstab.row26
#print axioms WuSource.SrcBuchstab.row26
#check @WuSource.SrcBuchstab.row27
#print axioms WuSource.SrcBuchstab.row27
#check @WuSource.SrcBuchstab.row28
#print axioms WuSource.SrcBuchstab.row28
#check @WuSource.SrcBuchstab.row29
#print axioms WuSource.SrcBuchstab.row29
#check @WuSource.SrcBuchstab.row30
#print axioms WuSource.SrcBuchstab.row30
#check @WuSource.SrcBuchstab.row31
#print axioms WuSource.SrcBuchstab.row31
#check @WuSource.SrcBuchstab.row32
#print axioms WuSource.SrcBuchstab.row32
#check @WuSource.SrcBuchstab.row33
#print axioms WuSource.SrcBuchstab.row33
#check @WuSource.SrcBuchstab.row34
#print axioms WuSource.SrcBuchstab.row34
#check @WuSource.SrcBuchstab.row35
#print axioms WuSource.SrcBuchstab.row35
#check @WuSource.SrcBuchstab.row36
#print axioms WuSource.SrcBuchstab.row36
#check @WuSource.SrcBuchstab.row37
#print axioms WuSource.SrcBuchstab.row37
#check @WuSource.SrcBuchstab.row38
#print axioms WuSource.SrcBuchstab.row38
#check @WuSource.SrcBuchstab.row39
#print axioms WuSource.SrcBuchstab.row39
#check @WuSource.SrcBuchstab.row40
#print axioms WuSource.SrcBuchstab.row40
#check @WuSource.SrcBuchstab.row41
#print axioms WuSource.SrcBuchstab.row41
#check @WuSource.SrcBuchstab.row42
#print axioms WuSource.SrcBuchstab.row42
#check @WuSource.SrcBuchstab.row43
#print axioms WuSource.SrcBuchstab.row43
#check @WuSource.SrcBuchstab.row44
#print axioms WuSource.SrcBuchstab.row44
#check @WuSource.SrcBuchstab.row45
#print axioms WuSource.SrcBuchstab.row45
#check @WuSource.SrcBuchstab.row46
#print axioms WuSource.SrcBuchstab.row46
#check @WuSource.SrcBuchstab.row47
#print axioms WuSource.SrcBuchstab.row47
#check @WuSource.SrcBuchstab.row48
#print axioms WuSource.SrcBuchstab.row48
#check @WuSource.SrcBuchstab.row49
#print axioms WuSource.SrcBuchstab.row49
#check @WuSource.SrcBuchstab.row50
#print axioms WuSource.SrcBuchstab.row50
#check @WuSource.SrcBuchstab.row51
#print axioms WuSource.SrcBuchstab.row51
#check @WuSource.SrcBuchstab.row52
#print axioms WuSource.SrcBuchstab.row52
#check @WuSource.SrcBuchstab.row53
#print axioms WuSource.SrcBuchstab.row53
#check @WuSource.SrcBuchstab.row54
#print axioms WuSource.SrcBuchstab.row54
#check @WuSource.SrcBuchstab.row55
#print axioms WuSource.SrcBuchstab.row55
#check @WuSource.SrcBuchstab.row56
#print axioms WuSource.SrcBuchstab.row56
#check @WuSource.SrcBuchstab.row57
#print axioms WuSource.SrcBuchstab.row57
#check @WuSource.SrcBuchstab.row58
#print axioms WuSource.SrcBuchstab.row58
#check @WuSource.SrcBuchstab.row59
#print axioms WuSource.SrcBuchstab.row59
#check @WuSource.SrcBuchstab.row60
#print axioms WuSource.SrcBuchstab.row60
#check @WuSource.SrcBuchstab.row61
#print axioms WuSource.SrcBuchstab.row61
#check @WuSource.SrcBuchstab.row62
#print axioms WuSource.SrcBuchstab.row62
#check @WuSource.SrcBuchstab.row63
#print axioms WuSource.SrcBuchstab.row63
#check @WuSource.SrcBuchstab.row64
#print axioms WuSource.SrcBuchstab.row64
#check @WuSource.SrcBuchstab.row65
#print axioms WuSource.SrcBuchstab.row65
#check @WuSource.SrcBuchstab.row66
#print axioms WuSource.SrcBuchstab.row66
#check @WuSource.SrcBuchstab.row67
#print axioms WuSource.SrcBuchstab.row67
#check @WuSource.SrcBuchstab.coefficients
#print axioms WuSource.SrcBuchstab.coefficients
#check @WuSource.SrcBuchstab.base_00
#print axioms WuSource.SrcBuchstab.base_00
#check @WuSource.SrcBuchstab.base_01
#print axioms WuSource.SrcBuchstab.base_01
#check @WuSource.SrcBuchstab.base_02
#print axioms WuSource.SrcBuchstab.base_02
#check @WuSource.SrcBuchstab.base_03
#print axioms WuSource.SrcBuchstab.base_03
#check @WuSource.SrcBuchstab.base_04
#print axioms WuSource.SrcBuchstab.base_04
#check @WuSource.SrcBuchstab.base_05
#print axioms WuSource.SrcBuchstab.base_05
#check @WuSource.SrcBuchstab.base_06
#print axioms WuSource.SrcBuchstab.base_06
#check @WuSource.SrcBuchstab.base_07
#print axioms WuSource.SrcBuchstab.base_07
#check @WuSource.SrcBuchstab.base_08
#print axioms WuSource.SrcBuchstab.base_08
#check @WuSource.SrcBuchstab.base_09
#print axioms WuSource.SrcBuchstab.base_09
#check @WuSource.SrcBuchstab.base_10
#print axioms WuSource.SrcBuchstab.base_10
#check @WuSource.SrcBuchstab.base_11
#print axioms WuSource.SrcBuchstab.base_11
#check @WuSource.SrcBuchstab.base_12
#print axioms WuSource.SrcBuchstab.base_12
#check @WuSource.SrcBuchstab.base_13
#print axioms WuSource.SrcBuchstab.base_13
#check @WuSource.SrcBuchstab.base_14
#print axioms WuSource.SrcBuchstab.base_14
#check @WuSource.SrcBuchstab.base_15
#print axioms WuSource.SrcBuchstab.base_15
#check @WuSource.SrcBuchstab.base_16
#print axioms WuSource.SrcBuchstab.base_16
#check @WuSource.SrcBuchstab.base_17
#print axioms WuSource.SrcBuchstab.base_17
#check @WuSource.SrcBuchstab.base_18
#print axioms WuSource.SrcBuchstab.base_18
#check @WuSource.SrcBuchstab.base_19
#print axioms WuSource.SrcBuchstab.base_19
#check @WuSource.SrcBuchstab.start_20
#print axioms WuSource.SrcBuchstab.start_20
#check @WuSource.SrcBuchstab.step_20
#print axioms WuSource.SrcBuchstab.step_20
#check @WuSource.SrcBuchstab.step_21
#print axioms WuSource.SrcBuchstab.step_21
#check @WuSource.SrcBuchstab.join_21
#print axioms WuSource.SrcBuchstab.join_21
#check @WuSource.SrcBuchstab.step_22
#print axioms WuSource.SrcBuchstab.step_22
#check @WuSource.SrcBuchstab.join_22
#print axioms WuSource.SrcBuchstab.join_22
#check @WuSource.SrcBuchstab.step_23
#print axioms WuSource.SrcBuchstab.step_23
#check @WuSource.SrcBuchstab.join_23
#print axioms WuSource.SrcBuchstab.join_23
#check @WuSource.SrcBuchstab.step_24
#print axioms WuSource.SrcBuchstab.step_24
#check @WuSource.SrcBuchstab.join_24
#print axioms WuSource.SrcBuchstab.join_24
#check @WuSource.SrcBuchstab.step_25
#print axioms WuSource.SrcBuchstab.step_25
#check @WuSource.SrcBuchstab.join_25
#print axioms WuSource.SrcBuchstab.join_25
#check @WuSource.SrcBuchstab.step_26
#print axioms WuSource.SrcBuchstab.step_26
#check @WuSource.SrcBuchstab.join_26
#print axioms WuSource.SrcBuchstab.join_26
#check @WuSource.SrcBuchstab.step_27
#print axioms WuSource.SrcBuchstab.step_27
#check @WuSource.SrcBuchstab.join_27
#print axioms WuSource.SrcBuchstab.join_27
#check @WuSource.SrcBuchstab.step_28
#print axioms WuSource.SrcBuchstab.step_28
#check @WuSource.SrcBuchstab.join_28
#print axioms WuSource.SrcBuchstab.join_28
#check @WuSource.SrcBuchstab.step_29
#print axioms WuSource.SrcBuchstab.step_29
#check @WuSource.SrcBuchstab.join_29
#print axioms WuSource.SrcBuchstab.join_29
#check @WuSource.SrcBuchstab.step_30
#print axioms WuSource.SrcBuchstab.step_30
#check @WuSource.SrcBuchstab.join_30
#print axioms WuSource.SrcBuchstab.join_30
#check @WuSource.SrcBuchstab.step_31
#print axioms WuSource.SrcBuchstab.step_31
#check @WuSource.SrcBuchstab.join_31
#print axioms WuSource.SrcBuchstab.join_31
#check @WuSource.SrcBuchstab.step_32
#print axioms WuSource.SrcBuchstab.step_32
#check @WuSource.SrcBuchstab.join_32
#print axioms WuSource.SrcBuchstab.join_32
#check @WuSource.SrcBuchstab.step_33
#print axioms WuSource.SrcBuchstab.step_33
#check @WuSource.SrcBuchstab.join_33
#print axioms WuSource.SrcBuchstab.join_33
#check @WuSource.SrcBuchstab.step_34
#print axioms WuSource.SrcBuchstab.step_34
#check @WuSource.SrcBuchstab.join_34
#print axioms WuSource.SrcBuchstab.join_34
#check @WuSource.SrcBuchstab.step_35
#print axioms WuSource.SrcBuchstab.step_35
#check @WuSource.SrcBuchstab.join_35
#print axioms WuSource.SrcBuchstab.join_35
#check @WuSource.SrcBuchstab.step_36
#print axioms WuSource.SrcBuchstab.step_36
#check @WuSource.SrcBuchstab.join_36
#print axioms WuSource.SrcBuchstab.join_36
#check @WuSource.SrcBuchstab.step_37
#print axioms WuSource.SrcBuchstab.step_37
#check @WuSource.SrcBuchstab.join_37
#print axioms WuSource.SrcBuchstab.join_37
#check @WuSource.SrcBuchstab.step_38
#print axioms WuSource.SrcBuchstab.step_38
#check @WuSource.SrcBuchstab.join_38
#print axioms WuSource.SrcBuchstab.join_38
#check @WuSource.SrcBuchstab.step_39
#print axioms WuSource.SrcBuchstab.step_39
#check @WuSource.SrcBuchstab.join_39
#print axioms WuSource.SrcBuchstab.join_39
#check @WuSource.SrcBuchstab.step_40
#print axioms WuSource.SrcBuchstab.step_40
#check @WuSource.SrcBuchstab.join_40
#print axioms WuSource.SrcBuchstab.join_40
#check @WuSource.SrcBuchstab.step_41
#print axioms WuSource.SrcBuchstab.step_41
#check @WuSource.SrcBuchstab.join_41
#print axioms WuSource.SrcBuchstab.join_41
#check @WuSource.SrcBuchstab.step_42
#print axioms WuSource.SrcBuchstab.step_42
#check @WuSource.SrcBuchstab.join_42
#print axioms WuSource.SrcBuchstab.join_42
#check @WuSource.SrcBuchstab.step_43
#print axioms WuSource.SrcBuchstab.step_43
#check @WuSource.SrcBuchstab.join_43
#print axioms WuSource.SrcBuchstab.join_43
#check @WuSource.SrcBuchstab.step_44
#print axioms WuSource.SrcBuchstab.step_44
#check @WuSource.SrcBuchstab.join_44
#print axioms WuSource.SrcBuchstab.join_44
#check @WuSource.SrcBuchstab.step_45
#print axioms WuSource.SrcBuchstab.step_45
#check @WuSource.SrcBuchstab.join_45
#print axioms WuSource.SrcBuchstab.join_45
#check @WuSource.SrcBuchstab.step_46
#print axioms WuSource.SrcBuchstab.step_46
#check @WuSource.SrcBuchstab.join_46
#print axioms WuSource.SrcBuchstab.join_46
#check @WuSource.SrcBuchstab.step_47
#print axioms WuSource.SrcBuchstab.step_47
#check @WuSource.SrcBuchstab.join_47
#print axioms WuSource.SrcBuchstab.join_47
#check @WuSource.SrcBuchstab.step_48
#print axioms WuSource.SrcBuchstab.step_48
#check @WuSource.SrcBuchstab.join_48
#print axioms WuSource.SrcBuchstab.join_48
#check @WuSource.SrcBuchstab.cap_48
#print axioms WuSource.SrcBuchstab.cap_48
#check @WuSource.SrcBuchstab.step_49
#print axioms WuSource.SrcBuchstab.step_49
#check @WuSource.SrcBuchstab.join_49
#print axioms WuSource.SrcBuchstab.join_49
#check @WuSource.SrcBuchstab.cap_49
#print axioms WuSource.SrcBuchstab.cap_49
#check @WuSource.SrcBuchstab.step_50
#print axioms WuSource.SrcBuchstab.step_50
#check @WuSource.SrcBuchstab.join_50
#print axioms WuSource.SrcBuchstab.join_50
#check @WuSource.SrcBuchstab.cap_50
#print axioms WuSource.SrcBuchstab.cap_50
#check @WuSource.SrcBuchstab.step_51
#print axioms WuSource.SrcBuchstab.step_51
#check @WuSource.SrcBuchstab.join_51
#print axioms WuSource.SrcBuchstab.join_51
#check @WuSource.SrcBuchstab.cap_51
#print axioms WuSource.SrcBuchstab.cap_51
#check @WuSource.SrcBuchstab.step_52
#print axioms WuSource.SrcBuchstab.step_52
#check @WuSource.SrcBuchstab.join_52
#print axioms WuSource.SrcBuchstab.join_52
#check @WuSource.SrcBuchstab.cap_52
#print axioms WuSource.SrcBuchstab.cap_52
#check @WuSource.SrcBuchstab.step_53
#print axioms WuSource.SrcBuchstab.step_53
#check @WuSource.SrcBuchstab.join_53
#print axioms WuSource.SrcBuchstab.join_53
#check @WuSource.SrcBuchstab.cap_53
#print axioms WuSource.SrcBuchstab.cap_53
#check @WuSource.SrcBuchstab.step_54
#print axioms WuSource.SrcBuchstab.step_54
#check @WuSource.SrcBuchstab.join_54
#print axioms WuSource.SrcBuchstab.join_54
#check @WuSource.SrcBuchstab.cap_54
#print axioms WuSource.SrcBuchstab.cap_54
#check @WuSource.SrcBuchstab.step_55
#print axioms WuSource.SrcBuchstab.step_55
#check @WuSource.SrcBuchstab.join_55
#print axioms WuSource.SrcBuchstab.join_55
#check @WuSource.SrcBuchstab.cap_55
#print axioms WuSource.SrcBuchstab.cap_55
#check @WuSource.SrcBuchstab.step_56
#print axioms WuSource.SrcBuchstab.step_56
#check @WuSource.SrcBuchstab.join_56
#print axioms WuSource.SrcBuchstab.join_56
#check @WuSource.SrcBuchstab.cap_56
#print axioms WuSource.SrcBuchstab.cap_56
#check @WuSource.SrcBuchstab.step_57
#print axioms WuSource.SrcBuchstab.step_57
#check @WuSource.SrcBuchstab.join_57
#print axioms WuSource.SrcBuchstab.join_57
#check @WuSource.SrcBuchstab.cap_57
#print axioms WuSource.SrcBuchstab.cap_57
#check @WuSource.SrcBuchstab.step_58
#print axioms WuSource.SrcBuchstab.step_58
#check @WuSource.SrcBuchstab.join_58
#print axioms WuSource.SrcBuchstab.join_58
#check @WuSource.SrcBuchstab.cap_58
#print axioms WuSource.SrcBuchstab.cap_58
#check @WuSource.SrcBuchstab.step_59
#print axioms WuSource.SrcBuchstab.step_59
#check @WuSource.SrcBuchstab.join_59
#print axioms WuSource.SrcBuchstab.join_59
#check @WuSource.SrcBuchstab.cap_59
#print axioms WuSource.SrcBuchstab.cap_59
#check @WuSource.SrcBuchstab.step_60
#print axioms WuSource.SrcBuchstab.step_60
#check @WuSource.SrcBuchstab.join_60
#print axioms WuSource.SrcBuchstab.join_60
#check @WuSource.SrcBuchstab.cap_60
#print axioms WuSource.SrcBuchstab.cap_60
#check @WuSource.SrcBuchstab.step_61
#print axioms WuSource.SrcBuchstab.step_61
#check @WuSource.SrcBuchstab.join_61
#print axioms WuSource.SrcBuchstab.join_61
#check @WuSource.SrcBuchstab.cap_61
#print axioms WuSource.SrcBuchstab.cap_61
#check @WuSource.SrcBuchstab.step_62
#print axioms WuSource.SrcBuchstab.step_62
#check @WuSource.SrcBuchstab.join_62
#print axioms WuSource.SrcBuchstab.join_62
#check @WuSource.SrcBuchstab.cap_62
#print axioms WuSource.SrcBuchstab.cap_62
#check @WuSource.SrcBuchstab.step_63
#print axioms WuSource.SrcBuchstab.step_63
#check @WuSource.SrcBuchstab.join_63
#print axioms WuSource.SrcBuchstab.join_63
#check @WuSource.SrcBuchstab.cap_63
#print axioms WuSource.SrcBuchstab.cap_63
#check @WuSource.SrcBuchstab.step_64
#print axioms WuSource.SrcBuchstab.step_64
#check @WuSource.SrcBuchstab.join_64
#print axioms WuSource.SrcBuchstab.join_64
#check @WuSource.SrcBuchstab.cap_64
#print axioms WuSource.SrcBuchstab.cap_64
#check @WuSource.SrcBuchstab.step_65
#print axioms WuSource.SrcBuchstab.step_65
#check @WuSource.SrcBuchstab.join_65
#print axioms WuSource.SrcBuchstab.join_65
#check @WuSource.SrcBuchstab.cap_65
#print axioms WuSource.SrcBuchstab.cap_65
#check @WuSource.SrcBuchstab.step_66
#print axioms WuSource.SrcBuchstab.step_66
#check @WuSource.SrcBuchstab.join_66
#print axioms WuSource.SrcBuchstab.join_66
#check @WuSource.SrcBuchstab.cap_66
#print axioms WuSource.SrcBuchstab.cap_66
#check @WuSource.SrcBuchstab.step_67
#print axioms WuSource.SrcBuchstab.step_67
#check @WuSource.SrcBuchstab.join_67
#print axioms WuSource.SrcBuchstab.join_67
#check @WuSource.SrcBuchstab.cap_67
#print axioms WuSource.SrcBuchstab.cap_67
#check @WuSource.SrcBuchstab.base_certificate
#print axioms WuSource.SrcBuchstab.base_certificate
#check @WuSource.SrcBuchstab.start_certificate
#print axioms WuSource.SrcBuchstab.start_certificate
#check @WuSource.SrcBuchstab.join_certificate
#print axioms WuSource.SrcBuchstab.join_certificate
#check @WuSource.SrcBuchstab.step_certificate
#print axioms WuSource.SrcBuchstab.step_certificate
#check @WuSource.SrcBuchstab.cap_certificate
#print axioms WuSource.SrcBuchstab.cap_certificate
#check @WuSource.SrcBuchstab.fixed_initial_window
#print axioms WuSource.SrcBuchstab.fixed_initial_window
#check @WuSource.SrcBuchstab.buchstab_le_source_fine
#print axioms WuSource.SrcBuchstab.buchstab_le_source_fine
#check @WuSource.SrcBuchstab.buchstab_le_weak_fine
#print axioms WuSource.SrcBuchstab.buchstab_le_weak_fine
#check @WuSource.SrcBuchstab.buchstab_le_on_wu04_domain
#print axioms WuSource.SrcBuchstab.buchstab_le_on_wu04_domain
#check @WuSource.SrcBuchstab.weighted_buchstab_le_source_fine
#print axioms WuSource.SrcBuchstab.weighted_buchstab_le_source_fine
#check @WuSource.SrcBuchstab.fine_cap_saving
#print axioms WuSource.SrcBuchstab.fine_cap_saving
