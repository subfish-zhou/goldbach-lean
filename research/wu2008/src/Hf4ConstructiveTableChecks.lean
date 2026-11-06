import Hf4ConstructiveTableData
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! UNCOMPILED arithmetic/enclosure decision experiment. -/
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Hf4Quad.ConstructiveDag.DirectTable

theorem panel_00 : panelCheck ⟨0, by decide⟩ = true := by
  decide +kernel

theorem panel_01 : panelCheck ⟨1, by decide⟩ = true := by
  decide +kernel

theorem panel_02 : panelCheck ⟨2, by decide⟩ = true := by
  decide +kernel

theorem panel_03 : panelCheck ⟨3, by decide⟩ = true := by
  decide +kernel

theorem panel_04 : panelCheck ⟨4, by decide⟩ = true := by
  decide +kernel

theorem panel_05 : panelCheck ⟨5, by decide⟩ = true := by
  decide +kernel

theorem panel_06 : panelCheck ⟨6, by decide⟩ = true := by
  decide +kernel

theorem panel_07 : panelCheck ⟨7, by decide⟩ = true := by
  decide +kernel

theorem panel_08 : panelCheck ⟨8, by decide⟩ = true := by
  decide +kernel

theorem panel_09 : panelCheck ⟨9, by decide⟩ = true := by
  decide +kernel

theorem panel_10 : panelCheck ⟨10, by decide⟩ = true := by
  decide +kernel

theorem panel_11 : panelCheck ⟨11, by decide⟩ = true := by
  decide +kernel

theorem panel_12 : panelCheck ⟨12, by decide⟩ = true := by
  decide +kernel

theorem panel_13 : panelCheck ⟨13, by decide⟩ = true := by
  decide +kernel

theorem panel_14 : panelCheck ⟨14, by decide⟩ = true := by
  decide +kernel

theorem panel_15 : panelCheck ⟨15, by decide⟩ = true := by
  decide +kernel

theorem panel_16 : panelCheck ⟨16, by decide⟩ = true := by
  decide +kernel

theorem panel_17 : panelCheck ⟨17, by decide⟩ = true := by
  decide +kernel

theorem panel_18 : panelCheck ⟨18, by decide⟩ = true := by
  decide +kernel

theorem panel_19 : panelCheck ⟨19, by decide⟩ = true := by
  decide +kernel

theorem panel_20 : panelCheck ⟨20, by decide⟩ = true := by
  decide +kernel

theorem panel_21 : panelCheck ⟨21, by decide⟩ = true := by
  decide +kernel

theorem panel_22 : panelCheck ⟨22, by decide⟩ = true := by
  decide +kernel

theorem panel_23 : panelCheck ⟨23, by decide⟩ = true := by
  decide +kernel

theorem panel_24 : panelCheck ⟨24, by decide⟩ = true := by
  decide +kernel

theorem panel_25 : panelCheck ⟨25, by decide⟩ = true := by
  decide +kernel

theorem panel_26 : panelCheck ⟨26, by decide⟩ = true := by
  decide +kernel

theorem panel_27 : panelCheck ⟨27, by decide⟩ = true := by
  decide +kernel

theorem panel_28 : panelCheck ⟨28, by decide⟩ = true := by
  decide +kernel

theorem panel_29 : panelCheck ⟨29, by decide⟩ = true := by
  decide +kernel

theorem panel_30 : panelCheck ⟨30, by decide⟩ = true := by
  decide +kernel

theorem panel_31 : panelCheck ⟨31, by decide⟩ = true := by
  decide +kernel

theorem panel_32 : panelCheck ⟨32, by decide⟩ = true := by
  decide +kernel

theorem panel_33 : panelCheck ⟨33, by decide⟩ = true := by
  decide +kernel

theorem panel_34 : panelCheck ⟨34, by decide⟩ = true := by
  decide +kernel

theorem panel_35 : panelCheck ⟨35, by decide⟩ = true := by
  decide +kernel

theorem panel_36 : panelCheck ⟨36, by decide⟩ = true := by
  decide +kernel

theorem panel_37 : panelCheck ⟨37, by decide⟩ = true := by
  decide +kernel

theorem panel_38 : panelCheck ⟨38, by decide⟩ = true := by
  decide +kernel

theorem panel_39 : panelCheck ⟨39, by decide⟩ = true := by
  decide +kernel

theorem all_panels (i : Fin 40) : panelCheck i = true := by
  fin_cases i
  · exact panel_00
  · exact panel_01
  · exact panel_02
  · exact panel_03
  · exact panel_04
  · exact panel_05
  · exact panel_06
  · exact panel_07
  · exact panel_08
  · exact panel_09
  · exact panel_10
  · exact panel_11
  · exact panel_12
  · exact panel_13
  · exact panel_14
  · exact panel_15
  · exact panel_16
  · exact panel_17
  · exact panel_18
  · exact panel_19
  · exact panel_20
  · exact panel_21
  · exact panel_22
  · exact panel_23
  · exact panel_24
  · exact panel_25
  · exact panel_26
  · exact panel_27
  · exact panel_28
  · exact panel_29
  · exact panel_30
  · exact panel_31
  · exact panel_32
  · exact panel_33
  · exact panel_34
  · exact panel_35
  · exact panel_36
  · exact panel_37
  · exact panel_38
  · exact panel_39

end Hf4Quad.ConstructiveDag.DirectTable
