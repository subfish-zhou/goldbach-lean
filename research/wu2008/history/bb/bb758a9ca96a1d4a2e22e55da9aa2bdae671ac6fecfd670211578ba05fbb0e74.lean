import WRMapMFirstFunctions
import WRMapMFirstConstants
import WRMapMFirstPartition
import WRMapMFirstTransport
import WRMapMFirstLow
import WRMapMFirstErrors

noncomputable section
namespace WuPaper.RMapMFirst

theorem original_C1234_identity :
    C1 = Wu08TerminalAlignment.firstMain ∧
    C2 = Wu08TerminalAlignment.secondMain ∧
    C3 = Wu08TerminalAlignment.thirdMain ∧
    C4 = Wu08TerminalAlignment.fourthMain :=
  ⟨C1_exact, C2_exact, C3_exact, C4_exact⟩

#check @original_C1234_identity
#print axioms original_C1234_identity
#check @a_piecewise_original
#print axioms a_piecewise_original
#check @A_piecewise_original
#print axioms A_piecewise_original
#check @C1_original
#print axioms C1_original
#check @C2_original
#print axioms C2_original
#check @C3_original
#print axioms C3_original
#check @C4_original
#print axioms C4_original
#check @C3_partition
#print axioms C3_partition
#check @C4_partition
#print axioms C4_partition
#check @C3_minus_C4_original
#print axioms C3_minus_C4_original
#check @C1_directed_lower
#print axioms C1_directed_lower
#check @C2_directed_lower
#print axioms C2_directed_lower
#check @C3_directed_upper
#print axioms C3_directed_upper
#check @C4_directed_upper
#print axioms C4_directed_upper
#check @C34_exact_combination
#print axioms C34_exact_combination
#check @C34_component_error
#print axioms C34_component_error

#check @Wu08OriginalFirstSteps.B_literal
#print axioms Wu08OriginalFirstSteps.B_literal
#check @Wu08OriginalFirstSteps.C_literal
#print axioms Wu08OriginalFirstSteps.C_literal
#check @Wu08OriginalFirstSteps.D_literal
#print axioms Wu08OriginalFirstSteps.D_literal
#check @Wu08OriginalFirstSteps.E_literal
#print axioms Wu08OriginalFirstSteps.E_literal
#check @Wu08OriginalFirstSteps.B_nonneg
#print axioms Wu08OriginalFirstSteps.B_nonneg
#check @Wu08OriginalFirstSteps.C_nonneg
#print axioms Wu08OriginalFirstSteps.C_nonneg
#check @Wu08OriginalFirstSteps.D_nonneg
#print axioms Wu08OriginalFirstSteps.D_nonneg
#check @Wu08OriginalFirstSteps.E_nonneg
#print axioms Wu08OriginalFirstSteps.E_nonneg
#check @Wu2008DoubleSieve.wuLowerCoefficient_sub_eq_integral
#print axioms Wu2008DoubleSieve.wuLowerCoefficient_sub_eq_integral
#check @Wu2008DoubleSieve.wuUpperCoefficient_sub_eq_integral
#print axioms Wu2008DoubleSieve.wuUpperCoefficient_sub_eq_integral
#check @Wu08TerminalAlignment.first_actual_count
#print axioms Wu08TerminalAlignment.first_actual_count
#check @Wu2008DoubleSieve.SingleUpperClassicalAssembly.original_third_fourth_Glin_upper
#print axioms Wu2008DoubleSieve.SingleUpperClassicalAssembly.original_third_fourth_Glin_upper

end WuPaper.RMapMFirst
