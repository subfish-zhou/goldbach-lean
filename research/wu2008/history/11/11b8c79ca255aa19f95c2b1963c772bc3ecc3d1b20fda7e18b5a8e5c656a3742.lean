import WSrcNineGridInstance
import WSrcSixthGainConsumer

noncomputable section
namespace WuTarget.SourceSixthInstance
open Wu2008DoubleSieve NodeExtension

def nodes (j : Fin 21) : ℝ := SourceNodeInstance.h (j.val+1)

/-- Conservative consumed gain: full weights minus the stated high-domain debit.
This is not claimed to be the full original high-domain h contribution. -/
def amount : ℝ := WuSource.SrcSixthGain.conservative nodes

theorem nodes_nonneg (j : Fin 21) : 0 ≤ nodes j :=
  SourceNodeInstance.lower_nonneg (by omega)

theorem nodes_le_transferred (j : Fin 21) :
    nodes j ≤ WuSource.SrcSixthGain.transferred WuSource.SrcNine.z j := by
  change originalTransfer WuSource.SrcNine.z (j.val+1) ≤ _
  rw [originalTransfer_expansion]
  exact le_rfl

theorem actual_sixth_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((381/100 : ℝ)+amount-ε)*U8CanonicalMother.M N ≤ SixthSlotCore.sixth N :=
  WuSource.SrcSixthGain.actual_sixth_classical_lower
    (fun i => (WuSource.SrcNine.z_positive i).le) nodes_nonneg
    nodes_le_transferred WuSource.SrcNine.d_pos
    (fun _ hδ hr => WuSource.SrcNine.actual_nine_lower hδ hr) hε

end WuTarget.SourceSixthInstance

#check @WuTarget.SourceSixthInstance.actual_sixth_count
#print axioms WuTarget.SourceSixthInstance.actual_sixth_count
