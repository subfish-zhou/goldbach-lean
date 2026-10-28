import WR2ClassicalNinthGridBlock000
import WR2ClassicalNinthGridBlock001
import WR2ClassicalNinthGridBlock002
import WR2ClassicalNinthGridBlock003
import WR2ClassicalNinthGridBlock004
import WR2ClassicalNinthGridBlock005
import WR2ClassicalNinthGridBlock006
import WR2ClassicalNinthGridBlock007
noncomputable section
namespace WuPaper.ClassicalNinth
open Finset
set_option maxHeartbeats 4000000 in
theorem payments_paid (j : Fin 512) : upperValue ((point j.val+point (j.val+1))/2) ≤ payment j.val := by
  have hj : j.val%64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : j.val/64 < 8 := by omega
  have hh (b : Fin 8) : upperValue ((point (64*b.val+j.val%64)+point ((64*b.val+j.val%64)+1))/2) ≤ payment (64*b.val+j.val%64) := by
    fin_cases b
    · exact grid_block_000 ⟨j.val%64,hj⟩
    · exact grid_block_001 ⟨j.val%64,hj⟩
    · exact grid_block_002 ⟨j.val%64,hj⟩
    · exact grid_block_003 ⟨j.val%64,hj⟩
    · exact grid_block_004 ⟨j.val%64,hj⟩
    · exact grid_block_005 ⟨j.val%64,hj⟩
    · exact grid_block_006 ⟨j.val%64,hj⟩
    · exact grid_block_007 ⟨j.val%64,hj⟩
  have h := hh ⟨j.val/64,hb⟩
  simpa only [show 64*(j.val/64)+j.val%64 = j.val by omega] using h

theorem ninth_main_upper : Wu08TerminalAlignment.ninthMain ≤ (268621:ℝ)/50000 := by
  have h := uniform_upper payment (fun i hi => payments_paid ⟨i,hi⟩)
  apply h.trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]

end WuPaper.ClassicalNinth
#print axioms WuPaper.ClassicalNinth.ninth_main_upper
