import WR2ClassicalSeventhGridBlock000
import WR2ClassicalSeventhGridBlock001
import WR2ClassicalSeventhGridBlock002
import WR2ClassicalSeventhGridBlock003
noncomputable section
namespace WuPaper.ClassicalSeventh
open Finset

theorem payments_paid (j : Fin 256) : upperValue ((point j.val+point (j.val+1))/2) ≤ payment j.val := by
  have hj : j.val%64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : j.val/64 < 4 := by omega
  have hh (b : Fin 4) : upperValue ((point (64*b.val+j.val%64)+point ((64*b.val+j.val%64)+1))/2) ≤ payment (64*b.val+j.val%64) := by
    fin_cases b
    · exact grid_block_000 ⟨j.val%64,hj⟩
    · exact grid_block_001 ⟨j.val%64,hj⟩
    · exact grid_block_002 ⟨j.val%64,hj⟩
    · exact grid_block_003 ⟨j.val%64,hj⟩
  have h := hh ⟨j.val/64,hb⟩
  have he : 64*(j.val/64)+j.val%64 = j.val := by omega
  simpa only [he] using h

theorem seventh_main_upper : Wu08TerminalAlignment.seventhMain ≤ (29259:ℝ)/50000 := by
  have h := uniform_upper payment (fun i hi => payments_paid ⟨i,hi⟩)
  apply h.trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]

end WuPaper.ClassicalSeventh
#print axioms WuPaper.ClassicalSeventh.seventh_main_upper
