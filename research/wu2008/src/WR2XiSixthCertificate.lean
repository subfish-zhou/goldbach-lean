import WR2XiSixthGridBlock00
import WR2XiSixthGridBlock01
import WR2XiSixthGridBlock02
import WR2XiSixthGridBlock03
import WR2XiSixthGridBlock04
import WR2XiSixthGridBlock05
import WR2XiSixthGridBlock06
import WR2XiSixthGridBlock07
import WR2XiSixthGridBlock08
import WR2XiSixthGridBlock09
import WR2XiSixthGridBlock10
import WR2XiSixthGridBlock11
import WR2XiSixthGridBlock12
import WR2XiSixthGridBlock13
import WR2XiSixthGridBlock14
import WR2XiSixthGridBlock15
import WR2XiSixthGridBlock16
import WR2XiSixthGridBlock17
import WR2XiSixthGridBlock18
import WR2XiSixthGridBlock19
import WR2XiSixthGridBlock20
import WR2XiSixthGridBlock21
import WR2XiSixthGridBlock22
import WR2XiSixthGridBlock23
import WR2XiSixthGridBlock24
import WR2XiSixthGridBlock25
import WR2XiSixthGridBlock26
import WR2XiSixthGridBlock27
import WR2XiSixthGridBlock28
import WR2XiSixthGridBlock29
import WR2XiSixthGridBlock30
import WR2XiSixthGridBlock31
import WR2XiSourceFinalBudget
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous

theorem all_panels_paid (i : ℕ) (hi : i < 1024) : payment i ≤ panelBound i := by
  have hj : i%32 < 32 := Nat.mod_lt _ (by norm_num)
  have hb : i/32 < 32 := by omega
  have hh (b : Fin 32) : payment (32*b.val+i%32) ≤ panelBound (32*b.val+i%32) := by
    fin_cases b
    · exact grid_block_00 ⟨i%32,hj⟩
    · exact grid_block_01 ⟨i%32,hj⟩
    · exact grid_block_02 ⟨i%32,hj⟩
    · exact grid_block_03 ⟨i%32,hj⟩
    · exact grid_block_04 ⟨i%32,hj⟩
    · exact grid_block_05 ⟨i%32,hj⟩
    · exact grid_block_06 ⟨i%32,hj⟩
    · exact grid_block_07 ⟨i%32,hj⟩
    · exact grid_block_08 ⟨i%32,hj⟩
    · exact grid_block_09 ⟨i%32,hj⟩
    · exact grid_block_10 ⟨i%32,hj⟩
    · exact grid_block_11 ⟨i%32,hj⟩
    · exact grid_block_12 ⟨i%32,hj⟩
    · exact grid_block_13 ⟨i%32,hj⟩
    · exact grid_block_14 ⟨i%32,hj⟩
    · exact grid_block_15 ⟨i%32,hj⟩
    · exact grid_block_16 ⟨i%32,hj⟩
    · exact grid_block_17 ⟨i%32,hj⟩
    · exact grid_block_18 ⟨i%32,hj⟩
    · exact grid_block_19 ⟨i%32,hj⟩
    · exact grid_block_20 ⟨i%32,hj⟩
    · exact grid_block_21 ⟨i%32,hj⟩
    · exact grid_block_22 ⟨i%32,hj⟩
    · exact grid_block_23 ⟨i%32,hj⟩
    · exact grid_block_24 ⟨i%32,hj⟩
    · exact grid_block_25 ⟨i%32,hj⟩
    · exact grid_block_26 ⟨i%32,hj⟩
    · exact grid_block_27 ⟨i%32,hj⟩
    · exact grid_block_28 ⟨i%32,hj⟩
    · exact grid_block_29 ⟨i%32,hj⟩
    · exact grid_block_30 ⟨i%32,hj⟩
    · exact grid_block_31 ⟨i%32,hj⟩
  have he : 32*(i/32)+i%32=i := by omega
  simpa only [he] using hh ⟨i/32,hb⟩

theorem sixth_gain_lower : (283:ℝ)/5000 ≤ SourceSixth.amount :=
  uniform_certificate all_panels_paid payment_total

theorem one894_of_classical
    (hc : (17401:ℝ)/20000 ≤ SourceContinuousCount.classicalPart) :
    ∃ T ≥ 512, ∀ N ≥ T, Even N → ∃ p r q : ℕ,
      p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧ N=p+r*q ∧ r^500≤q^447 :=
  SourceContinuousCount.one894_of_integral_bounds hc sixth_gain_lower

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.sixth_gain_lower
#print axioms WuPaper.R2Xi.SixthContinuous.one894_of_classical
