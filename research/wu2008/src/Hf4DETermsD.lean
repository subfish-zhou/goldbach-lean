import Hf4DELogsD
noncomputable section
namespace Hf4DE
open Real

theorem hf4determsd_term_0 : (98263509953/50000000000 : ℝ) ≤ (D0FullDensity.coeffV)*(log ((5/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (D0FullDensity.coeffV)*(log ((5/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (39305403983/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (384724279217/100000000000 : ℝ) ≤ (D0FullDensity.coeffV) ∧ (D0FullDensity.coeffV) ≤ (192362139609/50000000000 : ℝ) := by
    rw [d_coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogsd_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determsd_term_1 : (0/1 : ℝ) ≤ (D0FullDensity.coeffMinusOne)*(log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (D0FullDensity.coeffMinusOne)*(log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (1/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (0/1 : ℝ) ≤ (D0FullDensity.coeffMinusOne) ∧ (D0FullDensity.coeffMinusOne) ≤ (1/100000000000 : ℝ) := by
    rw [d_coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogsd_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determsd_term_2 : (43350187423/100000000000 : ℝ) ≤ (D0FullDensity.coeffPlusThree)*(log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (D0FullDensity.coeffPlusThree)*(log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (43350187429/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150687830687/100000000000 : ℝ) ≤ (D0FullDensity.coeffPlusThree) ∧ (D0FullDensity.coeffPlusThree) ≤ (4708994709/3125000000 : ℝ) := by
    rw [d_coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogsd_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determsd_term_3 : (-66962852953/50000000000 : ℝ) ≤ (D0FullDensity.coeffTriple)*(log ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (D0FullDensity.coeffTriple)*(log ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-133925705899/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-71236527533/25000000000 : ℝ) ≤ (D0FullDensity.coeffTriple) ∧ (D0FullDensity.coeffTriple) ≤ (-284946110131/100000000000 : ℝ) := by
    rw [d_coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (284946110131/100000000000 : ℝ) ≤ -(D0FullDensity.coeffTriple) ∧ -(D0FullDensity.coeffTriple) ≤ (71236527533/25000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogsd_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determsd_term_4 : (-2330862563/50000000000 : ℝ) ≤ (D0FullDensity.coeffEleven)*(log ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (D0FullDensity.coeffEleven)*(log ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1165431281/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-872776999/2500000000 : ℝ) ≤ (D0FullDensity.coeffEleven) ∧ (D0FullDensity.coeffEleven) ≤ (-34911079959/100000000000 : ℝ) := by
    rw [d_coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (34911079959/100000000000 : ℝ) ≤ -(D0FullDensity.coeffEleven) ∧ -(D0FullDensity.coeffEleven) ≤ (872776999/2500000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogsd_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determsd_term_5 : (-99754566941/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (-3/2)-TerminalESigned.minusCoeff (1/2)))*(log ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)-log ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (-3/2)-TerminalESigned.minusCoeff (1/2)))*(log ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)-log ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (-49877283467/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-153010414367/50000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (-3/2)-TerminalESigned.minusCoeff (1/2))) ∧ ((TerminalESigned.minusCoeff (-3/2)-TerminalESigned.minusCoeff (1/2))) ≤ (-306020828733/100000000000 : ℝ) := by
    rw [d_coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (306020828733/100000000000 : ℝ) ≤ -((TerminalESigned.minusCoeff (-3/2)-TerminalESigned.minusCoeff (1/2))) ∧ -((TerminalESigned.minusCoeff (-3/2)-TerminalESigned.minusCoeff (1/2))) ≤ (153010414367/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogsd_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determsd_term_6 : (53812554471/100000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (-3/2)-TerminalESigned.plusCoeff (1/2)))*(log ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)-log ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (-3/2)-TerminalESigned.plusCoeff (1/2)))*(log ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)-log ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (26906277237/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (2634453493/3125000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (-3/2)-TerminalESigned.plusCoeff (1/2))) ∧ ((TerminalESigned.plusCoeff (-3/2)-TerminalESigned.plusCoeff (1/2))) ≤ (84302511777/100000000000 : ℝ) := by
    rw [d_coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogsd_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determsd_term_7 : (-5658324419/20000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (8/3)-D0FullDensity.zeroMinus))*(log ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)-log ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (8/3)-D0FullDensity.zeroMinus))*(log ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)-log ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical)) ≤ (-5658324413/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-989911174753/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (8/3)-D0FullDensity.zeroMinus)) ∧ ((TerminalESigned.minusCoeff (8/3)-D0FullDensity.zeroMinus)) ≤ (-30934724211/3125000000 : ℝ) := by
    rw [d_coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (30934724211/3125000000 : ℝ) ≤ -((TerminalESigned.minusCoeff (8/3)-D0FullDensity.zeroMinus)) ∧ -((TerminalESigned.minusCoeff (8/3)-D0FullDensity.zeroMinus)) ≤ (989911174753/100000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogsd_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determsd_term_8 : (-3625767887/20000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (8/3)-D0FullDensity.zeroPlus))*(log ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)-log ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (8/3)-D0FullDensity.zeroPlus))*(log ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)-log ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical)) ≤ (-18128839431/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-72283094989/100000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (8/3)-D0FullDensity.zeroPlus)) ∧ ((TerminalESigned.plusCoeff (8/3)-D0FullDensity.zeroPlus)) ≤ (-18070773747/25000000000 : ℝ) := by
    rw [d_coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (18070773747/25000000000 : ℝ) ≤ -((TerminalESigned.plusCoeff (8/3)-D0FullDensity.zeroPlus)) ∧ -((TerminalESigned.plusCoeff (8/3)-D0FullDensity.zeroPlus)) ≤ (72283094989/100000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogsd_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

end Hf4DE
