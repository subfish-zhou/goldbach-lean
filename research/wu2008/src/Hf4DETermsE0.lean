import Hf4DELogsE0
noncomputable section
namespace Hf4DE
open Real

theorem hf4determse0_term_0 : (-54651728143/100000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((1/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((1/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-2732586407/5000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse0_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse0_term_1 : (-19767550933/100000000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1976755093/10000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse0_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse0_term_2 : (-6378620683/25000000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-25514482729/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse0_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse0_term_3 : (4341213409/50000000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (8682426821/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse0_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse0_term_4 : (9117826871/100000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (9117826873/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse0_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse0_term_5 : (17723993419/50000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (17723993421/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse0_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse0_term_6 : (867335443/10000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (4336677219/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse0_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse0_term_7 : (46675538997/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (46675539/100000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse0_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse0_term_8 : (2561394217/25000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (10245576871/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse0_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

end Hf4DE
