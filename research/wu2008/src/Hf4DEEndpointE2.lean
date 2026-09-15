import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse2_log_0 : (26599759/625000000 : ℝ) ≤ log ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (4255961443/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (40106540671/40000000000 : ℝ)) (u := (125332939597/125000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse2_log_1 : (1869213299/100000000000 : ℝ) ≤ log ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (934606651/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (15643264703/15625000000 : ℝ)) (u := (1001168940993/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse2_log_2 : (2985296313/100000000000 : ℝ) ≤ log ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (746324079/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001867551903/1000000000000 : ℝ)) (u := (31308360997/31250000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse2_log_3 : (1069528911/100000000000 : ℝ) ≤ log ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (534764457/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (250167169759/250000000000 : ℝ)) (u := (1000668679037/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse2_log_4 : (2489755161/100000000000 : ℝ) ≤ log ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (2489755163/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001557308323/1000000000000 : ℝ)) (u := (250389327081/250000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse2_log_5 : (17070893/1000000000 : ℝ) ≤ log ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (1707089303/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (500533750093/500000000000 : ℝ)) (u := (1001067500187/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse2_log_6 : (67857501/25000000000 : ℝ) ≤ log ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (135715003/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (1000169658143/1000000000000 : ℝ)) (u := (31255301817/31250000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse2_log_7 : (1441257983/50000000000 : ℝ) ≤ log ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical)-log ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical) ∧ log ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical)-log ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical) ≤ (2882515969/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical)) (b := ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical)) (l := (500901598143/500000000000 : ℝ)) (u := (1001803196287/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse2_log_8 : (252796667/12500000000 : ℝ) ≤ log ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical)-log ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical) ∧ log ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical)-log ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical) ≤ (2022373339/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical)) (b := ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical)) (l := (1001264782499/1000000000000 : ℝ)) (u := (400505913/400000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4determse2_term_0 : (-1475004607/50000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-2950009211/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse2_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse2_term_1 : (-176042311/12500000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-281667697/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse2_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse2_term_2 : (-1620589429/100000000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1620589427/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse2_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse2_term_3 : (332211557/50000000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (664423117/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse2_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse2_term_4 : (305481473/50000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (610962947/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse2_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse2_term_5 : (1281987353/50000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (320496839/12500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse2_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse2_term_6 : (354000471/50000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (177000237/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse2_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse2_term_7 : (1499435039/50000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical)-log ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical)-log ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical)) ≤ (1499435041/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse2_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse2_term_8 : (719358071/100000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical)-log ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical)-log ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical)) ≤ (719358073/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse2_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem e_cell_2_bounds : (137167/6250000 : ℝ) ≤ TerminalE.cellMass (23/10 : ℝ) (12/5 : ℝ) ∧ TerminalE.cellMass (23/10 : ℝ) (12/5 : ℝ) ≤ (2194673/100000000 : ℝ) := by
  have h0 := hf4determse2_term_0
  have h1 := hf4determse2_term_1
  have h2 := hf4determse2_term_2
  have h3 := hf4determse2_term_3
  have h4 := hf4determse2_term_4
  have h5 := hf4determse2_term_5
  have h6 := hf4determse2_term_6
  have h7 := hf4determse2_term_7
  have h8 := hf4determse2_term_8
  have hrat : TerminalESigned.rationalFull (12/5 : ℝ)-TerminalESigned.rationalFull (23/10 : ℝ) = (-809354818203902208301518731/879919974155651832222967050750 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (23/10 : ℝ)) (by norm_num : (23/10 : ℝ) ≤ (12/5 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
