import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse3_log_0 : (4082199451/100000000000 : ℝ) ≤ log ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (4082199453/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1002554632183/1000000000000 : ℝ)) (u := (125319329023/125000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse3_log_1 : (366982773/20000000000 : ℝ) ≤ log ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (458728467/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001147479017/1000000000000 : ℝ)) (u := (500573739509/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse3_log_2 : (1449376843/50000000000 : ℝ) ≤ log ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (362344211/12500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (250453340803/250000000000 : ℝ)) (u := (1001813363213/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse3_log_3 : (264552733/25000000000 : ℝ) ≤ log ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (211642187/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (500330800297/500000000000 : ℝ)) (u := (200132320119/200000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse3_log_4 : (303658657/12500000000 : ℝ) ≤ log ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1214634629/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (250379861619/250000000000 : ℝ)) (u := (1001519446477/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse3_log_5 : (1678436211/100000000000 : ℝ) ≤ log ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (839218107/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (1001049573049/1000000000000 : ℝ)) (u := (20020991461/20000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse3_log_6 : (54139051/20000000000 : ℝ) ≤ log ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (270695257/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (1000169198847/1000000000000 : ℝ)) (u := (3906910933/3906250000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse3_log_7 : (56034993/2000000000 : ℝ) ≤ log ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical)-log ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical) ∧ log ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical)-log ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical) ≤ (700437413/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical)) (b := ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical)) (l := (1001752627591/1000000000000 : ℝ)) (u := (125219078449/125000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse3_log_8 : (991141419/50000000000 : ℝ) ≤ log ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical)-log ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical) ∧ log ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical)-log ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical) ≤ (1982282841/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical)) (b := ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical)) (l := (1001239694561/1000000000000 : ℝ)) (u := (500619847281/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4determse3_term_0 : (-1414783259/50000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((12/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-565913303/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse3_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse3_term_1 : (-86405997/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((27/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1382495949/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse3_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse3_term_2 : (-314721829/20000000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((17/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1573609143/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse3_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse3_term_3 : (657392049/100000000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((47/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (164348013/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse3_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse3_term_4 : (596120263/100000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((61/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (74515033/12500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse3_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse3_term_5 : (2520938999/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((107/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (630234751/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse3_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse3_term_6 : (353042207/50000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((107/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (706084421/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse3_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse3_term_7 : (2914843591/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical)-log ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical)-log ((142/5 : ℝ)+(-27/5 : ℝ)*TerminalE.radical)) ≤ (1457421797/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse3_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse3_term_8 : (705097883/100000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical)-log ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical)-log ((142/5 : ℝ)+(27/5 : ℝ)*TerminalE.radical)) ≤ (141019577/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse3_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem e_cell_3_bounds : (2225179/100000000 : ℝ) ≤ TerminalE.cellMass (12/5 : ℝ) (5/2 : ℝ) ∧ TerminalE.cellMass (12/5 : ℝ) (5/2 : ℝ) ≤ (2225181/100000000 : ℝ) := by
  have h0 := hf4determse3_term_0
  have h1 := hf4determse3_term_1
  have h2 := hf4determse3_term_2
  have h3 := hf4determse3_term_3
  have h4 := hf4determse3_term_4
  have h5 := hf4determse3_term_5
  have h6 := hf4determse3_term_6
  have h7 := hf4determse3_term_7
  have h8 := hf4determse3_term_8
  have hrat : TerminalESigned.rationalFull (5/2 : ℝ)-TerminalESigned.rationalFull (12/5 : ℝ) = (-12348268957250304676676303/13777612066421444061794531250 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (12/5 : ℝ)) (by norm_num : (12/5 : ℝ) ≤ (5/2 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
