import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse4_log_0 : (784414263/20000000000 : ℝ) ≤ log ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (3922071317/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1002454301451/1000000000000 : ℝ)) (u := (250613575363/250000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse4_log_1 : (1801850549/100000000000 : ℝ) ≤ log ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (225231319/12500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (500563395473/500000000000 : ℝ)) (u := (1001126790947/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse4_log_2 : (176067981/6250000000 : ℝ) ≤ log ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1408543849/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001762230717/1000000000000 : ℝ)) (u := (500881115359/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse4_log_3 : (209425997/20000000000 : ℝ) ≤ log ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1047129987/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (250163667611/250000000000 : ℝ)) (u := (200130934089/200000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse4_log_4 : (118582633/5000000000 : ℝ) ≤ log ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1185826331/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001483382037/1000000000000 : ℝ)) (u := (500741691019/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse4_log_5 : (330145827/20000000000 : ℝ) ≤ log ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (1650729137/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (1001032238101/1000000000000 : ℝ)) (u := (500516119051/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse4_log_6 : (269964473/100000000000 : ℝ) ≤ log ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (10798579/4000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (1000168742031/1000000000000 : ℝ)) (u := (62510546377/62500000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse4_log_7 : (272538629/10000000000 : ℝ) ≤ log ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical)-log ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical) ∧ log ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical)-log ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical) ≤ (681346573/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical)) (b := ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical)) (l := (15651637781/15625000000 : ℝ)) (u := (200340963597/200000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse4_log_8 : (1943750959/100000000000 : ℝ) ≤ log ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical)-log ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical) ∧ log ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical)-log ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical) ≤ (971875481/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical)) (b := ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical)) (l := (250303895643/250000000000 : ℝ)) (u := (1001215582573/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4determse4_term_0 : (-1359287047/50000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((5/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-679643523/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse4_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse4_term_1 : (-271516951/20000000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((11/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-84849047/6250000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse4_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse4_term_2 : (-1529276179/100000000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((7/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1529276177/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse4_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse4_term_3 : (162627059/25000000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((19/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (325254119/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse4_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse4_term_4 : (290990841/50000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((25/2 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (581981683/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse4_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse4_term_5 : (1239662081/50000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((43/2 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (1239662083/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse4_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse4_term_6 : (140835647/20000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((43/2 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (704178241/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse4_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse4_term_7 : (708849447/25000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical)-log ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical)-log ((29/1 : ℝ)+(-11/2 : ℝ)*TerminalE.radical)) ≤ (2835397791/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse4_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse4_term_8 : (21606003/3125000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical)-log ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical)-log ((29/1 : ℝ)+(11/2 : ℝ)*TerminalE.radical)) ≤ (345696049/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse4_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem e_cell_4_bounds : (449999/20000000 : ℝ) ≤ TerminalE.cellMass (5/2 : ℝ) (13/5 : ℝ) ∧ TerminalE.cellMass (5/2 : ℝ) (13/5 : ℝ) ≤ (562499/25000000 : ℝ) := by
  have h0 := hf4determse4_term_0
  have h1 := hf4determse4_term_1
  have h2 := hf4determse4_term_2
  have h3 := hf4determse4_term_3
  have h4 := hf4determse4_term_4
  have h5 := hf4determse4_term_5
  have h6 := hf4determse4_term_6
  have h7 := hf4determse4_term_7
  have h8 := hf4determse4_term_8
  have hrat : TerminalESigned.rationalFull (13/5 : ℝ)-TerminalESigned.rationalFull (5/2 : ℝ) = (-720984593811043/825378579506250000 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (5/2 : ℝ)) (by norm_num : (5/2 : ℝ) ≤ (13/5 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
