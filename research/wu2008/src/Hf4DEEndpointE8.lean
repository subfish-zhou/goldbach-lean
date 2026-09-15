import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse8_log_0 : (3390155167/100000000000 : ℝ) ≤ log ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (3390155169/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (501060546661/500000000000 : ℝ)) (u := (1002121093323/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse8_log_1 : (1680711831/100000000000 : ℝ) ≤ log ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1680711833/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (200210199361/200000000000 : ℝ)) (u := (500525498403/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse8_log_2 : (632945199/25000000000 : ℝ) ≤ log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (2531780799/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (200316723119/200000000000 : ℝ)) (u := (250395903899/250000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse8_log_3 : (1005033583/100000000000 : ℝ) ≤ log ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (502516793/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (200125668663/200000000000 : ℝ)) (u := (250157085829/250000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse8_log_4 : (541537419/25000000000 : ℝ) ≤ log ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (2166149679/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (125169345051/125000000000 : ℝ)) (u := (1001354760409/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse8_log_5 : (24195031/1562500000 : ℝ) ≤ log ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (1548481987/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (1000968269711/1000000000000 : ℝ)) (u := (62560516857/62500000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse8_log_6 : (133540191/50000000000 : ℝ) ≤ log ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (53416077/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (250041734793/250000000000 : ℝ)) (u := (1000166939173/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse8_log_7 : (2457469219/100000000000 : ℝ) ≤ log ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical)-log ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical) ∧ log ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical)-log ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical) ≤ (1228734611/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical)) (b := ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical)) (l := (1001537098389/1000000000000 : ℝ)) (u := (100153709839/100000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse8_log_8 : (225440361/12500000000 : ℝ) ≤ log ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical)-log ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical) ∧ log ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical)-log ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical) ≤ (1803522891/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical)) (b := ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical)) (l := (125140979667/125000000000 : ℝ)) (u := (1001127837337/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4determse8_term_0 : (-2349877723/100000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((29/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-2349877721/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse8_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse8_term_1 : (-1266314101/100000000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((59/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1266314099/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse8_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse8_term_2 : (-1374395291/100000000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((39/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1374395289/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse8_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse8_term_3 : (624356701/100000000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((99/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (19511147/3125000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse8_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse8_term_4 : (106310629/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((137/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (531553147/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse8_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse8_term_5 : (2325753339/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((219/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (465150669/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse8_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse8_term_6 : (696655341/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((219/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (13933107/2000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse8_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse8_term_7 : (2556666119/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical)-log ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical)-log ((157/5 : ℝ)+(-59/10 : ℝ)*TerminalE.radical)) ≤ (2556666123/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse8_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse8_term_8 : (32075649/5000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical)-log ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical)-log ((157/5 : ℝ)+(59/10 : ℝ)*TerminalE.radical)) ≤ (320756491/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse8_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem e_cell_8_bounds : (1153449/50000000 : ℝ) ≤ TerminalE.cellMass (29/10 : ℝ) (3/1 : ℝ) ∧ TerminalE.cellMass (29/10 : ℝ) (3/1 : ℝ) ≤ (2306899/100000000 : ℝ) := by
  have h0 := hf4determse8_term_0
  have h1 := hf4determse8_term_1
  have h2 := hf4determse8_term_2
  have h3 := hf4determse8_term_3
  have h4 := hf4determse8_term_4
  have h5 := hf4determse8_term_5
  have h6 := hf4determse8_term_6
  have h7 := hf4determse8_term_7
  have h8 := hf4determse8_term_8
  have hrat : TerminalESigned.rationalFull (3/1 : ℝ)-TerminalESigned.rationalFull (29/10 : ℝ) = (-490095128743307335993/620281141952852495115000 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (29/10 : ℝ)) (by norm_num : (29/10 : ℝ) ≤ (3/1 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
