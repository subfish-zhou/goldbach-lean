import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse5_log_0 : (3774032797/100000000000 : ℝ) ≤ log ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (3774032799/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (501180777293/500000000000 : ℝ)) (u := (1002361554587/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse5_log_1 : (442489427/25000000000 : ℝ) ≤ log ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1769957711/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001106835659/1000000000000 : ℝ)) (u := (50055341783/50000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse5_log_2 : (1369948709/50000000000 : ℝ) ≤ log ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (136994871/5000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (500856951471/500000000000 : ℝ)) (u := (1001713902943/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse5_log_3 : (518139351/50000000000 : ℝ) ≤ log ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (64767419/6250000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (40025915359/40000000000 : ℝ)) (u := (125080985497/125000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse5_log_4 : (289588241/12500000000 : ℝ) ≤ log ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (231670593/10000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (500724494989/500000000000 : ℝ)) (u := (1001448989979/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse5_log_5 : (1623921983/100000000000 : ℝ) ≤ log ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (811960993/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (1001015466477/1000000000000 : ℝ)) (u := (500507733239/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse5_log_6 : (269237627/100000000000 : ℝ) ≤ log ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (26923763/10000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (250042071919/250000000000 : ℝ)) (u := (1000168287677/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse5_log_7 : (2653075379/100000000000 : ℝ) ≤ log ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical)-log ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical) ∧ log ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical)-log ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical) ≤ (1326537691/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical)) (b := ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical)) (l := (25041488691/25000000000 : ℝ)) (u := (1001659547641/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse5_log_8 : (1906688537/100000000000 : ℝ) ≤ log ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical)-log ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical) ∧ log ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical)-log ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical) ≤ (1906688539/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical)) (b := ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical)) (l := (1001192390669/1000000000000 : ℝ)) (u := (100119239067/100000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4determse5_term_0 : (-2615961559/100000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((13/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-2615961557/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse5_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse5_term_1 : (-16669443/1250000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((28/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1333555437/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse5_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse5_term_2 : (-743686443/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((18/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-371843221/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse5_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse5_term_3 : (643767097/100000000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((48/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (643767099/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse5_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse5_term_4 : (28424913/5000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((64/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (284249131/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse5_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse5_term_5 : (2439060973/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((108/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (1219530489/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse5_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse5_term_6 : (351141161/50000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((108/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (702282331/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse5_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse5_term_7 : (2760168013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical)-log ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical)-log ((148/5 : ℝ)+(-28/5 : ℝ)*TerminalE.radical)) ≤ (1380084009/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse5_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse5_term_8 : (135641799/20000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical)-log ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical)-log ((148/5 : ℝ)+(28/5 : ℝ)*TerminalE.radical)) ≤ (169552249/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse5_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem e_cell_5_bounds : (2269939/100000000 : ℝ) ≤ TerminalE.cellMass (13/5 : ℝ) (27/10 : ℝ) ∧ TerminalE.cellMass (13/5 : ℝ) (27/10 : ℝ) ≤ (113497/5000000 : ℝ) := by
  have h0 := hf4determse5_term_0
  have h1 := hf4determse5_term_1
  have h2 := hf4determse5_term_2
  have h3 := hf4determse5_term_3
  have h4 := hf4determse5_term_4
  have h5 := hf4determse5_term_5
  have h6 := hf4determse5_term_6
  have h7 := hf4determse5_term_7
  have h8 := hf4determse5_term_8
  have hrat : TerminalESigned.rationalFull (27/10 : ℝ)-TerminalESigned.rationalFull (13/5 : ℝ) = (-4299846422940754334581/5049333997157751223482000 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (13/5 : ℝ)) (by norm_num : (13/5 : ℝ) ≤ (27/10 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
