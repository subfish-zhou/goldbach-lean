import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse6_log_0 : (727352883/20000000000 : ℝ) ≤ log ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1818382209/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (250568890733/250000000000 : ℝ)) (u := (1002275562933/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse6_log_1 : (173917427/10000000000 : ℝ) ≤ log ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (13587299/781250000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (10010875749/10000000000 : ℝ)) (u := (1001087574901/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse6_log_2 : (2666824707/100000000000 : ℝ) ≤ log ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (266682471/10000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (250417038817/250000000000 : ℝ)) (u := (1001668155269/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse6_log_3 : (205130003/20000000000 : ℝ) ≤ log ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1025650017/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (250160309191/250000000000 : ℝ)) (u := (200128247353/200000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse6_log_4 : (2264247673/100000000000 : ℝ) ≤ log ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (566061919/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (5007080783/5000000000 : ℝ)) (u := (1001416156601/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse6_log_5 : (159797161/10000000000 : ℝ) ≤ log ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (1597971613/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (250249807789/250000000000 : ℝ)) (u := (1000999231157/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse6_log_6 : (268514683/100000000000 : ℝ) ≤ log ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (134257343/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (12502097947/12500000000 : ℝ)) (u := (1000167835761/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse6_log_7 : (1292251329/50000000000 : ℝ) ≤ log ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical)-log ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical) ∧ log ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical)-log ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical) ≤ (129225133/5000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical)) (b := ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical)) (l := (250404154871/250000000000 : ℝ)) (u := (200323323897/200000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse6_log_8 : (467753271/25000000000 : ℝ) ≤ log ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical)-log ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical) ∧ log ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical)-log ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical) ≤ (1871013087/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical)) (b := ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical)) (l := (1001170067173/1000000000000 : ℝ)) (u := (500585033587/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4determse6_term_0 : (-1260407159/50000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((14/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((27/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-504162863/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse6_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse6_term_1 : (-163795249/12500000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((29/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((57/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-1310361989/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse6_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse6_term_2 : (-1447704843/100000000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((19/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((37/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-36192621/2500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse6_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse6_term_3 : (637164241/100000000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((49/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((97/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (637164243/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse6_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse6_term_4 : (555625489/100000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((67/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((131/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (55562549/10000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse6_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse6_term_5 : (2400084629/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((109/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((217/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (1200042317/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse6_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse6_term_6 : (700396587/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((109/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((217/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (175099149/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse6_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse6_term_7 : (1344413661/50000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical)-log ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((154/5 : ℝ)+(-29/5 : ℝ)*TerminalE.radical)-log ((151/5 : ℝ)+(-57/10 : ℝ)*TerminalE.radical)) ≤ (107553093/4000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse6_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse6_term_8 : (332759619/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical)-log ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((154/5 : ℝ)+(29/5 : ℝ)*TerminalE.radical)-log ((151/5 : ℝ)+(57/10 : ℝ)*TerminalE.radical)) ≤ (16637981/2500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse6_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem e_cell_6_bounds : (2285699/100000000 : ℝ) ≤ TerminalE.cellMass (27/10 : ℝ) (14/5 : ℝ) ∧ TerminalE.cellMass (27/10 : ℝ) (14/5 : ℝ) ≤ (22857/1000000 : ℝ) := by
  have h0 := hf4determse6_term_0
  have h1 := hf4determse6_term_1
  have h2 := hf4determse6_term_2
  have h3 := hf4determse6_term_3
  have h4 := hf4determse6_term_4
  have h5 := hf4determse6_term_5
  have h6 := hf4determse6_term_6
  have h7 := hf4determse6_term_7
  have h8 := hf4determse6_term_8
  have hrat : TerminalESigned.rationalFull (14/5 : ℝ)-TerminalESigned.rationalFull (27/10 : ℝ) = (-3658543170912512266591416548671/4405928277712280668278439262492250 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (27/10 : ℝ)) (by norm_num : (27/10 : ℝ) ≤ (14/5 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
