import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse1_log_0 : (69455879/1562500000 : ℝ) ≤ log ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (2222588129/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (62673881127/62500000000 : ℝ)) (u := (1002782098033/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse1_log_1 : (238102437/12500000000 : ℝ) ≤ log ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (952409749/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (500595610563/500000000000 : ℝ)) (u := (1001191221127/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse1_log_2 : (1538582933/50000000000 : ℝ) ≤ log ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (3077165869/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001925079257/1000000000000 : ℝ)) (u := (500962539629/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse1_log_3 : (108109161/10000000000 : ℝ) ≤ log ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (270272903/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1000675910581/1000000000000 : ℝ)) (u := (500337955291/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse1_log_4 : (2553330199/100000000000 : ℝ) ≤ log ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (2553330201/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1001597105391/1000000000000 : ℝ)) (u := (62599819087/62500000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse1_log_5 : (347347539/20000000000 : ℝ) ≤ log ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (868368849/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (500543025193/500000000000 : ℝ)) (u := (1001086050387/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse1_log_6 : (17010547/6250000000 : ℝ) ≤ log ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (136084377/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (1000170119939/1000000000000 : ℝ)) (u := (50008505997/50000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse1_log_7 : (296807737/10000000000 : ℝ) ≤ log ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical)-log ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical) ∧ log ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical)-log ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical) ≤ (742019343/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical)) (b := ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical)) (l := (1001856770023/1000000000000 : ℝ)) (u := (125232096253/125000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse1_log_8 : (103205949/5000000000 : ℝ) ≤ log ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical)-log ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical) ∧ log ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical)-log ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical) ≤ (2064118983/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical)) (b := ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical)) (l := (1001290906867/1000000000000 : ℝ)) (u := (250322726717/250000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4determse1_term_0 : (-1540581499/50000000000 : ℝ) ≤ (TerminalESigned.coeffU)*(log ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffU)*(log ((23/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-770290749/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-34657377107/50000000000 : ℝ) ≤ (TerminalESigned.coeffU) ∧ (TerminalESigned.coeffU) ≤ (-69314754213/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_0]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (69314754213/100000000000 : ℝ) ≤ -(TerminalESigned.coeffU) ∧ -(TerminalESigned.coeffU) ≤ (34657377107/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse1_log_0 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse1_term_1 : (-1435165591/100000000000 : ℝ) ≤ (TerminalESigned.coeffThree)*(log ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffThree)*(log ((53/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-358791397/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-4708994709/6250000000 : ℝ) ≤ (TerminalESigned.coeffThree) ∧ (TerminalESigned.coeffThree) ≤ (-75343915343/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_1]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (75343915343/100000000000 : ℝ) ≤ -(TerminalESigned.coeffThree) ∧ -(TerminalESigned.coeffThree) ≤ (4708994709/6250000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse1_log_1 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse1_term_2 : (-52201921/3125000000 : ℝ) ≤ (TerminalESigned.coeffOne)*(log ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffOne)*(log ((33/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (-167046147/10000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (-27142857143/50000000000 : ℝ) ≤ (TerminalESigned.coeffOne) ∧ (TerminalESigned.coeffOne) ≤ (-10857142857/20000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_2]
    constructor <;> nlinarith only [hr.1,hr.2]
  have hn : (10857142857/20000000000 : ℝ) ≤ -(TerminalESigned.coeffOne) ∧ -(TerminalESigned.coeffOne) ≤ (27142857143/50000000000 : ℝ) := by
    constructor <;> linarith only [hc.1,hc.2]
  have ht := mul_bounds hn hf4delogse1_log_2 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse1_term_3 : (335803103/50000000000 : ℝ) ≤ (TerminalESigned.coeffSeven)*(log ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffSeven)*(log ((93/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (10493847/1562500000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (12424593809/20000000000 : ℝ) ≤ (TerminalESigned.coeffSeven) ∧ (TerminalESigned.coeffSeven) ≤ (31061484523/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_3]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse1_log_3 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse1_term_4 : (626563673/100000000000 : ℝ) ≤ (TerminalESigned.coeffFive)*(log ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.coeffFive)*(log ((119/10 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) ≤ (25062547/4000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (4907815481/20000000000 : ℝ) ≤ (TerminalESigned.coeffFive) ∧ (TerminalESigned.coeffFive) ≤ (12269538703/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_4]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse1_log_4 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse1_term_5 : (65212633/2500000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4))*(log ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.minusCoeff (3/4))*(log ((213/10 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) ≤ (1304252663/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (150195698991/100000000000 : ℝ) ≤ (TerminalESigned.minusCoeff (3/4)) ∧ (TerminalESigned.minusCoeff (3/4)) ≤ (9387231187/6250000000 : ℝ) := by
    rw [TerminalESigned.coefficient_5]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse1_log_5 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse1_term_6 : (7099279/1000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4))*(log ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ∧ (TerminalESigned.plusCoeff (3/4))*(log ((213/10 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) ≤ (354963953/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (260841075681/100000000000 : ℝ) ≤ (TerminalESigned.plusCoeff (3/4)) ∧ (TerminalESigned.plusCoeff (3/4)) ≤ (130420537841/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_6]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse1_log_6 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse1_term_7 : (385985651/12500000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical)-log ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2))*(log ((139/5 : ℝ)+(-53/10 : ℝ)*TerminalE.radical)-log ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical)) ≤ (3087885211/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (104036547013/100000000000 : ℝ) ≤ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ∧ ((TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2)) ≤ (52018273507/50000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_7]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse1_log_7 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem hf4determse1_term_8 : (367103497/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical)-log ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2))*(log ((139/5 : ℝ)+(53/10 : ℝ)*TerminalE.radical)-log ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical)) ≤ (183551749/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hc : (17784996921/50000000000 : ℝ) ≤ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ∧ ((TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2)) ≤ (35569993843/100000000000 : ℝ) := by
    rw [TerminalESigned.coefficient_8]
    constructor <;> nlinarith only [hr.1,hr.2]
  have ht := mul_bounds hc hf4delogse1_log_8 (by norm_num) (by norm_num)
  constructor <;> nlinarith only [ht.1,ht.2]

theorem e_cell_1_bounds : (431497/20000000 : ℝ) ≤ TerminalE.cellMass (11/5 : ℝ) (23/10 : ℝ) ∧ TerminalE.cellMass (11/5 : ℝ) (23/10 : ℝ) ≤ (1078743/50000000 : ℝ) := by
  have h0 := hf4determse1_term_0
  have h1 := hf4determse1_term_1
  have h2 := hf4determse1_term_2
  have h3 := hf4determse1_term_3
  have h4 := hf4determse1_term_4
  have h5 := hf4determse1_term_5
  have h6 := hf4determse1_term_6
  have h7 := hf4determse1_term_7
  have h8 := hf4determse1_term_8
  have hrat : TerminalESigned.rationalFull (23/10 : ℝ)-TerminalESigned.rationalFull (11/5 : ℝ) = (-2176019695289794832715114791/2304628531345341628769097756000 : ℝ) := by
    norm_num [TerminalESigned.rationalFull,TerminalE.leftArg,TerminalE.rightArg,TerminalESigned.rationalPart,TerminalE.mainCoeff,TerminalE.zeroOne,TerminalE.zeroTwo,TerminalE.negOne,TerminalE.negTwo,TerminalE.negThree,TerminalE.negFour,TerminalE.quadOne,TerminalE.quadZero,TerminalE.residue,TerminalE.q,TerminalE.k,TerminalE.a,TerminalE.b,TerminalE.c,TerminalE.d,TerminalE.e,TerminalE.f,TerminalE.g,TerminalE.h]
  rw [TerminalESigned.cellMass_collected (by norm_num : (1:ℝ) ≤ (11/5 : ℝ)) (by norm_num : (11/5 : ℝ) ≤ (23/10 : ℝ))]
  norm_num only [div_one] at hrat ⊢
  rw [hrat]
  simp only [TerminalESigned.affineLogs, TerminalESigned.coefficient_0,TerminalESigned.coefficient_1,TerminalESigned.coefficient_2,TerminalESigned.coefficient_3,TerminalESigned.coefficient_4,TerminalESigned.coefficient_5,TerminalESigned.coefficient_6,TerminalESigned.coefficient_7,TerminalESigned.coefficient_8] at *
  norm_num [TerminalESigned.leftMinus,TerminalESigned.leftPlus,TerminalESigned.rightMinus,TerminalESigned.rightPlus] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

end Hf4DE
