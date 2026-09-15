import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogse0_log_0 : (15769147207/20000000000 : ℝ) ≤ log ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((1/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((1/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (78845736037/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((1/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((11/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1050512967157/1000000000000 : ℝ)) (u := (525256483579/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse0_log_1 : (13118213223/50000000000 : ℝ) ≤ log ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (1639776653/6250000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((26/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (508266473891/500000000000 : ℝ)) (u := (1016532947783/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse0_log_2 : (11750090731/25000000000 : ℝ) ≤ log ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (23500181463/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((16/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (514905467339/500000000000 : ℝ)) (u := (1029810934679/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse0_log_3 : (3494048559/25000000000 : ℝ) ≤ log ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (13976194239/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((46/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1008773383899/1000000000000 : ℝ)) (u := (10087733839/10000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse0_log_4 : (18578177821/50000000000 : ℝ) ≤ log ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (7431271129/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((58/5 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (511747234591/500000000000 : ℝ)) (u := (1023494469183/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse0_log_5 : (11800599843/50000000000 : ℝ) ≤ log ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (2950149961/12500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((106/5 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (l := (202972015803/200000000000 : ℝ)) (u := (126857509877/125000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse0_log_6 : (831287251/25000000000 : ℝ) ≤ log ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (3325149007/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((106/5 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (l := (12526004739/12500000000 : ℝ)) (u := (1002080379121/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse0_log_7 : (44864559943/100000000000 : ℝ) ≤ log ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (8972911989/20000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((20/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((136/5 : ℝ)+(-26/5 : ℝ)*TerminalE.radical)) (l := (257109295247/250000000000 : ℝ)) (u := (1028437180989/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogse0_log_8 : (3600498539/12500000000 : ℝ) ≤ log ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical)-log ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (7200997079/25000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((20/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((136/5 : ℝ)+(26/5 : ℝ)*TerminalE.radical)) (l := (1018165514363/1000000000000 : ℝ)) (u := (203633102873/200000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

end Hf4DE
