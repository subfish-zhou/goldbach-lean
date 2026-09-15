import Hf4DECoefficients
noncomputable section
namespace Hf4DE
open Real

theorem hf4delogsd_log_0 : (6385320297/12500000000 : ℝ) ≤ log ((5/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((5/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (25541281189/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((3/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((5/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (206488344567/200000000000 : ℝ)) (u := (258110430709/250000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogsd_log_1 : (13862943611/20000000000 : ℝ) ≤ log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (69314718057/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((2/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((4/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1044273782427/1000000000000 : ℝ)) (u := (261068445607/250000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogsd_log_2 : (7192051811/25000000000 : ℝ) ≤ log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (28768207247/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((6/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((8/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (254535686303/250000000000 : ℝ)) (u := (1018142745213/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogsd_log_3 : (11750090731/25000000000 : ℝ) ≤ log ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (23500181463/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((10/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (514905467339/500000000000 : ℝ)) (u := (1029810934679/1000000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogsd_log_4 : (13353139261/100000000000 : ℝ) ≤ log ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ∧ log ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)-log ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical) ≤ (208642801/1562500000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((14/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (b := ((16/1 : ℝ)+(0/1 : ℝ)*TerminalE.radical)) (l := (1008380634577/1000000000000 : ℝ)) (u := (504190317289/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogsd_log_5 : (8149328213/25000000000 : ℝ) ≤ log ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)-log ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ∧ log ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)-log ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical) ≤ (16298656427/50000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((22/1 : ℝ)+(-4/1 : ℝ)*TerminalE.radical)) (b := ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)) (l := (204116454647/200000000000 : ℝ)) (u := (255145568309/250000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogsd_log_6 : (63832682251/100000000000 : ℝ) ≤ log ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)-log ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ∧ log ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)-log ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical) ≤ (63832682253/100000000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((22/1 : ℝ)+(4/1 : ℝ)*TerminalE.radical)) (b := ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)) (l := (1040701938561/1000000000000 : ℝ)) (u := (520350969281/500000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogsd_log_7 : (2857996029/100000000000 : ℝ) ≤ log ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)-log ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical) ∧ log ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)-log ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical) ≤ (11164047/390625000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((32/1 : ℝ)+(-6/1 : ℝ)*TerminalE.radical)) (b := ((40/1 : ℝ)+(-8/1 : ℝ)*TerminalE.radical)) (l := (1001787843809/1000000000000 : ℝ)) (u := (100178784381/100000000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

theorem hf4delogsd_log_8 : (25080330933/100000000000 : ℝ) ≤ log ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)-log ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical) ∧ log ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)-log ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical) ≤ (3135041367/12500000000 : ℝ) := by
  have hr := Hf4Target.radical_bounds
  have hx := log_sub_bounds (a := ((32/1 : ℝ)+(6/1 : ℝ)*TerminalE.radical)) (b := ((40/1 : ℝ)+(8/1 : ℝ)*TerminalE.radical)) (l := (1015798707343/1000000000000 : ℝ)) (u := (63487419209/62500000000 : ℝ))
    (by nlinarith only [hr.1,hr.2]) (by nlinarith only [hr.1,hr.2])
    (by norm_num) (by norm_num)
    (by norm_num; nlinarith only [hr.1,hr.2]) (by norm_num; nlinarith only [hr.1,hr.2])
  norm_num [RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom] at hx ⊢
  constructor <;> linarith only [hx.1,hx.2]

end Hf4DE
