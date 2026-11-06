import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabLaplaceODE
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabAbel
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailTransportLimit

/-! Euler identification and effective compact reduction for the original joint kernel. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter Real LiLiuPrereqBuchstab SecondFunctionalCoupled
open scoped Topology

/-- Two independently proved limits of the same literal scaled transform identify the constant. -/
theorem buchstabTailLimit_eq_exp_neg_euler :
    buchstabTailLimit = exp (-eulerMascheroniConstant) :=
  tendsto_nhds_unique tendsto_mul_buchstabLaplace_zero buchstabLaplace_scaled_tendsto





/-- A rigorous sandwich, not an unconditional equality with the compact supremum. -/
theorem compact_euler_tail_sandwich (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m) {P : ℝ}
    (hP : max 2 (((m : ℝ) + 6) / 2) ≤ P) :
    max (compactSup p P) (exp (-eulerMascheroniConstant) * M p) ≤ jointSup p ∧
      jointSup p ≤ max (compactSup p P)
        (exp (-eulerMascheroniConstant) * M p + 4 * M p / (m.factorial : ℝ)) := by
  simpa only [buchstabTailLimit_eq_exp_neg_euler] using compact_tail_sandwich p hp hs m hm hP


end Wu2008DoubleSieve.SecondFunctionalJointTail
