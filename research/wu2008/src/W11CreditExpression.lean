import W11BudgetV2

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.W11Credit
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open TotalEndpointComparison (H gap A1 rationalShared)
open ExactWeightTripleEnclosure (poly algebraic tA tB tC tD)

def endpointPacket (f : ℝ → ℝ) (j A B C D l r : ℝ) : ℝ :=
  16 * tA j A B C D * f (r / l) -
    8 * poly (tA j A B C D) (tB j B C D) (tC j C D) (tD D) (1 / 2) *
      f ((1 / 2 - l) / (1 / 2 - r)) +
    algebraic (tB j B C D) (tC j C D) (tD D) r -
    algebraic (tB j B C D) (tC j C D) (tD D) l

def alphaPacket (f : ℝ → ℝ) : ℝ :=
  f (4 / 3) + 2 * f (3 / 2) +
    (11 / 2 * f (4 / 3) - 15 / 4 * (4 - 3) +
      ((4 : ℝ)^2 - 3^2) / 2 - (4^3 - 3^3) / 36) +
    GConvexChord.m + GConvexChord.C * f (5 / 4) +
    (42823 / 151875) * (1127 / 200 - 5)

def gPacket (f : ℝ → ℝ) : ℝ :=
  (8 / a) * (42823 / 151875) * f (c 5 / a) +
    8 * ((GConvexChord.m / a + 2 * GConvexChord.C) * f (c 4 / c 5) +
      2 * GConvexChord.C * f (5 / 4)) +
    8 * (VariableGIntegral.logCoefficient * f (s / c 4) +
      VariableGIntegral.linearCoefficient * (s - c 4) -
      (s^2 - (c 4)^2) / (24 * a^3) + 11 * f (4 / 3)) +
    8 * f (6 * a / s)

/-- The full frozen credit, with all shared terms present before log payment. -/
def packet (f : ℝ → ℝ) : ℝ :=
  24 * alphaPacket f - gPacket f +
    (rationalShared + A1 * f (3 / 2) - 144 * f (4 / 3) +
      16 * gap H * f ((H - 2) / (H - 3))) +
    endpointPacket f 0 0 ((1845671 / 520931250) / 5) 0 0 a (c 5) +
    endpointPacket f 4 (GConvexChord.r4 - 287 / 250)
      ((GConvexChord.r5 - 9044059 / 6431250) -
        (GConvexChord.r4 - 287 / 250) + 1 / 144) (-1 / 144) 0 (c 5) (c 4) +
    BaseSharedSlack.lowGain

theorem log_three_identity :
    log (3 : ℝ) = log (4 / 3) + 2 * log (3 / 2) := by
  have h1 := log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0)
    (by norm_num : (3 / 2 : ℝ) ≠ 0)
  have h2 := log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (3 / 2 : ℝ) ≠ 0)
  norm_num at h1 h2
  linarith only [h1, h2]

theorem alpha_exact : Phase23.alphaModel = alphaPacket log := by
  unfold Phase23.alphaModel
  rw [Phase23.CP_difference (by norm_num) (by norm_num),
    BaseRecurrenceLower.P_difference 0 GConvexChord.C GConvexChord.m
      (by norm_num) (by norm_num), log_three_identity]
  unfold alphaPacket
  norm_num
  ring

theorem g_exact : Phase23.gModel = gPacket log := by
  change (8 / a) * (42823 / 151875) * log (c 5 / a) +
    8 * GConvexChord.endpoint +
    8 * (VariableGIntegral.primitive VariableGIntegral.s -
      VariableGIntegral.primitive (VariableGIntegral.c 4)) +
    8 * log (6 * a / s) = _
  rw [VariableGIntegral.endpoint]
  rfl

theorem shared_exact :
    SharedRationalEnvelope.deltaShared =
      rationalShared + A1 * log (3 / 2) - 144 * log (4 / 3) +
        16 * gap H * log ((H - 2) / (H - 3)) := by
  rw [TotalEndpointComparison.shared_log_endpoint]
  have he : log ((H - 3) / (H - 2)) = -log ((H - 2) / (H - 3)) := by
    rw [← log_inv]
    congr 1
    norm_num [H, a, truncatedSixthLowerAlpha]
  rw [he]
  ring

theorem credit_exact : WuTarget.W11.correlatedCredit = packet log := by
  unfold WuTarget.W11.correlatedCredit WuTarget.W11.sharedRecovery
  rw [alpha_exact, g_exact, shared_exact]
  unfold packet ExactWeightTripleEnclosure.highLower
    ExactWeightTripleEnclosure.middleLower ExactWeightTripleEnclosure.pay
    ExactWeightTripleEnclosure.payment endpointPacket
  ring

end WuTarget.W11Credit
