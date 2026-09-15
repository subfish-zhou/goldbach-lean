import GatedDensityLog

namespace GatedDensityPayment
open Wu2008DoubleSieve MotherPair Real Set MeasureTheory
open scoped Interval BigOperators
noncomputable section

/-- The original endpoint gate and full logarithmic cross-ratio on an original cell. -/
def kernelEndpoint (p : SecondFunctionalParameters) (j : Term) (a b : ℝ) : ℝ :=
  if feedbackLower p j a < min (feedbackUpper p j a) (feedbackUpper p j b) then
    log (ratio (feedbackPole p j a) (feedbackLower p j a)
      (min (feedbackUpper p j a) (feedbackUpper p j b))) / b
  else 0

theorem kernelEndpoint_le {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {a b v : ℝ} (ha : 1 ≤ a) (hb : b ≤ 3) (hv : v ∈ Icc a b) :
    kernelEndpoint p j a b ≤ feedbackLogKernel p j v := by
  have hab : a ≤ b := hv.1.trans hv.2
  have hva : v ∈ Icc 1 3 := ⟨ha.trans hv.1,hv.2.trans hb⟩
  have haa : a ∈ Icc 1 3 := ⟨ha,hab.trans hb⟩
  have hl := lower_antitone hp j ha hv.1
  have hu := upper_endpoint_min hp j ha hv
  unfold kernelEndpoint
  split_ifs with hgate
  · have hvaGate : feedbackLower p j v < feedbackUpper p j v :=
      hl.trans_lt (hgate.trans_le hu)
    have haGate : feedbackLower p j a < feedbackUpper p j a :=
      hgate.trans_le (min_le_left _ _)
    have hUa := (feedback_pole_geometry hp j haa ⟨haGate.le,le_rfl⟩).2
    have hUv := (feedback_pole_geometry hp j hva ⟨hvaGate.le,le_rfl⟩).2
    have hPa : min (feedbackUpper p j a) (feedbackUpper p j b) < feedbackPole p j a :=
      (min_le_left _ _).trans_lt hUa
    have hLa := lower_pos hp j a
    have hLv := lower_pos hp j v
    have hratio := ratio_mono hLv hvaGate hUv hLa hgate hPa hl hu
      (pole_antitone hp j ha hv.1)
    have hlog := log_le_log (ratio_pos hLa hgate hPa) hratio
    have hlog0 := log_nonneg (ratio_one_le hLa hgate hPa)
    have hlogv := hlog0.trans hlog
    have hfactor := factor_lower hp j hva.1 hv.2 (hLv.trans (hvaGate.trans hUv))
    rw [feedbackLogKernel,if_pos ⟨hva,hvaGate⟩]
    change _ ≤ feedbackFactor p j v * log (ratio (feedbackPole p j v)
      (feedbackLower p j v) (feedbackUpper p j v))
    calc
      log (ratio (feedbackPole p j a) (feedbackLower p j a)
        (min (feedbackUpper p j a) (feedbackUpper p j b))) / b
          ≤ log (ratio (feedbackPole p j v) (feedbackLower p j v)
              (feedbackUpper p j v)) / b :=
        div_le_div_of_nonneg_right hlog (by linarith)
      _ = (1/b)*log (ratio (feedbackPole p j v) (feedbackLower p j v)
          (feedbackUpper p j v)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hlogv
  · exact feedback_log_nonnegative hp j v

theorem kernelEndpoint_nonneg {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    0 ≤ kernelEndpoint p j a b := by
  unfold kernelEndpoint
  split_ifs with hg
  · have hUa := (feedback_pole_geometry hp j ⟨ha,hab.trans hb⟩
        ⟨(hg.trans_le (min_le_left _ _)).le,le_rfl⟩).2
    apply div_nonneg
    · exact log_nonneg (ratio_one_le (lower_pos hp j a) hg ((min_le_left _ _).trans_lt hUa))
    · linarith
  · exact le_rfl

/-- Every point of the original integration interval is covered, including inactive gates. -/
theorem kernelEndpoint_integral_le {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    (b-a)*kernelEndpoint p j a b ≤ ∫ v in a..b,feedbackLogKernel p j v := by
  have hm := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := kernelEndpoint p j a b))
    (feedback_log_integrable hp j).intervalIntegrable
    (fun v hv => kernelEndpoint_le hp j ha hb hv)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hm

end
end GatedDensityPayment
