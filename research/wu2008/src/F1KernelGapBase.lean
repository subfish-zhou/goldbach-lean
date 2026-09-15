import F1PaymentExtent

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence FirstIntegralRecovery
open F1FullRecoveryPayment
namespace F1RemainingRecovery

/-- The already proved payment, in the literal first split factor of the C kernel. -/
theorem first_factor_payment {u : ℝ} (hu : 2 ≤ u) :
    (u-2)^5/((u+2)^3*(u^2+16*u+4)) ≤ log (u-1)-splitL (u-1) := by
  have hx : 1 ≤ u-1 := by linarith
  have h1 := lowerGapPayment_le (show (1:ℝ) ≤ (1+(u-1))/2 by linarith)
  have h2 := log_lower (split_arguments hx).2
  have hid := split_log_identity hx
  have hu2 : u+2 ≠ 0 := by linarith
  have hq : u^2+16*u+4 ≠ 0 := by positivity
  have hu0 : u ≠ 0 := by linarith
  have hp : lowerGapPayment ((1+(u-1))/2) =
      (u-2)^5/((u+2)^3*(u^2+16*u+4)) := by
    dsimp [lowerGapPayment,upperLog,lowerLog]
    field_simp
    ring
  rw [hp] at h1
  unfold splitL
  linarith only [h1,h2,hid]

/-- A paying linear numerator on the original triangular projection. -/
theorem ratio_log_payment {s u : ℝ} (hu : u ∈ Icc 2 (s-2)) :
    2*(s-2-u)/(s+u) ≤ log ((s-1)/(u+1)) := by
  have hr := ratio_ge_one hu
  have h := log_lower hr
  have hpos : 0 ≤ (((s-1)/(u+1)-1)/((s-1)/(u+1)+1)) :=
    div_nonneg (by linarith) (by linarith)
  have hlin : 2*(((s-1)/(u+1)-1)/((s-1)/(u+1)+1)) =
      2*(s-2-u)/(s+u) := by
    have hn : u+1 ≠ 0 := by linarith [hu.1]
    have hs : s+u ≠ 0 := by linarith [hu.1,hu.2]
    field_simp [hn,hs]
    ring
  unfold lowerLog at h
  rw [← hlin]
  linarith only [h,show 0 ≤ 2*(((s-1)/(u+1)-1)/((s-1)/(u+1)+1))^3/3 by positivity]

/-- A literal nonzero rational portion of the original kernel recovery. -/
theorem exact_kernel_payment {s u : ℝ} (hu : u ∈ Icc 2 (s-2)) :
    ((u-2)^5/((u+2)^3*(u^2+16*u+4)))/u * (2*(s-2-u)/(s+u)) ≤
      cExactKernel s u-cLowerKernel s u := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hp := first_factor_payment hu.1
  have hl := ratio_log_payment hu
  have hfirst : 0 ≤ (u-2)^5/((u+2)^3*(u^2+16*u+4)) := by
    apply div_nonneg (pow_nonneg (by linarith [hu.1]) _) (by positivity)
  have hratio : 0 ≤ log ((s-1)/(u+1)) := log_nonneg (ratio_ge_one hu)
  have hlower : splitL ((s-1)/(u+1)) ≤ log ((s-1)/(u+1)) :=
    splitL_le_log (ratio_ge_one hu)
  have hsl : 0 ≤ splitL (u-1)/u := div_nonneg (splitL_nonneg (by linarith [hu.1])) (by linarith [hu.1])
  have hprod := mul_le_mul
    (div_le_div_of_nonneg_right hp hu0) hl
    (by apply div_nonneg (by linarith [hu.2]) (by linarith [hu.1,hu.2]))
    (div_nonneg (sub_nonneg.mpr (splitL_le_log (by linarith [hu.1]))) hu0)
  have hrest := mul_le_mul_of_nonneg_left hlower hsl
  dsimp [cExactKernel,cLowerKernel]
  have hdist : (log (u-1)-splitL (u-1))/u*log ((s-1)/(u+1)) =
      log (u-1)/u*log ((s-1)/(u+1))-splitL (u-1)/u*log ((s-1)/(u+1)) := by ring
  rw [hdist] at hprod
  linarith only [hprod,hrest]

end F1RemainingRecovery
