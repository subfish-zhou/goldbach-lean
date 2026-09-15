import Hf4ActualPublic

noncomputable section
namespace Wu04Source
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open OriginalProfileSigmaPayment
open scoped Interval BigOperators

/-- Wu 2004, definitions immediately before (3.21). -/
def paperSigma (a b c : ℝ) : ℝ := ∫ v in a..b, log (c/(v-1))/v

def paperSigma0 (t : ℝ) : ℝ := paperSigma 3 (t+2) (t+1)/(1-paperSigma 3 5 4)
def alpha2 (S : ℝ) : ℝ := S-2
def alpha3 (s S : ℝ) : ℝ := S-S/s-1

/-- Literal three-term Xi1 from Wu 2004 Proposition 3, (3.21). -/
def xi1 (t s S : ℝ) : ℝ :=
  paperSigma0 t/(2*t)*log (16/((s-1)*(S-1)))+
  (Icc (alpha2 S) 3).indicator (fun _ => (1:ℝ)) t/(2*t)*
    log ((t+1)^2/((s-1)*(S-1)))+
  (Icc (alpha3 s S) (alpha2 S)).indicator (fun _ => (1:ℝ)) t/(2*t)*
    log ((t+1)/((s-1)*(S-1-t)))

theorem paperSigma_eq (a b c : ℝ) : paperSigma a b c = NodeExtension.sigma a b c := rfl
theorem paperSigma0_eq (t : ℝ) : paperSigma0 t = NodeExtension.sigma0 t := rfl

def terminalKernel (t : ℝ) : ℝ := NodeExtension.sigma0 t/t*log 2+log ((t+1)/2)/t

theorem xi1_terminal {t : ℝ} (ht : t ∈ Icc 1 3) : xi1 t 3 3 = terminalKernel t := by
  have h1 : (Icc (1:ℝ) 3).indicator (fun _ => (1:ℝ)) t = 1 := indicator_of_mem ht _
  have hs : (Icc (1:ℝ) 1).indicator (fun _ => (1:ℝ)) t/(2*t)*
      log ((t+1)/(2*(2-t))) = 0 := by
    by_cases he : t = 1
    · subst t
      norm_num
    · rw [indicator_of_notMem]
      · simp
      · intro hh
        apply he
        linarith only [hh.1,hh.2]
  have hf : xi1 t 3 3 = NodeExtension.sigma0 t/(2*t)*log 4+
      1/(2*t)*log ((t+1)^2/4)+
      (Icc (1:ℝ) 1).indicator (fun _ => (1:ℝ)) t/(2*t)*log ((t+1)/(2*(2-t))) := by
    norm_num [xi1,alpha2,alpha3,paperSigma0_eq,h1]
  have hl4 : log (4:ℝ) = 2*log 2 := by
    calc
      _ = log ((2:ℝ)^2) := congrArg log (by norm_num)
      _ = _ := Real.log_pow _ _
  have he : (t+1)^2/(4:ℝ) = ((t+1)/2)^2 := by ring
  have hl : log ((t+1)^2/(4:ℝ)) = 2*log ((t+1)/2) := by
    rw [he]
    exact Real.log_pow _ _
  rw [hf,hs,add_zero,hl4,hl]
  unfold terminalKernel
  ring

theorem sigmaWeight_continuous : ContinuousOn (fun t : ℝ => sigma0 t/t) (uIcc 1 3) := by
  apply (original_sigma_continuous.div_const (1-D0)).div continuousOn_id
  intro t ht
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht
  change t ≠ 0
  linarith only [ht.1]

theorem logWeight_continuous : ContinuousOn (fun t : ℝ => log ((t+1)/2)/t) (uIcc 1 3) := by
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

theorem terminalKernel_continuous : ContinuousOn terminalKernel (uIcc 1 3) :=
  (sigmaWeight_continuous.mul_const (log 2)).add logWeight_continuous

theorem firstFeedback_eq_kernel (z : Fin 9 → ℝ) :
    firstFeedback z 3 3 = ∫ t in (1:ℝ)..3, nineProfile z t*terminalKernel t := by
  have hp := nineProfile_integrable z
  have ha : IntervalIntegrable (fun t => nineProfile z t*sigma0 t/t) volume 1 3 := by
    convert hp.mul_continuousOn sigmaWeight_continuous using 1
    ext t
    ring
  have hb : IntervalIntegrable (fun t => nineProfile z t/t*log ((t+1)/2)) volume 1 3 := by
    convert hp.mul_continuousOn logWeight_continuous using 1
    ext t
    ring
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  unfold eProfile aProfile
  norm_num only [show (3:ℝ)-1=2 by norm_num,show (3:ℝ)-2=1 by norm_num,
    show (4:ℝ)/2=2 by norm_num]
  have he : (fun t => nineProfile z t*terminalKernel t) =
      (fun t => nineProfile z t*sigma0 t/t*log 2+nineProfile z t/t*log ((t+1)/2)) := by
    ext t
    unfold terminalKernel
    ring
  rw [he,intervalIntegral.integral_add (ha.mul_const (log 2)) hb,intervalIntegral.integral_mul_const]

theorem firstFeedback_eq_paper_integral (z : Fin 9 → ℝ) :
    firstFeedback z 3 3 = ∫ t in (1:ℝ)..3, nineProfile z t*xi1 t 3 3 := by
  rw [firstFeedback_eq_kernel]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht
  dsimp only
  rw [xi1_terminal ht]

end Wu04Source
