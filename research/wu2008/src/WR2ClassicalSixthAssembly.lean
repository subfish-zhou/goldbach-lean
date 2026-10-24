import WR2ClassicalSixthQuadrature
import WR2ClassicalSixthIntegral
import WR2ClassicalSixthRational

noncomputable section
namespace WuPaper.ClassicalSixthAssembly
open Real Set Finset
open WuSource.SrcSixthGain ClassicalSixthBranch ClassicalSixthKernel
open ClassicalSixthQuadrature ClassicalSixthRational

theorem midpoint_mem {a b : ℝ} (hab : a ≤ b) {i : ℕ} (hi : i < 4096) :
    (point a b 4096 i+point a b 4096 (i+1))/2 ∈ Icc a b := by
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have hiR : (i:ℝ) ≤ 4095 := by exact_mod_cast (show i ≤ 4095 by omega)
  have ht0 : 0 ≤ (2*(i:ℝ)+1)/8192 := by positivity
  have ht1 : (2*(i:ℝ)+1)/8192 ≤ 1 := by linarith
  have h0 := mul_nonneg (sub_nonneg.mpr hab) ht0
  have h1 := mul_le_mul_of_nonneg_left ht1 (sub_nonneg.mpr hab)
  have he : (point a b 4096 i+point a b 4096 (i+1))/2 = a+(b-a)*((2*(i:ℝ)+1)/8192) := by
    simp only [point,step,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  rw [he]
  constructor <;> linarith

/-- Only the two finite midpoint families and their sums remain numerical obligations. -/
theorem sixth_lower_of_payments (ql qu : ℕ → ℝ)
    (hql : ∀ i < 4096, ql i ≤ lowerValue ((point 2 split 4096 i+point 2 split 4096 (i+1))/2))
    (hqu : ∀ i < 4096, qu i ≤ upperValue ((point split endpoint 4096 i+point split endpoint 4096 (i+1))/2))
    (hsl : (939922834048256:ℝ)/1000000000000 ≤ ∑ i ∈ range 4096, ql i)
    (hsu : (1025832247091325:ℝ)/1000000000000 ≤ ∑ i ∈ range 4096, qu i) :
    (381909:ℝ)/100000 ≤ Wu08TerminalAlignment.sixthMain := by
  have h2 : (2:ℝ) ≤ split := by norm_num [split,QuarterTrim.alpha,QuarterTrim.beta]
  have he : split ≤ endpoint := by norm_num [split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
  have hl := uniform_lower (by norm_num : 0 < (4096:ℕ)) le_rfl he h2
    (fun s hs => ClassicalSixthBranch.lower_deriv (hs.2.trans he))
    (fun s hs => ClassicalSixthBranch.lowerD1_deriv (hs.2.trans he))
    (fun s hs => ClassicalSixthBranch.lower_bounds hs.2)
    (fun s hs => (derivative_bounds (hs.2.trans he)).1)
    (fun s hs => (derivative_bounds (hs.2.trans he)).2.2.1) ql
    (fun i hi => (hql i hi).trans (lower_value_le (midpoint_mem h2 hi).1 (midpoint_mem h2 hi).2))
  have hu := uniform_lower (by norm_num : 0 < (4096:ℕ)) h2 le_rfl he
    (fun s hs => ClassicalSixthBranch.upper_deriv hs.2)
    (fun s hs => ClassicalSixthBranch.upperD1_deriv hs.2)
    (fun s hs => ClassicalSixthBranch.upper_bounds hs.1 hs.2)
    (fun s hs => (derivative_bounds hs.2).2.1)
    (fun s hs => (derivative_bounds hs.2).2.2.2) qu
    (fun i hi => (hqu i hi).trans (upper_value_le (midpoint_mem he hi).1 (midpoint_mem he hi).2))
  have hwl := mul_le_mul_of_nonneg_left hsl (show 0 ≤ step 2 split 4096 by
    exact div_nonneg (sub_nonneg.mpr h2) (by norm_num))
  have hwu := mul_le_mul_of_nonneg_left hsu (show 0 ≤ step split endpoint 4096 by
    exact div_nonneg (sub_nonneg.mpr he) (by norm_num))
  have h := ClassicalSixthIntegral.sixth_lower
  norm_num [step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta] at hl hu hwl hwu h
  linarith only [hl,hu,hwl,hwu,h]

end WuPaper.ClassicalSixthAssembly
#print axioms WuPaper.ClassicalSixthAssembly.sixth_lower_of_payments
