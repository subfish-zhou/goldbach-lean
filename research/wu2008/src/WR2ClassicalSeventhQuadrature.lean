import WR2ClassicalSeventhIntegral

noncomputable section
namespace WuPaper.ClassicalSeventh
open Real Set MeasureTheory Finset ClassicalLogRatio Wu08TerminalAlignment

def step : ℝ := (1/3-lowerEndpoint)/256
def point (i : ℕ) : ℝ := lowerEndpoint+step*i

theorem point_bounds {i : ℕ} (hi : i ≤ 256) : point i ∈ Set.Icc lowerEndpoint (1/3) := by
  have h0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have h1 : (i:ℝ) ≤ 256 := by exact_mod_cast hi
  norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,
    Wu2008DoubleSieve.SeventhEighth.alpha,Set.mem_Icc]
  linarith

/-- All numerical hypotheses concern rational values, with the whole-cell error paid. -/
theorem uniform_upper (q : ℕ → ℝ)
    (hq : ∀ i < 256, upperValue ((point i+point (i+1))/2) ≤ q i) :
    seventhMain ≤ 8*(step*(∑ i ∈ range 256, q i)+(256:ℝ)*900*step^3/24) := by
  have hdelta : 0 ≤ step := by
    norm_num [step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]
  have h0 : point 0 = lowerEndpoint := by simp [point]
  have hlast : point 256 = (1:ℝ)/3 := by unfold point step; ring
  have hwidth (i : ℕ) : point (i+1)-point i = step := by
    simp only [point,Nat.cast_add,Nat.cast_one]; ring
  have hstep (i : ℕ) (_hi : i < 256) : point i ≤ point (i+1) := by
    have h := hwidth i
    linarith
  have hsub (i : ℕ) (hi : i < 256) {t : ℝ} (ht : t ∈ Set.Icc (point i) (point (i+1))) :
      t ∈ Set.Icc (1/4) (1/3) := domain
    ⟨(point_bounds (by omega : i ≤ 256)).1.trans ht.1,ht.2.trans (point_bounds (by omega : i+1 ≤ 256)).2⟩
  have hm (i : ℕ) (hi : i < 256) : (point i+point (i+1))/2 ∈ Set.Icc (1/4) (1/3) := by
    apply hsub i hi
    constructor <;> linarith only [hstep i hi]
  have h := ClassicalMidpoint.panels_upper hstep
    (fun i hi t ht => kernel_deriv 1 (-2) 0 1
      (by linarith [(hsub i hi ht).1]) (by linarith [(hsub i hi ht).2])
      (by linarith [(hsub i hi ht).2]) (by linarith [(hsub i hi ht).1]))
    (fun i hi t ht => kernelD1_deriv 1 (-2) 0 1
      (by linarith [(hsub i hi ht).1]) (by linarith [(hsub i hi ht).2])
      (by linarith [(hsub i hi ht).2]) (by linarith [(hsub i hi ht).1]))
    (fun i hi t ht => second_bound (hsub i hi ht))
    (fun i hi => kernel_le_upper (hm i hi))
  rw [h0,hlast] at h
  simp_rw [hwidth] at h
  rw [sum_add_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at h
  have hq' := mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi => hq i (mem_range.mp hi))) hdelta
  rw [seventh_integral]
  nlinarith only [h,hq']

end WuPaper.ClassicalSeventh
#print axioms WuPaper.ClassicalSeventh.uniform_upper
