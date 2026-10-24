import WR2ClassicalNinthIntegral

noncomputable section
namespace WuPaper.ClassicalNinth
open Wu2008DoubleSieve Real Set MeasureTheory Finset ClassicalLogRatio Wu08TerminalAlignment

def step : ℝ := (upperEndpoint-lowerEndpoint)/512
def point (i : ℕ) : ℝ := lowerEndpoint+step*i

theorem point_bounds {i : ℕ} (hi : i ≤ 512) : point i ∈ Set.Icc lowerEndpoint upperEndpoint := by
  have h0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have h1 : (i:ℝ) ≤ 512 := by exact_mod_cast hi
  norm_num [point,step,lowerEndpoint,upperEndpoint,ninthProfileSigma,ninthProfileK1,ninthProfileK2,Set.mem_Icc]
  linarith

/-- All numerical hypotheses concern rational values, with the whole-cell error paid. -/
theorem uniform_upper (q : ℕ → ℝ)
    (hq : ∀ i < 512, upperValue ((point i+point (i+1))/2) ≤ q i) :
    ninthMain ≤ 8*(step*(∑ i ∈ range 512, q i)+(512:ℝ)*1900*step^3/24) := by
  have hdelta : 0 ≤ step := by
    norm_num [step,lowerEndpoint,upperEndpoint,ninthProfileSigma,ninthProfileK1,ninthProfileK2]
  have h0 : point 0 = lowerEndpoint := by simp [point]
  have hlast : point 512 = upperEndpoint := by unfold point step; ring
  have hwidth (i : ℕ) : point (i+1)-point i = step := by
    simp only [point,Nat.cast_add,Nat.cast_one]; ring
  have hstep (i : ℕ) (_hi : i < 512) : point i ≤ point (i+1) := by
    have h := hwidth i
    linarith
  have hsub (i : ℕ) (hi : i < 512) {t : ℝ} (ht : t ∈ Set.Icc (point i) (point (i+1))) :
      t ∈ Set.Icc (3/25) (3/10) := domain
    ⟨(point_bounds (by omega : i ≤ 512)).1.trans ht.1,ht.2.trans (point_bounds (by omega : i+1 ≤ 512)).2⟩
  have hm (i : ℕ) (hi : i < 512) : (point i+point (i+1))/2 ∈ Set.Icc (3/25) (3/10) := by
    apply hsub i hi
    constructor <;> linarith only [hstep i hi]
  have h := ClassicalMidpoint.panels_upper hstep
    (fun i hi t ht => kernel_deriv (1-upperEndpoint) (-1) upperEndpoint 0
      (by linarith [(hsub i hi ht).1]) (by linarith [(hsub i hi ht).2])
      (by linarith [(hsub i hi ht).2,sigma_bounds.2]) (by linarith [sigma_bounds.1] ))
    (fun i hi t ht => kernelD1_deriv (1-upperEndpoint) (-1) upperEndpoint 0
      (by linarith [(hsub i hi ht).1]) (by linarith [(hsub i hi ht).2])
      (by linarith [(hsub i hi ht).2,sigma_bounds.2]) (by linarith [sigma_bounds.1] ))
    (fun i hi t ht => second_bound sigma_bounds (hsub i hi ht))
    (fun i hi => kernel_le_upper (hm i hi))
  rw [h0,hlast] at h
  simp_rw [hwidth] at h
  rw [sum_add_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at h
  have hq' := mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi => hq i (mem_range.mp hi))) hdelta
  rw [ninth_integral]
  nlinarith only [h,hq']

end WuPaper.ClassicalNinth
#print axioms WuPaper.ClassicalNinth.uniform_upper
