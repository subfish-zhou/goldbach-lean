import WR2ClassicalSixthKernel

noncomputable section
namespace WuPaper.ClassicalSixthQuadrature
open Real Set MeasureTheory Finset
open WuSource.SrcSixthGain ClassicalSixthKernel

def step (a b : ℝ) (n : ℕ) : ℝ := (b-a)/n
def point (a b : ℝ) (n i : ℕ) : ℝ := a+step a b n*i

/-- Uniform midpoint lower bound; the hypotheses distinguish the two smooth branches. -/
theorem uniform_lower {L L1 L2 : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (ha : 2 ≤ a) (hb : b ≤ endpoint) (hab : a ≤ b)
    (hd : ∀ s ∈ Icc a b, HasDerivAt L (L1 s) s)
    (hd1 : ∀ s ∈ Icc a b, HasDerivAt L1 (L2 s) s)
    (hL : ∀ s ∈ Icc a b, |L s| ≤ 2)
    (hL1 : ∀ s ∈ Icc a b, |L1 s| ≤ 2)
    (hL2 : ∀ s ∈ Icc a b, |L2 s| ≤ 2)
    (q : ℕ → ℝ)
    (hq : ∀ i < n, q i ≤ kernel L ((point a b n i+point a b n (i+1))/2)) :
    step a b n*(∑ i ∈ range n, q i)-(n:ℝ)*26*(step a b n)^3/24 ≤
      ∫ s in a..b, kernel L s := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hstep : 0 ≤ step a b n := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  have h0 : point a b n 0 = a := by simp [point]
  have hlast : point a b n n = b := by unfold point step; field_simp; ring
  have hx (i : ℕ) (hi : i ≤ n) : point a b n i ∈ Icc a b := by
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have hin : (i:ℝ) ≤ n := by exact_mod_cast hi
    have htop : step a b n*(n:ℝ) = b-a := by unfold step; exact div_mul_cancel₀ _ hn0
    constructor
    · dsimp [point]; linarith [mul_nonneg hstep hi0]
    · have h := mul_le_mul_of_nonneg_left hin hstep
      dsimp [point]; linarith
  have hwidth (i : ℕ) : point a b n (i+1)-point a b n i = step a b n := by
    simp only [point,Nat.cast_add,Nat.cast_one]
    ring
  have horder (i : ℕ) : point a b n i ≤ point a b n (i+1) := by linarith [hwidth i]
  have hsub (i : ℕ) (hi : i < n) : Icc (point a b n i) (point a b n (i+1)) ⊆ Icc a b :=
    fun _ ht => ⟨(hx i (by omega)).1.trans ht.1,ht.2.trans (hx (i+1) hi).2⟩
  have hr (s : ℝ) (hs : s ∈ Icc a b) : ClassicalSixthWeight.R-s ≠ 0 := by
    have hh := hs.2.trans hb
    norm_num [ClassicalSixthWeight.R,endpoint,QuarterTrim.alpha,QuarterTrim.beta] at hh ⊢
    linarith
  have hf (s : ℝ) (hs : s ∈ Icc a b) := kernel_deriv (ha.trans hs.1) (hr s hs) (hd s hs)
  have hf1 (s : ℝ) (hs : s ∈ Icc a b) := first_deriv (ha.trans hs.1) (hr s hs) (hd s hs) (hd1 s hs)
  have hi (i : ℕ) (hin : i < n) :
      IntervalIntegrable (kernel L) volume (point a b n i) (point a b n (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (horder i)]
    exact fun s hs => (hf s (hsub i hin hs)).continuousAt.continuousWithinAt
  have hp (i : ℕ) (hin : i < n) :
      step a b n*q i-26*(step a b n)^3/24 ≤
        ∫ s in point a b n i..point a b n (i+1), kernel L s := by
    have hm := (WuSource.SrcFourEnclosure.midpoint_cell (horder i)
      (fun s hs => hf s (hsub i hin hs))
      (fun s hs => hf1 s (hsub i hin hs))
      (fun s hs => second_abs_le (ha.trans (hsub i hin hs).1) ((hsub i hin hs).2.trans hb)
        (hL s (hsub i hin hs)) (hL1 s (hsub i hin hs)) (hL2 s (hsub i hin hs)))).1
    rw [hwidth] at hm
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left (hq i hin) hstep) _).trans hm
  have hh := sum_le_sum (fun i hi => hp i (mem_range.mp hi))
  rw [intervalIntegral.sum_integral_adjacent_intervals hi,h0,hlast] at hh
  simp only [sum_sub_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at hh
  linarith only [hh]

end WuPaper.ClassicalSixthQuadrature
#print axioms WuPaper.ClassicalSixthQuadrature.uniform_lower
