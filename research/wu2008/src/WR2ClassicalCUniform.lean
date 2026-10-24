import WR2ClassicalCQuadrature

noncomputable section
namespace WuPaper.ClassicalC
open Real Set Finset Wu08OriginalFirstSteps

def step (s : ℝ) (n : ℕ) : ℝ := (s-4)/n
def point (s : ℝ) (n i : ℕ) : ℝ := 2+step s n*i

theorem uniform_lower {s : ℝ} (hs : 4 ≤ s) (hs7 : s ≤ 7)
    (depth n : ℕ) (hn : 0 < n) (q : ℕ → ℝ)
    (hq : ∀ i < n, q i ≤ lowerKernel depth s ((point s n i+point s n (i+1))/2)) :
    step s n*(∑ i ∈ range n, q i)-(n:ℝ)*8*(step s n)^3/24 ≤ C s := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdelta : 0 ≤ step s n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h0 : point s n 0 = 2 := by simp [point]
  have hlast : point s n n = s-2 := by unfold point step; field_simp; ring
  have hx (i : ℕ) (hi : i ≤ n) : point s n i ∈ Set.Icc 2 (s-2) := by
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have hin : (i:ℝ) ≤ n := by exact_mod_cast hi
    have htop : step s n*(n:ℝ) = s-4 := by unfold step; exact div_mul_cancel₀ _ hn0
    constructor
    · dsimp [point]
      linarith [mul_nonneg hdelta hi0]
    · have h := mul_le_mul_of_nonneg_left hin hdelta
      dsimp [point]
      linarith
  have hwidth (i : ℕ) : point s n (i+1)-point s n i = step s n := by
    simp only [point,Nat.cast_add,Nat.cast_one]
    ring
  have hstep (i : ℕ) (_hi : i < n) : point s n i ≤ point s n (i+1) := by
    have h := hwidth i
    linarith
  have h := (C_enclosure hs hs7 depth n (point s n) h0 hlast hx hstep).1
  simp_rw [hwidth] at h
  rw [sum_sub_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at h
  have hq' := mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi => hq i (mem_range.mp hi))) hdelta
  nlinarith only [h,hq']

end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.uniform_lower
