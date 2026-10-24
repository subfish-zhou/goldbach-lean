import WR2ClassicalEighthCorrection
import U8CanonicalMother

noncomputable section
namespace WuPaper.ClassicalEighthCorrection
open Real Set MeasureTheory Finset

def step : ℝ := (b-a)/512
def point (i : ℕ) : ℝ := a+step*i

theorem point_bounds {i : ℕ} (hi : i ≤ 512) : point i ∈ Icc a b := by
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have hi1 : (i:ℝ) ≤ 512 := by exact_mod_cast hi
  norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b,Set.mem_Icc]
  linarith

theorem uniform_lower (q : ℕ → ℝ)
    (hq : ∀ i < 512, step*q i ≤ cellPayment (point i) (point (i+1))) :
    8*step*(∑ i ∈ range 512, q i) ≤ 8*(U8CanonicalMother.L-U8CanonicalMother.I) := by
  have hs : 0 ≤ step := by
    norm_num [step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
  have h0 : point 0 = a := by simp [point]
  have hn : point 512 = b := by unfold point step; ring
  have hstep (i : ℕ) (_hi : i < 512) : point i ≤ point (i+1) := by
    have he : point (i+1)-point i = step := by
      simp only [point,Nat.cast_add,Nat.cast_one]; ring
    linarith
  have h := panels_lower h0 hn hstep (fun i hi => point_bounds hi) hq
  rw [← mul_sum] at h
  have hid := OriginalU8.SymbolicSmallGain.gain_identity
  change 2*(U8CanonicalMother.L-U8CanonicalMother.I) = 2*∫ t in a..b, gain t at hid
  linarith only [h,hid]

end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.uniform_lower
