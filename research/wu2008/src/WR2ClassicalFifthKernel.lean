import WR2ClassicalFifthProfile
import WR2ClassicalFifthBranch

noncomputable section
namespace WuPaper.ClassicalFifthKernel
open Real
open ClassicalFourth

def inner (L : ℝ → ℝ) (s : ℝ) : ℝ := L s*weight s
def innerFirst (L L1 : ℝ → ℝ) (s : ℝ) : ℝ := L1 s*weight s+L s*weightD1 s
def innerSecond (L L1 L2 : ℝ → ℝ) (s : ℝ) : ℝ :=
  L2 s*weight s+2*L1 s*weightD1 s+L s*weightD2 s

def kernel (A L : ℝ → ℝ) (s : ℝ) : ℝ := A s*inner L s
def first (A A1 L L1 : ℝ → ℝ) (s : ℝ) : ℝ := A1 s*inner L s+A s*innerFirst L L1 s
def second (A A1 A2 L L1 L2 : ℝ → ℝ) (s : ℝ) : ℝ :=
  A2 s*inner L s+2*A1 s*innerFirst L L1 s+A s*innerSecond L L1 L2 s

theorem second_abs_le {A A1 A2 L L1 L2 : ℝ → ℝ} {s : ℝ}
    (hs : 3 ≤ s) (he : s ≤ ClassicalFourth.R-1)
    (hA : |A s| ≤ 3) (hA1 : |A1 s| ≤ 2) (hA2 : |A2 s| ≤ 2)
    (hL : |L s| ≤ 1) (hL1 : |L1 s| ≤ 1) (hL2 : |L2 s| ≤ 1) :
    |second A A1 A2 L L1 L2 s| ≤ 60 := by
  obtain ⟨hw,hw1,hw2⟩ := weight_bounds hs he
  have hi : |inner L s| ≤ (8:ℝ)/3 := by
    unfold inner
    rw [abs_mul]
    simpa using mul_le_mul hL hw (abs_nonneg _) ((abs_nonneg _).trans hL)
  have hi1 : |innerFirst L L1 s| ≤ (44:ℝ)/9 := by
    exact (ClassicalSixthKernel.first_bound hL1 hw hL hw1).trans (by norm_num)
  have hi2 : |innerSecond L L1 L2 s| ≤ (304:ℝ)/27 := by
    exact (ClassicalSixthKernel.second_bound hL2 hw hL1 hw1 hL hw2).trans (by norm_num)
  exact (ClassicalSixthKernel.second_bound hA2 hi hA1 hi1 hA hi2).trans (by norm_num)

theorem inner_deriv {L L1 : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hr : ClassicalFourth.R-s ≠ 0)
    (hL : HasDerivAt L (L1 s) s) : HasDerivAt (inner L) (innerFirst L L1 s) s :=
  hL.mul (weight_deriv hs hr)

theorem innerFirst_deriv {L L1 L2 : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hr : ClassicalFourth.R-s ≠ 0)
    (hL : HasDerivAt L (L1 s) s) (hL1 : HasDerivAt L1 (L2 s) s) :
    HasDerivAt (innerFirst L L1) (innerSecond L L1 L2 s) s := by
  have h := (hL1.mul (weight_deriv hs hr)).add (hL.mul (weightD1_deriv hs hr))
  change HasDerivAt (innerFirst L L1) _ s at h
  apply h.congr_deriv
  dsimp [innerSecond]
  ring

theorem kernel_deriv {A A1 L L1 : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hr : ClassicalFourth.R-s ≠ 0)
    (hA : HasDerivAt A (A1 s) s) (hL : HasDerivAt L (L1 s) s) :
    HasDerivAt (kernel A L) (first A A1 L L1 s) s :=
  hA.mul (inner_deriv hs hr hL)

theorem first_deriv {A A1 A2 L L1 L2 : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hr : ClassicalFourth.R-s ≠ 0)
    (hA : HasDerivAt A (A1 s) s) (hA1 : HasDerivAt A1 (A2 s) s)
    (hL : HasDerivAt L (L1 s) s) (hL1 : HasDerivAt L1 (L2 s) s) :
    HasDerivAt (first A A1 L L1) (second A A1 A2 L L1 L2 s) s := by
  have h := (hA1.mul (inner_deriv hs hr hL)).add (hA.mul (innerFirst_deriv hs hr hL hL1))
  change HasDerivAt (first A A1 L L1) _ s at h
  apply h.congr_deriv
  dsimp [second]
  ring

end WuPaper.ClassicalFifthKernel
#print axioms WuPaper.ClassicalFifthKernel.second_abs_le
#print axioms WuPaper.ClassicalFifthKernel.first_deriv
