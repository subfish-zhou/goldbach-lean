import SigmaRationalOuterPolePrimitive
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set

/-- Fixed block 0 in ascending coefficient order from the frozen Hermite certificate. -/
def block0 : ℝ[X] := C (1) * X

theorem block0_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block0.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block0.eval t := by
    simp only [block0, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 1 in ascending coefficient order from the frozen Hermite certificate. -/
def block1 : ℝ[X] := C (1)+C (1) * X

theorem block1_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block1.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block1.eval t := by
    simp only [block1, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 2 in ascending coefficient order from the frozen Hermite certificate. -/
def block2 : ℝ[X] := C (2)+C (1) * X

theorem block2_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block2.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block2.eval t := by
    simp only [block2, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 3 in ascending coefficient order from the frozen Hermite certificate. -/
def block3 : ℝ[X] := C (3)+C (1) * X

theorem block3_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block3.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block3.eval t := by
    simp only [block3, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 4 in ascending coefficient order from the frozen Hermite certificate. -/
def block4 : ℝ[X] := C (((63/17)+(-8/17)*TerminalE.radical))+C (1) * X

theorem block4_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block4.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hc0 : (0:ℝ) < ((63/17)+(-8/17)*TerminalE.radical) := by linarith [TerminalE.radical_lt_four]
  have hp : 0 < block4.eval t := by
    simp only [block4, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 5 in ascending coefficient order from the frozen Hermite certificate. -/
def block5 : ℝ[X] := C (((63/17)+(8/17)*TerminalE.radical))+C (1) * X

theorem block5_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block5.eval t) ≠ 0 := by
  have hr := TerminalE.radical_pos
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block5.eval t := by
    simp only [block5, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 6 in ascending coefficient order from the frozen Hermite certificate. -/
def block6 : ℝ[X] := C (5)+C (1) * X

theorem block6_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block6.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block6.eval t := by
    simp only [block6, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 7 in ascending coefficient order from the frozen Hermite certificate. -/
def block7 : ℝ[X] := C ((9+-2*TerminalE.radical))+C (1) * X

theorem block7_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block7.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hc0 : (0:ℝ) < (9+-2*TerminalE.radical) := by linarith [TerminalE.radical_lt_four]
  have hp : 0 < block7.eval t := by
    simp only [block7, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 8 in ascending coefficient order from the frozen Hermite certificate. -/
def block8 : ℝ[X] := C ((9+2*TerminalE.radical))+C (1) * X

theorem block8_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block8.eval t) ≠ 0 := by
  have hr := TerminalE.radical_pos
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block8.eval t := by
    simp only [block8, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 9 in ascending coefficient order from the frozen Hermite certificate. -/
def block9 : ℝ[X] := C (11)+C (1) * X

theorem block9_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block9.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block9.eval t := by
    simp only [block9, eval_add, eval_mul, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 10 in ascending coefficient order from the frozen Hermite certificate. -/
def block10 : ℝ[X] := C (-6)+C (-6) * X+C (1) * X^2

theorem block10_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block10.eval t) ≠ 0 := by
  have h := SigmaRationalOuterFTC.outerQ_pos ht
  have he : block10.eval t = -SigmaRationalOuterFTC.outerQ t := by
    simp [block10, SigmaRationalOuterFTC.outerQ]
    ring
  rw [he]
  exact neg_ne_zero.mpr h.ne'

/-- Fixed block 11 in ascending coefficient order from the frozen Hermite certificate. -/
def block11 : ℝ[X] := C (8)+C (7) * X+C (1) * X^2

theorem block11_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block11.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block11.eval t := by
    simp only [block11, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 12 in ascending coefficient order from the frozen Hermite certificate. -/
def block12 : ℝ[X] := C (12)+C (11) * X+C (1) * X^2

theorem block12_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block12.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block12.eval t := by
    simp only [block12, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 13 in ascending coefficient order from the frozen Hermite certificate. -/
def block13 : ℝ[X] := C (((1677/77)+(-360/77)*TerminalE.radical))+C (((12582/1309)+(-1880/1309)*TerminalE.radical)) * X+C (1) * X^2

theorem block13_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block13.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hc0 : (0:ℝ) < ((1677/77)+(-360/77)*TerminalE.radical) := by linarith [TerminalE.radical_lt_four]
  have hc1 : (0:ℝ) < ((12582/1309)+(-1880/1309)*TerminalE.radical) := by linarith [TerminalE.radical_lt_four]
  have hp : 0 < block13.eval t := by
    simp only [block13, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 14 in ascending coefficient order from the frozen Hermite certificate. -/
def block14 : ℝ[X] := C (((1677/77)+(360/77)*TerminalE.radical))+C (((12582/1309)+(1880/1309)*TerminalE.radical)) * X+C (1) * X^2

theorem block14_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block14.eval t) ≠ 0 := by
  have hr := TerminalE.radical_pos
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block14.eval t := by
    simp only [block14, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 15 in ascending coefficient order from the frozen Hermite certificate. -/
def block15 : ℝ[X] := C (24)+C (23) * X+C (1) * X^2

theorem block15_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block15.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block15.eval t := by
    simp only [block15, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 16 in ascending coefficient order from the frozen Hermite certificate. -/
def block16 : ℝ[X] := C ((480/7))+C (120) * X+C ((487/7)) * X^2+C ((106/7)) * X^3+C (1) * X^4

theorem block16_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block16.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block16.eval t := by
    simp only [block16, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 17 in ascending coefficient order from the frozen Hermite certificate. -/
def block17 : ℝ[X] := C (114)+C (216) * X+C (127) * X^2+C (22) * X^3+C (1) * X^4

theorem block17_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block17.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block17.eval t := by
    simp only [block17, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 18 in ascending coefficient order from the frozen Hermite certificate. -/
def block18 : ℝ[X] := C (174)+C (336) * X+C (187) * X^2+C (22) * X^3+C (1) * X^4

theorem block18_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block18.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block18.eval t := by
    simp only [block18, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 19 in ascending coefficient order from the frozen Hermite certificate. -/
def block19 : ℝ[X] := C (354)+C (696) * X+C (367) * X^2+C (22) * X^3+C (1) * X^4

theorem block19_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block19.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block19.eval t := by
    simp only [block19, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 20 in ascending coefficient order from the frozen Hermite certificate. -/
def block20 : ℝ[X] := C (1440)+C (2760) * X+C (1441) * X^2+C (118) * X^3+C (1) * X^4

theorem block20_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block20.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block20.eval t := by
    simp only [block20, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 21 in ascending coefficient order from the frozen Hermite certificate. -/
def block21 : ℝ[X] := C ((97452/7))+C ((369216/7)) * X+C ((566844/7)) * X^2+C (64200) * X^3+C (27781) * X^4+C ((45020/7)) * X^5+C ((5286/7)) * X^6+C (44) * X^7+C (1) * X^8

theorem block21_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block21.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block21.eval t := by
    simp only [block21, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

/-- Fixed block 22 in ascending coefficient order from the frozen Hermite certificate. -/
def block22 : ℝ[X] := C (313236)+C (1231488) * X+C (1859892) * X^2+C (1317000) * X^3+C (416581) * X^4+C (43460) * X^5+C (2298) * X^6+C (44) * X^7+C (1) * X^8

theorem block22_eval_ne {t : ℝ} (ht : t ∈ Icc 1 3) : (block22.eval t) ≠ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hp : 0 < block22.eval t := by
    simp only [block22, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    positivity
  exact hp.ne'

end SigmaHermiteActualFTC
