import SigmaActualPrimitiveBlock0
import SigmaActualPrimitiveBlock1
import SigmaActualPrimitiveBlock2
import SigmaActualPrimitiveBlock3
import SigmaActualPrimitiveBlock4
import SigmaActualPrimitiveBlock5
import SigmaActualPrimitiveBlock6
import SigmaActualPrimitiveBlock7
import SigmaActualPrimitiveBlock8
import SigmaActualPrimitiveBlock9
import SigmaActualPrimitiveBlock10
import SigmaActualPrimitiveBlock11
import SigmaActualPrimitiveBlock12
import SigmaActualPrimitiveBlock13
import SigmaActualPrimitiveBlock14
import SigmaActualPrimitiveBlock15
import SigmaActualPrimitiveBlock16
import SigmaActualPrimitiveBlock17
import SigmaActualPrimitiveBlock18
import SigmaActualPrimitiveBlock19
import SigmaActualPrimitiveBlock20
import SigmaActualPrimitiveBlock21
import SigmaActualPrimitiveBlock22

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC


theorem block1_derivative_eval (t : ℝ) : block1.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block1, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

theorem block2_derivative_eval (t : ℝ) : block2.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block2, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

theorem block3_derivative_eval (t : ℝ) : block3.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block3, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

theorem block4_derivative_eval (t : ℝ) : block4.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block4, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

theorem block5_derivative_eval (t : ℝ) : block5.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block5, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

theorem block6_derivative_eval (t : ℝ) : block6.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block6, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

theorem block7_derivative_eval (t : ℝ) : block7.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block7, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

theorem block8_derivative_eval (t : ℝ) : block8.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block8, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

theorem block9_derivative_eval (t : ℝ) : block9.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block9, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring


theorem block11_derivative_eval (t : ℝ) : block11.derivative.eval t = (1:ℝ)*(7)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block11, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block12_derivative_eval (t : ℝ) : block12.derivative.eval t = (1:ℝ)*(11)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block12, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring



theorem block15_derivative_eval (t : ℝ) : block15.derivative.eval t = (1:ℝ)*(23)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block15, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring


theorem block17_derivative_eval (t : ℝ) : block17.derivative.eval t = (1:ℝ)*(216)*t^0+(2:ℝ)*(127)*t^1+(3:ℝ)*(22)*t^2+(4:ℝ)*(1)*t^3 := by
  simp only [block17, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block18_derivative_eval (t : ℝ) : block18.derivative.eval t = (1:ℝ)*(336)*t^0+(2:ℝ)*(187)*t^1+(3:ℝ)*(22)*t^2+(4:ℝ)*(1)*t^3 := by
  simp only [block18, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block19_derivative_eval (t : ℝ) : block19.derivative.eval t = (1:ℝ)*(696)*t^0+(2:ℝ)*(367)*t^1+(3:ℝ)*(22)*t^2+(4:ℝ)*(1)*t^3 := by
  simp only [block19, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring




end SigmaActualBlockSeparable
