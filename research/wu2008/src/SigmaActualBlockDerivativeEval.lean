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

theorem block0_derivative_eval (t : ℝ) : block0.derivative.eval t = (1:ℝ)*(1)*t^0 := by
  simp only [block0, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
  ring

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

theorem block10_derivative_eval (t : ℝ) : block10.derivative.eval t = (1:ℝ)*(-6)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block10, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block11_derivative_eval (t : ℝ) : block11.derivative.eval t = (1:ℝ)*(7)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block11, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block12_derivative_eval (t : ℝ) : block12.derivative.eval t = (1:ℝ)*(11)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block12, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block13_derivative_eval (t : ℝ) : block13.derivative.eval t = (1:ℝ)*((12582/1309)+(-1880/1309)*TerminalE.radical)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block13, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block14_derivative_eval (t : ℝ) : block14.derivative.eval t = (1:ℝ)*((12582/1309)+(1880/1309)*TerminalE.radical)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block14, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block15_derivative_eval (t : ℝ) : block15.derivative.eval t = (1:ℝ)*(23)*t^0+(2:ℝ)*(1)*t^1 := by
  simp only [block15, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block16_derivative_eval (t : ℝ) : block16.derivative.eval t = (1:ℝ)*(120)*t^0+(2:ℝ)*(487/7)*t^1+(3:ℝ)*(106/7)*t^2+(4:ℝ)*(1)*t^3 := by
  simp only [block16, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
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

theorem block20_derivative_eval (t : ℝ) : block20.derivative.eval t = (1:ℝ)*(2760)*t^0+(2:ℝ)*(1441)*t^1+(3:ℝ)*(118)*t^2+(4:ℝ)*(1)*t^3 := by
  simp only [block20, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block21_derivative_eval (t : ℝ) : block21.derivative.eval t = (1:ℝ)*(369216/7)*t^0+(2:ℝ)*(566844/7)*t^1+(3:ℝ)*(64200)*t^2+(4:ℝ)*(27781)*t^3+(5:ℝ)*(45020/7)*t^4+(6:ℝ)*(5286/7)*t^5+(7:ℝ)*(44)*t^6+(8:ℝ)*(1)*t^7 := by
  simp only [block21, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

theorem block22_derivative_eval (t : ℝ) : block22.derivative.eval t = (1:ℝ)*(1231488)*t^0+(2:ℝ)*(1859892)*t^1+(3:ℝ)*(1317000)*t^2+(4:ℝ)*(416581)*t^3+(5:ℝ)*(43460)*t^4+(6:ℝ)*(2298)*t^5+(7:ℝ)*(44)*t^6+(8:ℝ)*(1)*t^7 := by
  simp only [block22, derivative_add, derivative_mul, derivative_C, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one, derivative_pow, eval_pow]
  ring

end SigmaActualBlockSeparable
