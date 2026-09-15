import SigmaActualBlockSeparable15
import SigmaActualPrimitiveTools

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC Set

def residueNumerator15 : ℝ[X] := C (2795622945448517/6263845664494320)+C (148536839/385786800)*X^1

theorem residueNumerator15_degree : residueNumerator15.degree < block15.degree := by
  have hb : block15.degree = (2 : ℕ) := by
    unfold block15
    compute_degree; all_goals norm_num
  rw [hb]
  unfold residueNumerator15
  compute_degree; all_goals norm_num

def simplePartPrimitive15 : ℝ → ℝ :=
  SigmaSimpleResiduePrimitive.simplePrimitive residueNumerator15 block15

theorem simplePartPrimitive15_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt simplePartPrimitive15 (residueNumerator15.eval t / block15.eval t) t :=
  SigmaSimpleResiduePrimitive.simplePrimitive_deriv _ _ block15_separable
    residueNumerator15_degree t (block15_eval_ne ht)

def principalNumerator23 : ℝ[X] := C (17677381714937753/1304967846769650)+C (206458531618559/260993569353930)*X^1
def principalPrimitive23 (t : ℝ) : ℝ := principalNumerator23.eval t / (block15.eval t)^1
def principalKernel23 (t : ℝ) : ℝ :=
  (principalNumerator23.derivative.eval t * block15.eval t -
    1*principalNumerator23.eval t*block15.derivative.eval t) / (block15.eval t)^2

theorem principalPrimitive23_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive23 (principalKernel23 t) t := by
  convert rationalPrimitive_deriv principalNumerator23 block15 0 t (block15_eval_ne ht) using 1 <;> first | rfl | norm_num [principalKernel23]

def principalNumerator24 : ℝ[X] := C (-182363071457822/167432364225)+C (-763091222978/3416987025)*X^1
def principalPrimitive24 (t : ℝ) : ℝ := principalNumerator24.eval t / (block15.eval t)^2
def principalKernel24 (t : ℝ) : ℝ :=
  (principalNumerator24.derivative.eval t * block15.eval t -
    2*principalNumerator24.eval t*block15.derivative.eval t) / (block15.eval t)^3

theorem principalPrimitive24_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive24 (principalKernel24 t) t := by
  exact rationalPrimitive_deriv principalNumerator24 block15 1 t (block15_eval_ne ht)

def principalNumerator25 : ℝ[X] := C (7445085461024/386679825)+C (970711791904/55239975)*X^1
def principalPrimitive25 (t : ℝ) : ℝ := principalNumerator25.eval t / (block15.eval t)^3
def principalKernel25 (t : ℝ) : ℝ :=
  (principalNumerator25.derivative.eval t * block15.eval t -
    3*principalNumerator25.eval t*block15.derivative.eval t) / (block15.eval t)^4

theorem principalPrimitive25_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt principalPrimitive25 (principalKernel25 t) t := by
  exact rationalPrimitive_deriv principalNumerator25 block15 2 t (block15_eval_ne ht)

end SigmaActualBlockSeparable
