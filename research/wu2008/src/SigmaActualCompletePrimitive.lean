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
open Polynomial SigmaHermiteActualFTC Set

def primitiveGroup0 (t : ℝ) : ℝ := principalPrimitive0 t + principalPrimitive1 t + principalPrimitive2 t + principalPrimitive3 t + principalPrimitive4 t + principalPrimitive5 t + principalPrimitive6 t + principalPrimitive7 t
def kernelGroup0 (t : ℝ) : ℝ := principalKernel0 t + principalKernel1 t + principalKernel2 t + principalKernel3 t + principalKernel4 t + principalKernel5 t + principalKernel6 t + principalKernel7 t

theorem primitiveGroup0_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt primitiveGroup0 (kernelGroup0 t) t := by
  have hd0 := principalPrimitive0_deriv ht
  have hd1 := hd0.add (principalPrimitive1_deriv ht)
  have hd2 := hd1.add (principalPrimitive2_deriv ht)
  have hd3 := hd2.add (principalPrimitive3_deriv ht)
  have hd4 := hd3.add (principalPrimitive4_deriv ht)
  have hd5 := hd4.add (principalPrimitive5_deriv ht)
  have hd6 := hd5.add (principalPrimitive6_deriv ht)
  have hd7 := hd6.add (principalPrimitive7_deriv ht)
  exact hd7

def primitiveGroup1 (t : ℝ) : ℝ := principalPrimitive8 t + principalPrimitive9 t + principalPrimitive10 t + principalPrimitive11 t + principalPrimitive12 t + principalPrimitive13 t + principalPrimitive14 t + principalPrimitive15 t
def kernelGroup1 (t : ℝ) : ℝ := principalKernel8 t + principalKernel9 t + principalKernel10 t + principalKernel11 t + principalKernel12 t + principalKernel13 t + principalKernel14 t + principalKernel15 t

theorem primitiveGroup1_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt primitiveGroup1 (kernelGroup1 t) t := by
  have hd0 := principalPrimitive8_deriv ht
  have hd1 := hd0.add (principalPrimitive9_deriv ht)
  have hd2 := hd1.add (principalPrimitive10_deriv ht)
  have hd3 := hd2.add (principalPrimitive11_deriv ht)
  have hd4 := hd3.add (principalPrimitive12_deriv ht)
  have hd5 := hd4.add (principalPrimitive13_deriv ht)
  have hd6 := hd5.add (principalPrimitive14_deriv ht)
  have hd7 := hd6.add (principalPrimitive15_deriv ht)
  exact hd7

def primitiveGroup2 (t : ℝ) : ℝ := principalPrimitive16 t + principalPrimitive17 t + principalPrimitive18 t + principalPrimitive19 t + principalPrimitive20 t + principalPrimitive21 t + principalPrimitive22 t + principalPrimitive23 t
def kernelGroup2 (t : ℝ) : ℝ := principalKernel16 t + principalKernel17 t + principalKernel18 t + principalKernel19 t + principalKernel20 t + principalKernel21 t + principalKernel22 t + principalKernel23 t

theorem primitiveGroup2_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt primitiveGroup2 (kernelGroup2 t) t := by
  have hd0 := principalPrimitive16_deriv ht
  have hd1 := hd0.add (principalPrimitive17_deriv ht)
  have hd2 := hd1.add (principalPrimitive18_deriv ht)
  have hd3 := hd2.add (principalPrimitive19_deriv ht)
  have hd4 := hd3.add (principalPrimitive20_deriv ht)
  have hd5 := hd4.add (principalPrimitive21_deriv ht)
  have hd6 := hd5.add (principalPrimitive22_deriv ht)
  have hd7 := hd6.add (principalPrimitive23_deriv ht)
  exact hd7

def primitiveGroup3 (t : ℝ) : ℝ := principalPrimitive24 t + principalPrimitive25 t + principalPrimitive26 t + principalPrimitive27 t + principalPrimitive28 t + principalPrimitive29 t + principalPrimitive30 t + principalPrimitive31 t
def kernelGroup3 (t : ℝ) : ℝ := principalKernel24 t + principalKernel25 t + principalKernel26 t + principalKernel27 t + principalKernel28 t + principalKernel29 t + principalKernel30 t + principalKernel31 t

theorem primitiveGroup3_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt primitiveGroup3 (kernelGroup3 t) t := by
  have hd0 := principalPrimitive24_deriv ht
  have hd1 := hd0.add (principalPrimitive25_deriv ht)
  have hd2 := hd1.add (principalPrimitive26_deriv ht)
  have hd3 := hd2.add (principalPrimitive27_deriv ht)
  have hd4 := hd3.add (principalPrimitive28_deriv ht)
  have hd5 := hd4.add (principalPrimitive29_deriv ht)
  have hd6 := hd5.add (principalPrimitive30_deriv ht)
  have hd7 := hd6.add (principalPrimitive31_deriv ht)
  exact hd7

def primitiveGroup4 (t : ℝ) : ℝ := principalPrimitive32 t + simplePartPrimitive0 t + simplePartPrimitive1 t + simplePartPrimitive2 t + simplePartPrimitive3 t + simplePartPrimitive4 t + simplePartPrimitive5 t + simplePartPrimitive6 t
def kernelGroup4 (t : ℝ) : ℝ := principalKernel32 t + (residueNumerator0.eval t / block0.eval t) + (residueNumerator1.eval t / block1.eval t) + (residueNumerator2.eval t / block2.eval t) + (residueNumerator3.eval t / block3.eval t) + (residueNumerator4.eval t / block4.eval t) + (residueNumerator5.eval t / block5.eval t) + (residueNumerator6.eval t / block6.eval t)

theorem primitiveGroup4_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt primitiveGroup4 (kernelGroup4 t) t := by
  have hd0 := principalPrimitive32_deriv ht
  have hd1 := hd0.add (simplePartPrimitive0_deriv ht)
  have hd2 := hd1.add (simplePartPrimitive1_deriv ht)
  have hd3 := hd2.add (simplePartPrimitive2_deriv ht)
  have hd4 := hd3.add (simplePartPrimitive3_deriv ht)
  have hd5 := hd4.add (simplePartPrimitive4_deriv ht)
  have hd6 := hd5.add (simplePartPrimitive5_deriv ht)
  have hd7 := hd6.add (simplePartPrimitive6_deriv ht)
  exact hd7

def primitiveGroup5 (t : ℝ) : ℝ := simplePartPrimitive7 t + simplePartPrimitive8 t + simplePartPrimitive9 t + simplePartPrimitive10 t + simplePartPrimitive11 t + simplePartPrimitive12 t + simplePartPrimitive13 t + simplePartPrimitive14 t
def kernelGroup5 (t : ℝ) : ℝ := (residueNumerator7.eval t / block7.eval t) + (residueNumerator8.eval t / block8.eval t) + (residueNumerator9.eval t / block9.eval t) + (residueNumerator10.eval t / block10.eval t) + (residueNumerator11.eval t / block11.eval t) + (residueNumerator12.eval t / block12.eval t) + (residueNumerator13.eval t / block13.eval t) + (residueNumerator14.eval t / block14.eval t)

theorem primitiveGroup5_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt primitiveGroup5 (kernelGroup5 t) t := by
  have hd0 := simplePartPrimitive7_deriv ht
  have hd1 := hd0.add (simplePartPrimitive8_deriv ht)
  have hd2 := hd1.add (simplePartPrimitive9_deriv ht)
  have hd3 := hd2.add (simplePartPrimitive10_deriv ht)
  have hd4 := hd3.add (simplePartPrimitive11_deriv ht)
  have hd5 := hd4.add (simplePartPrimitive12_deriv ht)
  have hd6 := hd5.add (simplePartPrimitive13_deriv ht)
  have hd7 := hd6.add (simplePartPrimitive14_deriv ht)
  exact hd7

def primitiveGroup6 (t : ℝ) : ℝ := simplePartPrimitive15 t + simplePartPrimitive16 t + simplePartPrimitive17 t + simplePartPrimitive18 t + simplePartPrimitive19 t + simplePartPrimitive20 t + simplePartPrimitive21 t + simplePartPrimitive22 t
def kernelGroup6 (t : ℝ) : ℝ := (residueNumerator15.eval t / block15.eval t) + (residueNumerator16.eval t / block16.eval t) + (residueNumerator17.eval t / block17.eval t) + (residueNumerator18.eval t / block18.eval t) + (residueNumerator19.eval t / block19.eval t) + (residueNumerator20.eval t / block20.eval t) + (residueNumerator21.eval t / block21.eval t) + (residueNumerator22.eval t / block22.eval t)

theorem primitiveGroup6_deriv {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt primitiveGroup6 (kernelGroup6 t) t := by
  have hd0 := simplePartPrimitive15_deriv ht
  have hd1 := hd0.add (simplePartPrimitive16_deriv ht)
  have hd2 := hd1.add (simplePartPrimitive17_deriv ht)
  have hd3 := hd2.add (simplePartPrimitive18_deriv ht)
  have hd4 := hd3.add (simplePartPrimitive19_deriv ht)
  have hd5 := hd4.add (simplePartPrimitive20_deriv ht)
  have hd6 := hd5.add (simplePartPrimitive21_deriv ht)
  have hd7 := hd6.add (simplePartPrimitive22_deriv ht)
  exact hd7

/-- Full fixed primitive, grouped only to respect default elaborator recursion. -/
def completePrimitive (t : ℝ) : ℝ := -143*t/980 + primitiveGroup0 t + primitiveGroup1 t + primitiveGroup2 t + primitiveGroup3 t + primitiveGroup4 t + primitiveGroup5 t + primitiveGroup6 t

def completePrimitiveKernel (t : ℝ) : ℝ := -143/980 + kernelGroup0 t + kernelGroup1 t + kernelGroup2 t + kernelGroup3 t + kernelGroup4 t + kernelGroup5 t + kernelGroup6 t

theorem completePrimitive_deriv_kernel {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt completePrimitive (completePrimitiveKernel t) t := by
  have hd0 := ((hasDerivAt_id t).const_mul (-143) |>.div_const 980)
  have hd1 := hd0.add (primitiveGroup0_deriv ht)
  have hd2 := hd1.add (primitiveGroup1_deriv ht)
  have hd3 := hd2.add (primitiveGroup2_deriv ht)
  have hd4 := hd3.add (primitiveGroup3_deriv ht)
  have hd5 := hd4.add (primitiveGroup4_deriv ht)
  have hd6 := hd5.add (primitiveGroup5_deriv ht)
  have hd7 := hd6.add (primitiveGroup6_deriv ht)
  convert hd7 using 1 <;> first | rfl | norm_num [completePrimitiveKernel, kernelGroup0]

end SigmaActualBlockSeparable
