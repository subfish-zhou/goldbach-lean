import SrcFourEnclosureTotals

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass

namespace WuSource.SrcFourEnclosure

def massLower : ℝ :=
  ((cut-alpha)/64)*(∑ i ∈ Finset.range 64, smallLower i)+
    ((beta-cut)/64)*(∑ i ∈ Finset.range 64, largeLower i)-
      (error alpha cut+error cut beta)
def massUpper : ℝ :=
  ((cut-alpha)/64)*(∑ i ∈ Finset.range 64, smallUpper i)+
    ((beta-cut)/64)*(∑ i ∈ Finset.range 64, largeUpper i)+
      (error alpha cut+error cut beta)

theorem mass_package_enclosure : massLower ≤ mass ∧ mass ≤ massUpper := by
  have hs1 : ((cut-alpha)/64)*(∑ i ∈ Finset.range 64, smallLower i) ≤
      midpointSum smallLo alpha cut :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => (small_certificate i (Finset.mem_range.mp hi)).1))
      (by have h : alpha ≤ cut := geometry.2.2.2.2.2.1; linarith only [h])
  have hs2 : midpointSum smallHi alpha cut ≤
      ((cut-alpha)/64)*(∑ i ∈ Finset.range 64, smallUpper i) :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => (small_certificate i (Finset.mem_range.mp hi)).2))
      (by have h : alpha ≤ cut := geometry.2.2.2.2.2.1; linarith only [h])
  have hl1 : ((beta-cut)/64)*(∑ i ∈ Finset.range 64, largeLower i) ≤
      midpointSum largeLo cut beta :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => (large_certificate i (Finset.mem_range.mp hi)).1))
      (by have h : cut ≤ beta := geometry.2.2.2.2.2.2; linarith only [h])
  have hl2 : midpointSum largeHi cut beta ≤
      ((beta-cut)/64)*(∑ i ∈ Finset.range 64, largeUpper i) :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => (large_certificate i (Finset.mem_range.mp hi)).2))
      (by have h : cut ≤ beta := geometry.2.2.2.2.2.2; linarith only [h])
  have hm := mass_rational_sums
  unfold massLower massUpper
  constructor <;> linarith only [hm.1,hm.2,hs1,hs2,hl1,hl2]

theorem massLower_exact :
    massLower = (593880545134673457600154103/490259108795374272000000000 : ℝ) := by
  norm_num [massLower,smallLower_sum,largeLower_sum,error,cut,alpha,beta,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem massUpper_exact :
    massUpper = (297186721518360047085081389/245129554397687136000000000 : ℝ) := by
  norm_num [massUpper,smallUpper_sum,largeUpper_sum,error,cut,alpha,beta,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem mass_rational_enclosure :
    (15142/12500 : ℝ) < mass ∧ mass < (606183/500000 : ℝ) := by
  have hm := mass_package_enclosure
  rw [massLower_exact,massUpper_exact] at hm
  constructor <;> linarith only [hm.1,hm.2]

#check @mass_package_enclosure
#check @massLower_exact
#check @massUpper_exact
#check @mass_rational_enclosure
#print axioms mass_package_enclosure
#print axioms massLower_exact
#print axioms massUpper_exact
#print axioms mass_rational_enclosure
end WuSource.SrcFourEnclosure
