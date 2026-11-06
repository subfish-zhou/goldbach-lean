import MixedEtaDebit

namespace MixedEta
open Finset Real Wu2008DoubleSieve MixedSixth Filter
open scoped Classical Topology
noncomputable section

def highScalar (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ highCells δ n, highCoefficient δ n i *
    truncatedSixthMassRectangleCoefficient δ (loX n i) (hiX n i) (loY n i) (hiY n i)

def highMain (N n : ℕ) (δ : ℝ) : ℝ :=
  ∑ k ∈ packing N n (highCells δ n),
    (log (sourceS δ n k-1)+(1/10000)*log (2/(sourceS δ n k-1)))*theta N n k δ

/-- The actual fine-grid labels carry their original coarse coefficient, without dropping weights. -/
theorem highMain_eq (N n : ℕ) (δ : ℝ) :
    highMain N n δ = ∑ i ∈ highCells δ n, highCoefficient δ n i *
      rectangleTheta N δ (loX n i) (hiX n i) (loY n i) (hiY n i) := by
  unfold highMain
  rw [sum_packing]
  apply sum_congr rfl
  intro i _
  simp only [sourceS,outer,MixedSixth.inner,x,y,Nat.unpair_pair,theta,highCoefficient,rectangleTheta,mul_sum]


end
end MixedEta
