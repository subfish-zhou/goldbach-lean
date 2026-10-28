import MathlibNt.SieveTheory.LiLiuGoldbachG11CommonMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDivisorDistribution


namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Finset
open scoped BigOperators
noncomputable section

abbrev GoldbachG12LinkedAtom := Σ _m : ℕ, ℕ

def goldbachG12LinkedAtoms (N : ℕ) (ε : ℝ) : Finset GoldbachG12LinkedAtom :=
  (goldbachG12ActiveProductSupport N).sigma (goldbachG11LinkedPrimeWindow N ε)

def goldbachG12LinkedOutput (N : ℕ) (x : GoldbachG12LinkedAtom) : ℕ := N-x.2*x.1

def goldbachG12LinkedOutputSupport (N : ℕ) (ε : ℝ) : Finset ℕ :=
  (goldbachG12LinkedAtoms N ε).image (goldbachG12LinkedOutput N)

/-- Weighted fibres, not a set of distinct outputs with weight one. -/
def goldbachG12LinkedOutputWeight (N : ℕ) (ε : ℝ) (p : ℕ) : ℝ :=
  ∑ x ∈ (goldbachG12LinkedAtoms N ε).filter (fun x => goldbachG12LinkedOutput N x = p),
    goldbachG12NormalizedCoefficient N x.1


end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig