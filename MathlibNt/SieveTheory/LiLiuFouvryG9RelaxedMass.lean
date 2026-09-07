import MathlibNt.SieveTheory.LiLiuFouvryG9MainUpper

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual labelled rectangle mass; no multiplicity is removed. -/
def fouvryG9RectangleMass (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : ℝ :=
  ∑ m ∈ fouvryG9LongProducts N ρ k, ∑ n ∈ fouvryG9RectanglePrimeSupport N ρ k,
    fouvryG9LongAlpha N ρ k m * fouvryG9RectangleBeta N n

/-- Positive enlargement of the original pair curve, not the original C10 carrier. -/
def fouvryG9RelaxedPairs (N : ℕ) (ρ : ℝ) : Finset (ℕ × ℕ) :=
  ((range (N+1)) ×ˢ (range (N+1))).filter fun rs =>
    rs.1.Prime ∧ rs.2.Prime ∧ (N : ℝ)^(4/53 : ℝ) ≤ rs.1 ∧
    (rs.1 : ℝ) < (N : ℝ)^(1/10 : ℝ) ∧ (N : ℝ)^(1/3 : ℝ) ≤ rs.2 ∧
    (rs.1 : ℝ)*(rs.2 : ℝ)^2 ≤ ρ^3*(N : ℝ)

/-- Logarithmic kernel for the genuinely enlarged pair region. -/
def fouvryG9RelaxedPairKernel (N : ℕ) (ρ δ : ℝ) : ℝ :=
  ∑ rs ∈ fouvryG9RelaxedPairs N ρ,
    let u := Real.log (rs.1 : ℝ)/Real.log (N : ℝ)
    let v := Real.log (rs.2 : ℝ)/Real.log (N : ℝ)
    let w := 1+3*Real.log ρ/Real.log (N : ℝ)
    1 / ((rs.1 : ℝ)*(rs.2 : ℝ)*(w-u-v)*((5/9 : ℝ)*(1-u)-δ))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
