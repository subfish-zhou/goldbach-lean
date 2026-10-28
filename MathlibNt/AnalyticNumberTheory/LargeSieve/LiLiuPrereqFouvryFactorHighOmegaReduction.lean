import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryModulusHighOmegaError
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDelayedConvolution
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWModulusSupportReduction


/-!
# The original error reduced to the actual low-omega factored W

The original modulus weight is unchanged on the left. Its difference from
the trimmed convolution is paid at the original signed error, including the
equality progression. Only then is the accepted five-small-factor reduction
applied to the trimmed convolution and its second coefficient expanded.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem signedError_sub_modulus (S N Q : Finset ℕ) (α β c d : ℕ → ℝ) (a : ℤ) :
    signedError S N Q α β c a - signedError S N Q α β d a =
      signedError S N Q α β (fun q => c q - d q) a := by
  simp only [signedError, sub_mul, sum_sub_distrib]

theorem signedError_sub_factorLowOmega (S N Q : Finset ℕ)
    (α β γ ζ : ℕ → ℝ) (a : ℤ) (ξ : ℝ) :
    signedError S N Q α β (factorConvolution γ ζ) a -
      signedError S N Q α β (factorConvolution γ (betaLowOmega ζ ξ)) a =
        signedError S N Q α β (factorConvolution γ (betaHighOmega ζ ξ)) a := by
  rw [signedError_sub_modulus, factorConvolution_sub_low]


def c2FiveSmallMask (x η : ℝ) (t : WOriginalTuple) : Prop :=
  ((((t.2.1.gcd t.2.2 : ℝ) ≤ x ^ η ∧
    (t.2.1.primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
    (t.2.2.primeFactors.card : ℝ) ≤ highOmegaCutoff x) ∧
    (t.1.1.gcd t.1.2 : ℝ) ≤ x ^ η) ∧
    ((wGCDTuple t).d₁ : ℝ) ≤ x ^ η) ∧
    ((wGCDTuple t).δ₁ : ℝ) ≤ x ^ η ∧ ((wGCDTuple t).δ₂ : ℝ) ≤ x ^ η


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
