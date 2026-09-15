import MathlibNt.Wu2008DoubleSieve.PhiBuchstab

/-! # The literal three terms of Wu04 Lemma 4.1 -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

noncomputable def wuOmega1 (N d : ℕ) (δ t : ℝ) : ℝ :=
  2 * (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d t) : ℝ)

noncomputable def wuOmega2 (N d : ℕ) (δ s t : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
    (sourceSieveCount N (d * p) (d * N) (wuLocalCutoff N δ d t) : ℝ)

/-- Each increasing triple occurs once. The selected modulus is `d*p₁*N`
and the strict cutoff is the middle prime, not the first prime. -/
noncomputable def wuOmega3 (N d : ℕ) (δ s t : ℝ) : ℝ :=
  ∑ p₃ ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
    ∑ p₂ ∈ primeWindow N (wuLocalCutoff N δ d t) (p₃ : ℝ),
      ∑ p₁ ∈ primeWindow N (wuLocalCutoff N δ d t) (p₂ : ℝ),
        (sourceSieveCount N (d * p₁ * p₂ * p₃) (d * p₁ * N) (p₂ : ℝ) : ℝ)

noncomputable def wuOmega1Sum {i : ℕ} (N : ℕ) (δ t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * wuOmega1 N d δ t

noncomputable def wuOmega2Sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * wuOmega2 N d δ s t

noncomputable def wuOmega3Sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * wuOmega3 N d δ s t

end Wu2008DoubleSieve
