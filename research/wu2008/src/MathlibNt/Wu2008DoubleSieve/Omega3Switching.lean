import MathlibNt.Wu2008DoubleSieve.Omega3SwitchingFibre

/-!
# Multiplicity-preserving finite Omega3 switching

The convolution coefficient is used exactly once, as the weight of each
fixed-d fibre. All three selected primes remain indexed. The upper endpoint
is the literal strict endpoint in `wuOmega3Sum`, not Wu04's closed enlargement.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def omega3LabelSum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p3 ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∑ p2 ∈ primeWindow N (wuLocalCutoff N δ d t) (p3 : ℝ),
        ∑ p1 ∈ primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ), F d p1 p2 p3

noncomputable def omega3SwitchedSiftedCount {i : ℕ} (N : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  omega3LabelSum N δ s t W fun d p1 p2 p3 =>
    (omega3SiftedSwitchedFibre N d p1 p2 p3 Z).card

noncomputable def omega3BadDCount {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  omega3LabelSum N δ s t W fun d p1 p2 p3 => (omega3BadDFibre N d p1 p2 p3).card

noncomputable def omega3BadNCount {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  omega3LabelSum N δ s t W fun d p1 p2 p3 => (omega3BadNFibre N d p1 p2 p3).card

noncomputable def omega3SmallOutputCount {i : ℕ} (N : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  omega3LabelSum N δ s t W fun d p1 p2 p3 =>
    (omega3SmallOutputFibre N d p1 p2 p3 Z).card

theorem omega3LabelSum_add {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (F G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    omega3LabelSum N δ s t W (fun d p1 p2 p3 => F d p1 p2 p3 + G d p1 p2 p3) =
      omega3LabelSum N δ s t W F + omega3LabelSum N δ s t W G := by
  simp only [omega3LabelSum, sum_add_distrib, mul_add]

theorem omega3LabelSum_mono {i : ℕ} {N : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} {F G : ℕ → ℕ → ℕ → ℕ → ℝ}
    (h : ∀ d ∈ boxConvolutionSupport W,
      ∀ p3 ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∀ p2 ∈ primeWindow N (wuLocalCutoff N δ d t) (p3 : ℝ),
      ∀ p1 ∈ primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ),
        F d p1 p2 p3 ≤ G d p1 p2 p3) :
    omega3LabelSum N δ s t W F ≤ omega3LabelSum N δ s t W G := by
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro p3 h3
  apply sum_le_sum
  intro p2 h2
  apply sum_le_sum
  intro p1 h1
  exact h d hd p3 h3 p2 h2 p1 h1

/-- The coefficient-weighted original count is literally Omega3, including
all tuple multiplicities already present in the convolution coefficient. -/
theorem wuOmega3Sum_eq_original_label_count {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) :
    wuOmega3Sum N δ s t W =
      omega3LabelSum N δ s t W fun d p1 p2 p3 =>
        (sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).card := by
  simp only [wuOmega3Sum, wuOmega3, omega3LabelSum, sourceSieveCount, Int.cast_natCast]



end Wu2008DoubleSieve
