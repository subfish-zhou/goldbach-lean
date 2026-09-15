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

/-- Exact weighted identity for an arbitrary real-valued test of all
original labels and the reconstructed quotient. -/
theorem omega3_weighted_fibre_identity {i N : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} (hN : 4 ≤ N) (heven : Even N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) :
    omega3LabelSum N δ s t W (fun d p1 p2 p3 =>
      ∑ ell ∈ sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ),
        f d p1 p2 p3 ell (omega3Quotient N d p1 p2 p3 ell)) =
    omega3LabelSum N δ s t W (fun d p1 p2 p3 =>
      ∑ n ∈ omega3QuotientFibre N d p1 p2 p3,
        f d p1 p2 p3 (N - omega3Cofactor d p1 p2 n * p3) n) := by
  unfold omega3LabelSum
  apply sum_congr rfl
  intro d hd'
  congr 1
  apply sum_congr rfl
  intro p3 h3
  apply sum_congr rfl
  intro p2 h2
  apply sum_congr rfl
  intro p1 h1
  exact omega3_fibre_sum_identity hN heven (hd d hd')
    (mem_primeWindow.mp h1).1.pos (mem_primeWindow.mp h2).1.pos
    (mem_primeWindow.mp h3).1.pos (f d p1 p2 p3)

/-- Finite switching with explicit original-label losses. This is the
counting bridge; no distribution estimate or asymptotic payment is assumed. -/
theorem wuOmega3Sum_le_switched_add_actual_errors {i N : ℕ} {δ s t Z : ℝ}
    {W : Fin i → Finset ℕ} (hN : 4 ≤ N) (heven : Even N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    wuOmega3Sum N δ s t W ≤
      omega3SwitchedSiftedCount N δ s t Z W +
      omega3BadDCount N δ s t W +
      omega3BadNCount N δ s t W +
      omega3SmallOutputCount N δ s t Z W := by
  rw [wuOmega3Sum_eq_original_label_count]
  unfold omega3SwitchedSiftedCount omega3BadDCount omega3BadNCount omega3SmallOutputCount
  rw [← omega3LabelSum_add, ← omega3LabelSum_add, ← omega3LabelSum_add]
  apply omega3LabelSum_mono
  intro d hd' p3 _ p2 h2 p1 h1
  have h := omega3_fibre_switching_bound (p3 := p3) (Z := Z) hN heven (hd d hd')
    (mem_primeWindow.mp h1).1 (mem_primeWindow.mp h1).2.1 (mem_primeWindow.mp h2).2.1
  exact_mod_cast h

end Wu2008DoubleSieve
