import MathlibNt.Wu2008DoubleSieve.Omega3FiniteErrorSource

/-!
# Actual coefficient-weighted Omega3 errors

Each convolution coefficient occurs exactly once. The finite errors here
are the original filtered counts from the switching theorem, not arbitrary
majorants supplied by the caller.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical


theorem omega3_badDCount_le_reciprocal_mass {i N : ℕ} {δ s t η : ℝ}
    (W : Fin i → Finset ℕ) (hN : 4 ≤ N) (heven : Even N) (hη : 0 < η)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ d ≤ N)
    (hlow : ∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ η ≤ wuLocalCutoff N δ d t)
    (hlarge : ∀ d ∈ boxConvolutionSupport W,
      ∀ q ∈ d.primeFactors, (N : ℝ) ^ η ≤ (q : ℝ)) :
    omega3BadDCount N δ s t W ≤
      ((1 / η) ^ 4 * ((N : ℝ) / (N : ℝ) ^ η)) * boxConvolutionReciprocalMass W := by
  unfold omega3BadDCount omega3LabelSum boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hdS
  calc
    _ ≤ (convolutionCoeff W d : ℝ) *
        ((1 / η) ^ 4 * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η)) :=
      mul_le_mul_of_nonneg_left
        (omega3_source_badD_sum_le_power hN heven (hd d hdS).1 (hd d hdS).2 hη
          (hlow d hdS) (hlarge d hdS)) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem omega3_badNCount_le_allowed_outputs {i N : ℕ} {δ s t η : ℝ}
    (W : Fin i → Finset ℕ) (E : Finset ℕ)
    (hN : 4 ≤ N) (heven : Even N) (hη : 0 < η)
    (hlow : ∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ η ≤ wuLocalCutoff N δ d t)
    (hE : ∀ ell, ell.Prime → ell ≤ N → ell ∣ N → ell ∈ E) :
    omega3BadNCount N δ s t W ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ((1 / η) ^ 3 * (E.card : ℝ)) := by
  unfold omega3BadNCount omega3LabelSum omega3BadNFibre
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (omega3_source_filter_sum_le_outputs (fun ell => ell ∣ N) E hN heven hη
      (hlow d hd) hE) (Nat.cast_nonneg _)


theorem omega3_smallOutputCount_le_allowed_outputs {i N : ℕ} {δ s t Z η : ℝ}
    (W : Fin i → Finset ℕ) (E : Finset ℕ)
    (hN : 4 ≤ N) (heven : Even N) (hη : 0 < η)
    (hlow : ∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ η ≤ wuLocalCutoff N δ d t)
    (hE : ∀ ell, ell.Prime → ell ≤ N → (ell : ℝ) < Z → ell ∈ E) :
    omega3SmallOutputCount N δ s t Z W ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ((1 / η) ^ 3 * (E.card : ℝ)) := by
  unfold omega3SmallOutputCount omega3LabelSum omega3SmallOutputFibre
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (omega3_source_filter_sum_le_outputs (fun ell => (ell : ℝ) < Z) E hN heven hη
      (hlow d hd) hE) (Nat.cast_nonneg _)


end Wu2008DoubleSieve
