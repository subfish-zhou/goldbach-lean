import HighCrossActual
import MathlibNt.Wu2008DoubleSieve.Omega2RawBlocks

namespace HighCross
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- A real inserted lower Phi contributes negatively in the weighted upper
mother. The two selected moduli are identified only above the cutoff. -/
theorem inserted_phi_le_omega2 {i N : ℕ} {δ s t u : ℝ}
    (W : Fin i → Finset ℕ) (P : Finset ℕ)
    (hinside : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P,
      p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∧
        wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ (d*p) u) :
    wuBoxPhi N δ (Fin.cons P W) u ≤ wuOmega2Sum N δ s t W := by
  rw [wuBoxPhi_cons]
  unfold wuOmega2Sum wuOmega2
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ p ∈ P, (sourceSieveCount N (d*p) (d*N) (wuLocalCutoff N δ d t) : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hwin := (hinside d hd p hp).1
      have hcut := (hinside d hd p hp).2
      have hm := omega2_source_count_prime_modulus_eq N d
        (mem_primeWindow.mp hwin).1 (mem_primeWindow.mp hwin).2.2.1
      rw [← hm]
      exact_mod_cast sourceSieveCount_antitone N (d*p) ((d*p)*N) hcut
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (hinside d hd p hp).1
      · intro p _ _
        unfold sourceSieveCount
        positivity

/-- Actual lower Rosser main, with its full CN/log^18 debit, now occurs
with the right sign in the switching candidate; it is not merely carried
along as an unused terminal field. -/
theorem inserted_rosser_le_omega2 {i N : ℕ} {δ ε C s t u : ℝ}
    (W : Fin i → Finset ℕ) (P : Finset ℕ)
    (hinside : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P,
      p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∧
        wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ (d*p) u)
    (hpaid : LowerSourcePaid N δ ε C u (Fin.cons P W)) :
    convolutionRosserMain N (Fin.cons P W) false (wuVariableRosserLevel N δ)
      (fun d => wuLocalCutoff N δ d u) - C*N/log (N : ℝ)^(18 : ℝ) ≤
      wuOmega2Sum N δ s t W :=
  hpaid.2.trans (inserted_phi_le_omega2 W P hinside)

/-- The lower-Rosser/switched-li competition giving the finite gain. -/
def rosserGainTest {i : ℕ} (N : ℕ) (δ ε ρ C s t u : ℝ)
    (W : Fin i → Finset ℕ) (P : Finset ℕ) : ℝ :=
  (convolutionRosserMain N (Fin.cons P W) false (wuVariableRosserLevel N δ)
      (fun d => wuLocalCutoff N δ d u) - C*N/log (N : ℝ)^(18 : ℝ) -
    (2 * (rosserUpper N δ t W - rosserUpper N δ s W) +
      liX N δ s t W * switchedDensity N δ ρ +
      ε*boxTheta N ((N : ℝ)^(1/2-δ)) W + switchingLoss N δ s t W)) / 2

/-- Constructed lower Rosser feeds the actual upper gain. Strict positivity
of this signed test remains to be established analytically. -/
theorem rosser_test_le_gain {i N : ℕ} {δ ε ρ C s t u : ℝ}
    (W : Fin i → Finset ℕ) (P : Finset ℕ)
    (hinside : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P,
      p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∧
        wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ (d*p) u)
    (hpaid : LowerSourcePaid N δ ε C u (Fin.cons P W)) :
    max 0 (rosserGainTest N δ ε ρ C s t u W P) ≤ finiteGain N δ ε ρ s t W := by
  have hl := inserted_rosser_le_omega2 W P hinside hpaid
  apply max_le_max le_rfl
  dsimp [rosserGainTest, switchedUpper]
  linarith


end
end HighCross
