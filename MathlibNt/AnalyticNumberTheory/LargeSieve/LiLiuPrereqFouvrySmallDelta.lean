import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCovariance
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmoothErrorBounds

/-!
# Small gcd contribution to the actual W-minus-U zero mode

The beta input is an independent coprime-sieved AP discrepancy estimate.
An L-infinity times L-one covariance bound avoids a factor of the gcd.
Elementary reciprocal divisor means then evaluate the entire small-gcd
modulus sum. The complementary large-gcd contribution is left explicit.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

theorem betaResidueMass_abs_le (N : Finset ℕ) (β : ℕ → ℝ) (q δ b : ℕ) :
    |betaResidueMass N β q δ b| ≤
      betaResidueMass N (fun n => |β n|) q δ b := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n _
  split_ifs <;> simp

/-- Centering on reduced classes costs at most twice the original L-one mass.
The partition uses the actual coprime sieve by `q`. -/
theorem sum_abs_betaResidueMass_centered_le
    (N : Finset ℕ) (β : ℕ → ℝ) {q δ : ℕ}
    (hδ : 0 < δ) (hdq : δ ∣ q) :
    (∑ b ∈ betaReducedResidues δ,
      |betaResidueMass N β q δ b - coprimeMass N β q / (δ.totient : ℝ)|) ≤
        2 * ∑ n ∈ N, |β n| := by
  have hφ : (δ.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hδ).ne'
  calc
    _ ≤ ∑ b ∈ betaReducedResidues δ,
        (betaResidueMass N (fun n => |β n|) q δ b +
          |coprimeMass N β q| / (δ.totient : ℝ)) := by
      apply sum_le_sum
      intro b _
      exact (abs_sub _ _).trans (add_le_add (betaResidueMass_abs_le N β q δ b)
        (by rw [abs_div, Nat.abs_cast]))
    _ = coprimeMass N (fun n => |β n|) q + |coprimeMass N β q| := by
      rw [sum_add_distrib, sum_betaResidueMass N _ hδ hdq]
      simp only [sum_const, nsmul_eq_mul, betaReducedResidues_card]
      rw [mul_div_cancel₀ _ hφ]
    _ ≤ _ := by
      have := coprimeMass_of_abs_le_sum_abs N β q
      have := coprimeMass_abs_le_sum_abs N β q
      linarith

/-- Only one independent AP bound is needed, with no totient/gcd factor. -/
theorem betaCovariance_abs_le_coprimeAP_lone
    (N : Finset ℕ) (β : ℕ → ℝ) {q r : ℕ} (hq : 0 < q)
    {E : ℝ} (hE : 0 ≤ E)
    (hAP : ∀ b ∈ betaReducedResidues (q.gcd r),
      |betaCoprimeAPDiscrepancy N β (q.gcd r) (q / q.gcd r) b| ≤ E) :
    |betaCovariance N β q r| ≤ 2 * E * ∑ n ∈ N, |β n| := by
  unfold betaCovariance
  calc
    _ ≤ ∑ b ∈ betaReducedResidues (q.gcd r),
        E * |betaResidueMass N β r (q.gcd r) b -
          coprimeMass N β r / ((q.gcd r).totient : ℝ)| := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b hb
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [betaResidueMass_centered_eq_coprimeAPDiscrepancy N β
        (Nat.gcd_dvd_left q r) (mem_filter.mp hb).2]
      exact hAP b hb
    _ ≤ E * (2 * ∑ n ∈ N, |β n|) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_abs_betaResidueMass_centered_le N β
          (Nat.gcd_pos_of_pos_left r hq) (Nat.gcd_dvd_right q r)) hE
    _ = _ := by ring

/-- A single term of the divisor convolution suffices; no monotonicity
of prime-power divisor coefficients is required. -/
theorem fouvryTau_div_le_succ (κ : ℕ) {q δ : ℕ} (hq : q ≠ 0) (hdq : δ ∣ q) :
    fouvryTau κ (q / δ) ≤ fouvryTau (κ + 1) q := by
  rw [fouvryTau_succ]
  exact single_le_sum (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdq, hq⟩)


end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
