import InsertedGainCover

namespace BuchstabCount
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- The actual Buchstab prime dominates the fixed inserted cutoff. The
comparison uses the lower endpoint three, not the Omega2 fixed cutoff. -/
theorem inserted_cutoff_le_prime {N d p : ℕ} {δ : ℝ}
    (hp : p.Prime) (hlo : wuLocalCutoff N δ d 3 ≤ (p : ℝ)) :
    wuLocalCutoff N δ (d*p) (29/10) ≤ (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hbase : 0 ≤ (N : ℝ)^(1/2-δ)/(d : ℝ) := by positivity
  have hcube := rpow_le_rpow (rpow_nonneg hbase (1/3)) hlo (by norm_num : (0 : ℝ) ≤ 3)
  change (((N : ℝ)^(1/2-δ)/(d : ℝ))^(1/(3 : ℝ)))^(3 : ℝ) ≤ (p : ℝ)^(3 : ℝ) at hcube
  rw [← rpow_mul hbase] at hcube
  norm_num at hcube
  have hquot : (N : ℝ)^(1/2-δ)/(d : ℝ)/(p : ℝ) ≤ (p : ℝ)^2 := by
    apply (div_le_iff₀ hp0).mpr
    nlinarith only [hcube]
  change ((N : ℝ)^(1/2-δ)/(d*p : ℕ))^(1/(29/10 : ℝ)) ≤ _
  rw [Nat.cast_mul, ← div_div]
  calc
    _ ≤ ((p : ℝ)^2)^(1/(29/10 : ℝ)) := rpow_le_rpow (by positivity) hquot (by norm_num)
    _ = (p : ℝ)^((2 : ℝ)*(1/(29/10 : ℝ))) := by
      rw [← rpow_natCast, ← rpow_mul hp0.le]
      norm_num
    _ ≤ (p : ℝ)^(1 : ℝ) := rpow_le_rpow_of_exponent_le hp1 (by norm_num)
    _ = _ := rpow_one _

/-- Retain d*N in the actual prime domain; only its inclusion in the
N-window is used to locate the pre-existing occupied source cell. -/
theorem selected_prime_window_subset (N d : ℕ) (z w : ℝ) :
    primeWindow (d*N) z w ⊆ primeWindow N z w := by
  intro p hp
  obtain ⟨hpp,hpc,hlo,hhi⟩ := mem_primeWindow.mp hp
  exact mem_primeWindow.mpr ⟨hpp,(Nat.coprime_mul_iff_right.mp hpc).2,hlo,hhi⟩

end
end BuchstabCount
