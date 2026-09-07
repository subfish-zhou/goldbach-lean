import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9Reindex

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The original signed modulus sum, before any absolute value or approximation. -/
def fouvryG9Discrepancy (N : ℕ) (eps : ℝ) (Q : Finset ℕ) (c : ℕ → ℝ) : ℝ := by
  classical
  exact ∑ d ∈ reducedModuli Q (N : ℤ), c d *
    ((∑ x ∈ goldbachB9LowPositivePrefixAtoms N eps,
      if Int.ModEq d ((x.1.1*x.1.2*x.2 : ℕ) : ℤ) (N : ℤ) then (1 : ℝ) else 0) -
     (∑ x ∈ goldbachB9LowPositivePrefixAtoms N eps,
      if (x.1.1*x.1.2*x.2).Coprime d then (1 : ℝ) else 0) / d.totient)

/-- The complete coprime-mass centering and the external signed weight are preserved. -/
theorem fouvryG9Discrepancy_eq_reindexed (N : ℕ) (eps : ℝ) (Q : Finset ℕ)
    (c : ℕ → ℝ) :
    fouvryG9Discrepancy N eps Q c =
      ∑ d ∈ reducedModuli Q (N : ℤ), c d *
        ((∑ y ∈ fouvryG9Carrier N eps,
          if Int.ModEq d ((y.2.2*y.1 : ℕ) : ℤ) (N : ℤ) then (1 : ℝ) else 0) -
         (∑ y ∈ fouvryG9Carrier N eps,
          if (y.2.2*y.1).Coprime d then (1 : ℝ) else 0) / d.totient) := by
  classical
  unfold fouvryG9Discrepancy
  apply sum_congr rfl
  intro d _
  have hAP := fouvryG9_sum_reindex N eps (fun n m =>
    if Int.ModEq d ((n*m : ℕ) : ℤ) (N : ℤ) then (1 : ℝ) else 0)
  have hmass := fouvryG9_sum_reindex N eps (fun n m =>
    if (n*m).Coprime d then (1 : ℝ) else 0)
  simp only [← Nat.mul_assoc] at hAP hmass
  rw [hAP,hmass]

/-- The actual natural subtraction output agrees with the integer congruence. -/
theorem fouvryG9_output_dvd_iff {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hx : x ∈ goldbachB9LowPositivePrefixAtoms N eps)
    (d : ℕ) :
    d ∣ goldbachPi10Output N x ↔
      Int.ModEq d ((x.1.1*x.1.2*x.2 : ℕ) : ℤ) (N : ℤ) := by
  have hupper := (goldbachB9LowPositivePrefixAtoms_product_window hx).2.2
  have hnat : x.1.1*x.1.2*x.2 ≤ N := by exact_mod_cast hupper.le
  rw [Int.modEq_iff_dvd]
  change d ∣ N - x.1.1*x.1.2*x.2 ↔ _
  rw [← Int.natCast_sub hnat]
  exact Int.natCast_dvd_natCast.symm

/-- This is the divisor count of the existing mother, not a replacement carrier. -/
theorem fouvryG9_actual_divisor_count (N : ℕ) (eps : ℝ) (d : ℕ) :
    (((goldbachB9LowPositivePrefixAtoms N eps).filter
      (fun x => d ∣ goldbachPi10Output N x)).card : ℝ) =
    ∑ y ∈ fouvryG9Carrier N eps,
      if Int.ModEq d ((y.2.2*y.1 : ℕ) : ℤ) (N : ℤ) then (1 : ℝ) else 0 := by
  classical
  have he := fouvryG9_sum_reindex N eps (fun n m =>
    if Int.ModEq d ((n*m : ℕ) : ℤ) (N : ℤ) then (1 : ℝ) else 0)
  rw [← he]
  rw [← sum_boole]
  apply sum_congr rfl
  intro x hx
  simp only [fouvryG9_output_dvd_iff hx, Nat.mul_assoc]

/-- A repeated long product is counted with its original prime-label multiplicity. -/
theorem fouvryG9Multiplicity_le_tau_two (N : ℕ) (eps : ℝ) (n m : ℕ) :
    (fouvryG9Multiplicity N eps n m : ℝ) ≤ (fouvryTau 2 m : ℝ) := by
  exact_mod_cast (show fouvryG9Multiplicity N eps n m ≤ fouvryTau 2 m by
    rw [fouvryTau_two]
    exact fouvryG9Multiplicity_le_divisors N eps n m)

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
