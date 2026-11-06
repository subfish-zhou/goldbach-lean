module

public import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutput

@[expose] public section

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A prime output at or above the cutoff survives the literal sieve carrier.
No coprimality of the output with N is needed. -/
theorem fouvryG9PrimeOutput_coprime {N r : ℕ} {z : ℝ}
    (hr : r.Prime) (hz : z ≤ (r : ℝ)) :
    r.Coprime ((fouvryG9SievePrimes N z).prod id) := by
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  obtain ⟨hpp,_,hpz⟩ := (fouvryG9SievePrimes_mem N p z).mp hp
  change r.Coprime p
  rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
  intro hd
  have he : r = p := (hr.dvd_iff_eq hpp.ne_one).mp hd
  subst r
  linarith

/-- The exact pointwise split retains small prime outputs as an explicit cost. -/
theorem fouvryG9PrimeOutput_indicator (N r : ℕ) (z : ℝ) :
    (if r.Prime then (1 : ℝ) else 0) ≤
      (if r.Coprime ((fouvryG9SievePrimes N z).prod id) then 1 else 0) +
      (if (r : ℝ) < z then 1 else 0) := by
  by_cases hs : (r : ℝ) < z
  · simp only [ite_eq_left hs]
    split_ifs <;> norm_num
  · by_cases hp : r.Prime
    · have hc := fouvryG9PrimeOutput_coprime (N := N) hp (le_of_not_gt hs)
      simp only [ite_eq_left hp, ite_eq_left hc, ite_eq_right hs, add_zero, le_refl]
    · simp only [ite_eq_right hp,ite_eq_right hs,add_zero]
      split_ifs <;> norm_num


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
