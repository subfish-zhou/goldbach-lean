import MathlibNt.SieveTheory.LiLiuFouvryG9FiniteTransport

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuPrereqWF

/-- The coprime center is an exact sum of the genuine progression densities,
not a replacement by a scalar mass with its gcd exclusions discarded. -/
theorem g9IntegerFibreCenter_eq_progressionDensity (U V : Finset ℕ)
    (α β : ℕ → ℝ) (d : ℕ) :
    g9IntegerFibreCenter U V α β d =
      ∑ m ∈ U, ∑ n ∈ V, α m*β n*progressionDensity (m*n) d := by
  unfold g9IntegerFibreCenter
  rw [sum_div]
  apply sum_congr rfl
  intro m _
  rw [sum_div]
  apply sum_congr rfl
  intro n _
  change (if (m*n).Coprime d then α m*β n else 0)/(d.totient : ℝ) =
    α m*β n*(if d.Coprime (m*n) then (d.totient : ℝ)⁻¹ else 0)
  by_cases h : (m*n).Coprime d
  · rw [if_pos h, if_pos h.symm]
    ring
  · have h' : ¬d.Coprime (m*n) := fun hh => h hh.symm
    rw [if_neg h, if_neg h']
    simp

/-- Exact normalization of the entire actual main term into the already
proved external-family density. No sign or analytic assumption is needed. -/
theorem g9IntegerFibreCenter_externalDensity (upper : Bool) (P : Finset ℕ)
    (D η z : ℝ) (U V : Finset ℕ) (α β : ℕ → ℝ) :
    (∑ t ∈ externalTags upper P D η z, ∑ d ∈ (P.prod id).divisors,
      externalTerm upper P D η z t d*g9IntegerFibreCenter U V α β d) =
    ∑ m ∈ U, ∑ n ∈ V, α m*β n*
      externalDensity upper P D η z (progressionDensity (m*n)) := by
  simp only [g9IntegerFibreCenter_eq_progressionDensity,externalDensity,mul_sum]
  simp_rw [sum_comm (s := (P.prod id).divisors) (t := U)]
  rw [sum_comm (s := externalTags upper P D η z) (t := U)]
  simp_rw [sum_comm (s := (P.prod id).divisors) (t := V)]
  simp_rw [sum_comm (s := externalTags upper P D η z) (t := V)]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro d _
  ring

end MathlibNt.SieveTheory.LiLiuPrereqWF
