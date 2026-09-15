import MathlibNt.Wu2004MeanValue.ActualAP
import MathlibNt.Wu2004MeanValue.OpenIntervals

/-! Exact conversion of the manuscript's open intervals into two actual Wu
errors and the upper-endpoint atom, before any modulus summation. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

def actualOpenErrorSum (S : Finset ℕ) (f lo hi : ℕ → ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ S, if m.Coprime d then f m *
    (((openScaledPrimeSet (lo m) (hi m) d b m).card : ℝ) -
      (wuLi (hi m / m) - wuLi (lo m / m)) / d.totient) else 0

def actualEndpointSum (S : Finset ℕ) (f hi : ℕ → ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ S.filter (fun m => m.Coprime d),
    f m * (upperEndpointSet (hi m) d b m).card

theorem actualOpenErrorSum_eq (S : Finset ℕ) (f lo hi : ℕ → ℝ) (d b : ℕ)
    (hS : ∀ m ∈ S, 0 < m) (hlo : ∀ m ∈ S, 0 ≤ lo m)
    (hlt : ∀ m ∈ S, lo m < hi m) :
    actualOpenErrorSum S f lo hi d b =
      actualAPSum S f (fun m => hi m / m) d b -
        actualAPSum S f (fun m => lo m / m) d b - actualEndpointSum S f hi d b := by
  simp only [actualOpenErrorSum, actualAPSum, actualEndpointSum, sum_filter,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  by_cases hc : m.Coprime d
  · simp only [if_pos hc]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (hS m hm).ne'
    have hmul (t : ℝ) : (m : ℝ) * (t / m) = t := by field_simp
    rw [hmul, hmul, openInterval_error_identity (lo m) (hi m) d b m
      (hlo m hm) (hlt m hm) (hS m hm)]
    ring
  · simp only [if_neg hc, sub_self]

theorem abs_actualEndpointSum_le (S : Finset ℕ) (f hi : ℕ → ℝ)
    (d b : ℕ) (F : ℝ) (hF : 0 ≤ F)
    (hS : ∀ m ∈ S, 0 < m) (hf : ∀ m ∈ S, |f m| ≤ F) :
    |actualEndpointSum S f hi d b| ≤ F * S.card := by
  refine (abs_sum_upperEndpoint_le (S.filter (fun m => m.Coprime d)) hi f d b F hF
    (fun m hm => hS m (mem_filter.mp hm).1)
    (fun m hm => hf m (mem_filter.mp hm).1)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hF
  exact_mod_cast card_filter_le S (fun m => m.Coprime d)

theorem weighted_actualOpenErrorSum_le (S : Finset ℕ) (f lo hi : ℕ → ℝ)
    (Q : ℕ) (b : ℕ → ℕ) (hS : ∀ m ∈ S, 0 < m)
    (hlo : ∀ m ∈ S, 0 ≤ lo m) (hlt : ∀ m ∈ S, lo m < hi m) :
    (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualOpenErrorSum S f lo hi d (b d)|) ≤
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum S f (fun m => hi m / m) d (b d)|) +
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum S f (fun m => lo m / m) d (b d)|) +
      ∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualEndpointSum S f hi d (b d)| := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro d _
  rw [actualOpenErrorSum_eq S f lo hi d (b d) hS hlo hlt, ← mul_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (wuModulusWeight_nonneg d)
  exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)

end
end Wu2004MeanValue
