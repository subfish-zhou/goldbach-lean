import MathlibNt.SieveTheory.LiLiuGoldbachG11CollarGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG11CollarScalar

open Finset LiLiuPrereqBuchstab
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- One integer reciprocal strip and three original prime reciprocal sums.
No factorial, distinctness, or unproved short-prime distribution is used. -/
theorem goldbachG11Collar_reciprocal_bound (N : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    (∑ v ∈ goldbachG11CollarBoxes N ρ,1/(goldbachG11SwitchedBodyProd v : ℝ)) ≤
      (ρ-1)*(∑ p ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),1/(p : ℝ))^3 := by
  let P := goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
  change _ ≤ (ρ-1)*(∑ p ∈ P,1/(p : ℝ))^3
  calc
    _ = ∑ t ∈ P,∑ s ∈ P,∑ q ∈ P,
        (1/((q : ℝ)*s*t))*(∑ p ∈ Ioc q ⌊ρ*(q : ℝ)⌋₊,1/(p : ℝ)) := by
      simp only [goldbachG11CollarBoxes,goldbachG11SwitchedBodyProd,sum_sigma,Nat.cast_mul,mul_sum]
      apply sum_congr rfl; intro t _
      apply sum_congr rfl; intro s _
      apply sum_congr rfl; intro q _
      apply sum_congr rfl; intro p _
      simp only [one_div,mul_inv]
    _ ≤ ∑ t ∈ P,∑ s ∈ P,∑ q ∈ P,(1/((q : ℝ)*s*t))*(ρ-1) := by
      apply sum_le_sum; intro t _
      apply sum_le_sum; intro s _
      apply sum_le_sum; intro q hq
      exact mul_le_mul_of_nonneg_left
        (goldbachG11_integer_collar_reciprocal (mem_goldbachClosedPrimes_iff.mp hq).1.pos hρ) (by positivity)
    _ = _ := by
      simp only [pow_succ,pow_zero,mul_sum,sum_mul]
      apply sum_congr rfl; intro t _
      apply sum_congr rfl; intro s _
      apply sum_congr rfl; intro q _
      simp only [one_div,mul_inv]
      ring

/-- The complete ordering collar is O(rho-1) in the required N/log N scale.
Its constant and threshold are uniform for the entire closed rho range. -/
theorem goldbachG11Collar_rough_paid :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ 5/4 →
      (Real.log (N : ℝ)/N)*goldbachG11CollarRoughMass N ρ ≤ C*(ρ-1) := by
  obtain ⟨B,hB,Mb,hMb,hb⟩ := goldbachG11_prime_reciprocal_bounded
  obtain ⟨Mr,hMr,hr⟩ := goldbachG11Collar_rough_point_bound
  refine ⟨53*B^3,by positivity,max Mb Mr,hMb.trans (le_max_left _ _),?_⟩
  intro N hN ρ hρ hρu
  obtain ⟨hNb,hNr⟩ := max_le_iff.mp hN
  have hp := hb N hNb
  have hnn : 0 ≤ ∑ p ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),1/(p : ℝ) :=
    sum_nonneg (fun p _ => by positivity)
  calc
    _ = ∑ v ∈ goldbachG11CollarBoxes N ρ,(Real.log (N : ℝ)/N)*
        (roughCount (ρ^2*N/goldbachG11SwitchedBodyProd v) v.2.2.1 : ℝ) := by rw [goldbachG11CollarRoughMass,mul_sum]
    _ ≤ ∑ v ∈ goldbachG11CollarBoxes N ρ,53*(1/(goldbachG11SwitchedBodyProd v : ℝ)) := sum_le_sum (hr N hNr ρ hρ hρu)
    _ = 53*∑ v ∈ goldbachG11CollarBoxes N ρ,1/(goldbachG11SwitchedBodyProd v : ℝ) := (mul_sum _ _ _).symm
    _ ≤ 53*((ρ-1)*(∑ p ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),1/(p : ℝ))^3) :=
      mul_le_mul_of_nonneg_left (goldbachG11Collar_reciprocal_bound N hρ) (by norm_num)
    _ ≤ 53*((ρ-1)*B^3) := by gcongr
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig