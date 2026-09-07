import MathlibNt.SieveTheory.LiLiuGoldbachG11FouvryMainGate
import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrection

open Finset
open scoped BigOperators Classical
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace G11FiniteGate

/-- A product-dependent progression Euler factor costs one payment for each
DISTINCT prime divisor. Repeated factors are allowed and no gate is discarded. -/
theorem progressionEuler_rough_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p)
    {v K : ℕ} {L : ℝ} (hv : 0 < v) (hL : 4 ≤ L)
    (hrough : ∀ p ∈ v.primeFactors, L ≤ (p : ℝ)) (hK : v.primeFactors.card ≤ K) :
    (∏ p ∈ P, (1-progressionDensity v p)) ≤ g9BaseEuler P*(1+1/(L-2))^K := by
  let C : ℝ := 1+1/(L-2)
  let S := P.filter fun p => p ∣ v
  have hC : 1 ≤ C := by
    have hh : 0 ≤ 1/(L-2) := div_nonneg zero_le_one (by linarith)
    dsimp [C]
    linarith
  have hS : S ⊆ v.primeFactors := by
    intro p hp
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hd,hv.ne'⟩
  have hpoint : ∀ p ∈ P, 1-progressionDensity v p ≤
      (1-1/((p : ℝ)-1))*(if p ∣ v then C else 1) := by
    intro p hp
    by_cases hd : p ∣ v
    · have hnc : ¬p.Coprime v := fun hc => (hP p hp).1.coprime_iff_not_dvd.mp hc hd
      rw [progressionDensity_prime v (hP p hp).1,if_neg hnc,sub_zero,if_pos hd]
      exact g9_euler_factor_payment hL (hrough p (hS (mem_filter.mpr ⟨hp,hd⟩)))
    · have hc := (hP p hp).1.coprime_iff_not_dvd.mpr hd
      simp only [progressionDensity_prime v (hP p hp).1,if_pos hc,if_neg hd,mul_one,le_refl]
  have hpnonneg : ∀ p ∈ P, 0 ≤ 1-progressionDensity v p := by
    intro p hp
    exact sub_nonneg.mpr (progressionDensity_prime_nonneg_lt_one v (hP p hp).1 (hP p hp).2).2.le
  have he : (∏ p ∈ P,if p ∣ v then C else 1) = C^S.card := by
    rw [← prod_filter]
    simp only [prod_const]
    rfl
  calc
    _ ≤ ∏ p ∈ P,(1-1/((p : ℝ)-1))*(if p ∣ v then C else 1) := prod_le_prod hpnonneg hpoint
    _ = g9BaseEuler P*C^S.card := by rw [prod_mul_distrib,he]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hC ((card_le_card hS).trans hK)) (g9_baseEuler_nonneg P (fun p hp => (hP p hp).2))

/-- Finite nonnegative transfer of the preceding exact Euler correction. -/
theorem weighted_progressionEuler_rough_le {ι : Type*} (I : Finset ι) (a : ι → ℕ) (w : ι → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) {L : ℝ} {K : ℕ}
    (hL : 4 ≤ L) (hw : ∀ i ∈ I, 0 ≤ w i)
    (ha : ∀ i ∈ I, w i ≠ 0 → 0 < a i ∧
      (∀ p ∈ (a i).primeFactors,L ≤ (p : ℝ)) ∧ (a i).primeFactors.card ≤ K) :
    (∑ i ∈ I,w i*(∏ p ∈ P,(1-progressionDensity (a i) p))) ≤
      g9BaseEuler P*(1+1/(L-2))^K*(∑ i ∈ I,w i) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  by_cases hwi : w i = 0
  · simp only [hwi,zero_mul,mul_zero,le_refl]
  · obtain ⟨hi0,hr,hk⟩ := ha i hi hwi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (progressionEuler_rough_le P hP hi0 hL hr hk) (hw i hi)

end G11FiniteGate