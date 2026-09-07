import MathlibNt.SieveTheory.LiLiuGoldbachG11GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG11FouvryRectangle

open Finset Filter
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G11FiniteGate

/-- Reuse the proved inverse-totient gate on a weighted indexed family.
Zero weights need no support conditions; output multiplicities are not removed. -/
theorem weighted_bad_inverseTotientMass {ι : Type*} (I : Finset ι)
    (a : ι → ℕ) (w : ι → ℝ) {N Q K : ℕ} {z : ℝ}
    (hQ : Q ≤ N) (hz : 0 < z) (hw : ∀ i ∈ I, 0 ≤ w i)
    (ha : ∀ i ∈ I, w i ≠ 0 → 0 < a i ∧
      (∀ p ∈ (a i).primeFactors, z ≤ (p : ℝ)) ∧ (a i).primeFactors.card ≤ K) :
    (∑ d ∈ Icc 1 Q, (∑ i ∈ I, if ¬(a i).Coprime d then w i else 0) /
      (d.totient : ℝ)) ≤
        (2*K/z)*conductorHarmonicFactor N^2*(∑ i ∈ I, w i) := by
  calc
    _ = ∑ i ∈ I,
        (∑ d ∈ Icc 1 Q, if ¬(a i).Coprime d then (d.totient : ℝ)⁻¹ else 0)*w i := by
      simp only [div_eq_mul_inv, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _hi
      apply sum_congr rfl
      intro d _hd
      split_ifs <;> ring
    _ ≤ ∑ i ∈ I, ((2*K/z)*conductorHarmonicFactor N^2)*w i := by
      apply sum_le_sum
      intro i hi
      by_cases hwi : w i = 0
      · simp only [hwi, mul_zero, le_refl]
      · obtain ⟨hi0, hf, hk⟩ := ha i hi hwi
        exact mul_le_mul_of_nonneg_right
          (bad_inverseTotientMass_le hQ hi0 hz hf hk) (hw i hi)
    _ = _ := (mul_sum _ _ _).symm

end G11FiniteGate

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The existing twenty-factor bound extends to the actual short-prime product.
Repeated factors are allowed, and the short prime is counted at most once more. -/
theorem goldbachG11_effectiveProduct_mul_prime_factors {N m p : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) (hp : p.Prime)
    (hzp : (N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ)) :
    0 < m*p ∧ (∀ q ∈ (m*p).primeFactors, (N : ℝ)^(4/53 : ℝ) ≤ (q : ℝ)) ∧
      (m*p).primeFactors.card ≤ 21 := by
  have hm0 := (goldbachG11ProductSupport_data (mem_filter.mp hm).1).1
  obtain ⟨hf, _heq, hk⟩ := goldbachG11EffectiveProductSupport_primeFactors hm
  refine ⟨Nat.mul_pos hm0 hp.pos, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    rcases hqp.dvd_mul.mp hqd with hqm | hqp'
    · exact hf q (Nat.mem_primeFactors.mpr ⟨hqp, hqm, hm0.ne'⟩)
    · rcases (Nat.dvd_prime hp).mp hqp' with hq1 | hqpEq
      · exact False.elim (hqp.ne_one hq1)
      · simpa only [hqpEq] using hzp
  · rw [Nat.primeFactors_mul hm0.ne' hp.ne_zero]
    have hcard := card_union_le m.primeFactors p.primeFactors
    have hpcard : p.primeFactors.card = 1 := by simp [hp]
    omega

/-- Actual rectangular coprime-center deletion, with all G11 multiplicities.
This is a main-term gate estimate, not a triangle over the oscillatory discrepancy. -/
theorem goldbachG11_Fouvry_rectangle_mainGate {N Q : ℕ} (ε : ℝ)
    (hN : 0 < N) (hQ : Q ≤ N) (U V : Finset ℕ)
    (hU : U ⊆ goldbachG11EffectiveProductSupport N ε)
    (hV : ∀ p ∈ V, (N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ)) :
    let w := fun v : ℕ × ℕ =>
      (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) v.1 : ℝ)*
        (if v.2.Coprime N then primeSWBeta v.2 else 0)
    (∑ d ∈ Icc 1 Q, (∑ v ∈ U ×ˢ V, if ¬(v.1*v.2).Coprime d then w v else 0) /
      (d.totient : ℝ)) ≤
        (42/(N : ℝ)^(4/53 : ℝ))*conductorHarmonicFactor N^2*(∑ v ∈ U ×ˢ V, w v) := by
  dsimp only
  let w : ℕ × ℕ → ℝ := fun v =>
    (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) v.1 : ℝ)*
      (if v.2.Coprime N then primeSWBeta v.2 else 0)
  have hw : ∀ v ∈ U ×ˢ V, 0 ≤ w v := by
    intro v _hv
    apply mul_nonneg (Nat.cast_nonneg _)
    dsimp [primeSWBeta]
    split_ifs <;> norm_num
  have ha : ∀ v ∈ U ×ˢ V, w v ≠ 0 → 0 < v.1*v.2 ∧
      (∀ p ∈ (v.1*v.2).primeFactors, (N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ)) ∧
      (v.1*v.2).primeFactors.card ≤ 21 := by
    rintro ⟨m,p⟩ hv hne
    obtain ⟨hm, hpV⟩ := mem_product.mp hv
    have hp : p.Prime := by
      by_contra hn
      simp [w, primeSWBeta, hn] at hne
    exact goldbachG11_effectiveProduct_mul_prime_factors (hU hm) hp (hV p hpV)
  have h := G11FiniteGate.weighted_bad_inverseTotientMass (U ×ˢ V)
    (fun v => v.1*v.2) w hQ (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hw ha
  norm_num only [Nat.cast_ofNat, show (2 : ℝ)*21=42 by norm_num] at h
  exact h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig