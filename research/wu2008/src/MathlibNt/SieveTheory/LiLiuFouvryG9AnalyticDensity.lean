import MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensityDimension
import MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpper
import MathlibNt.SieveTheory.LiLiuFouvryG9MotherSieve

noncomputable section
open Finset
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual progression density enters the extended upper theorem with a
single dimension constant selected before all products and carriers. -/
theorem g9ProgressionDensity_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧
      ∀ η : ℝ, 0 < η → η < 1/8 → ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧
      ∀ Q : ℝ, Q₀ ≤ Q → ∀ v : ℕ, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2 < p) → ∀ z : ℝ, 2 ≤ z → z ≤ Q^2 →
      (∀ p ∈ P, (p : ℝ) < z) →
      externalDensity true P (externalInternalLevel Q η) η z (progressionDensity v) ≤
        (∏ p ∈ P, (1-progressionDensity v p))*
          (jr1965F (Real.log Q/Real.log z)+
            C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))) := by
  obtain ⟨C,hC,hupper⟩ := G9ExtendedUpper.exists_externalFamilyDensity_upper_extended
  obtain ⟨K,hK,hdim⟩ := exists_progressionOmega_dimensionOneProductBound
  refine ⟨C,hC,K,hK,?_⟩
  intro η hη hηu
  obtain ⟨Q₀,hQ₀,hQ⟩ := hupper η hη hηu
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQN v P hP z hz hzQ hcut
  have h := hQ Q hQN P (fun p hp => (hP p hp).1) (progressionOmega v)
    (progressionOmega_isMultiplicative v)
    (fun p hp => progressionOmega_prime_nonneg_lt_one v (hP p hp).1 (hP p hp).2)
    z hz hzQ hcut K (by linarith) (hdim v P hP)
  change externalDensity true P (externalInternalLevel Q η) η z (primeDensity (progressionOmega v)) ≤
    (∏ p ∈ P, (1-primeDensity (progressionOmega v) p))*_ at h
  simpa only [primeDensity_progressionOmega] using h

/-- Evenness removes the prime 2 from the literal sieve carrier. -/
theorem fouvryG9SievePrimes_odd {N : ℕ} (hEven : Even N) (z : ℝ) :
    ∀ p ∈ fouvryG9SievePrimes N z, p.Prime ∧ 2 < p := by
  intro p hp
  obtain ⟨hprime,hcop,_⟩ := (fouvryG9SievePrimes_mem N p z).mp hp
  have hpne : p ≠ 2 := by
    intro h
    subst p
    exact Nat.prime_two.coprime_iff_not_dvd.mp hcop (even_iff_two_dvd.mp hEven)
  exact ⟨hprime, by have := hprime.two_le; omega⟩

/-- The actual sqrt(N) cutoff lies in the extended, not necessarily old, domain. -/
theorem g9WF_sqrt_cutoff {N T δ : ℝ} (hN : 4 ≤ N) (hT : 1 ≤ T)
    (hTu : T ≤ N^(1/10 : ℝ)) (hδ : 0 ≤ δ) (hδu : δ < 1/4) :
    2 ≤ Real.sqrt N ∧ Real.sqrt N ≤ (N^(5/9-δ)/T^(5/9 : ℝ))^2 := by
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  obtain ⟨hlo,_⟩ := g9WF_level_window hN1 hT hTu hδ
  have hp0 : 0 ≤ N^(1/2-δ) := Real.rpow_nonneg hN0 _
  have heq : (N^(1/2-δ))^2 = N^(1-2*δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1
    ring
  constructor
  · nlinarith [Real.sq_sqrt hN0,Real.sqrt_nonneg N]
  · calc
      Real.sqrt N = N^(1/2 : ℝ) := Real.sqrt_eq_rpow _
      _ ≤ N^(1-2*δ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (N^(1/2-δ))^2 := heq.symm
      _ ≤ _ := by nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
