import Wu08FourNormalizationOriginal
import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrection
import MathlibNt.SieveTheory.LiLiuGoldbachErrorFoundations

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour.Normalization

/-- All prime divisors of the genuine long cofactor are large. The rough
integer is retained, with no primality or squarefreeness assumption. -/
theorem longCell_prime_support {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hρ : 1 < ρ) {k : Key} {t : Long} (ht : t ∈ longCell N e ξ ρ k) :
    0 < longProduct t ∧ longProduct t < N ∧
      (∀ p ∈ (longProduct t).primeFactors,
        (N : ℝ)^truncatedSixthLowerAlpha ≤ (p : ℝ)) ∧
      (longProduct t).primeFactors.card ≤ 20 := by
  obtain ⟨htL,_,_,hzb,_,hface,_⟩ := mem_filter.mp ht
  obtain ⟨_,hb,_,hc,_,hd,_,hbc,hcd,_,_,_,hn,hr⟩ := mem_filter.mp htL
  have hbp := hb.pos
  have hcp := hc.pos
  have hdp := hd.pos
  have hm : 0 < longProduct t := by unfold longProduct; positivity
  have hmN : longProduct t < N := by
    have hh := mul_le_mul_of_nonneg_right (one_le_pow₀ hρ.le (n := k.1))
      (Nat.cast_nonneg (longProduct t))
    exact_mod_cast (show (longProduct t : ℝ) < N by linarith)
  have hf : ∀ p ∈ (longProduct t).primeFactors,
      (N : ℝ)^truncatedSixthLowerAlpha ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    change p ∣ t.1*t.2.1*t.2.2.1*t.2.2.2 at hpd
    have hbz : (N : ℝ)^truncatedSixthLowerAlpha ≤ (t.1 : ℝ) := hzb
    have hbcR : (t.1 : ℝ) ≤ t.2.1 := by exact_mod_cast hbc.le
    have hcdR : (t.2.1 : ℝ) ≤ t.2.2.1 := by exact_mod_cast hcd.le
    rcases hpp.dvd_mul.mp hpd with hleft | hnD
    · rcases hpp.dvd_mul.mp hleft with hleft | hdD
      · rcases hpp.dvd_mul.mp hleft with hbD | hcD
        · have he : p=t.1 := (Nat.dvd_prime hb).mp hbD |>.resolve_left hpp.ne_one
          simpa only [he] using hbz
        · have he : p=t.2.1 := (Nat.dvd_prime hc).mp hcD |>.resolve_left hpp.ne_one
          simpa only [he] using hbz.trans hbcR
      · have he : p=t.2.2.1 := (Nat.dvd_prime hd).mp hdD |>.resolve_left hpp.ne_one
        simpa only [he] using hbz.trans (hbcR.trans hcdR)
    · have hmin := (LiLiuPrereqBuchstab.rough_iff_minFac (by omega : t.2.2.2 ≠ 1)).mp hr
      exact hbz.trans (hmin.trans (by exact_mod_cast Nat.minFac_le_of_dvd hpp.two_le hnD))
  refine ⟨hm,hmN,hf,?_⟩
  have he : (longProduct t).primeFactors =
      MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.largePrimeDivisors
        (longProduct t) ((N : ℝ)^truncatedSixthLowerAlpha) := by
    symm
    exact filter_eq_self.mpr hf
  rw [he]
  exact largePrimeDivisors_card_le_twenty hm hmN (by norm_num [truncatedSixthLowerAlpha])

/-- This lower cutoff is obtained from occupied witnesses and the actual short
interval. In particular the entire cell, not just its original atoms, is rough. -/
theorem cell_full_cofactor_support {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : Key} (hk : k ∈ occupied N e ξ ρ) (hbig : 3 ≤ ρ^k.1)
    {m a : ℕ} (hm : m ∈ products (longCell N e ξ ρ k))
    (ha : a ∈ shortCell ρ k) (haβ : beta N a ≠ 0) :
    0 < m*a ∧
      (∀ p ∈ (m*a).primeFactors, (N : ℝ)^truncatedSixthLowerAlpha/2 ≤ (p : ℝ)) ∧
      (m*a).primeFactors.card ≤ 21 := by
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hm
  obtain ⟨hm0,_,hf,hcard⟩ := longCell_prime_support hρ ht
  have hap : a.Prime := by
    by_contra hh
    simp [beta,primeSWBeta,hh] at haβ
  have hgeom := occupied_geometry hξ hρ hρu hk
  have has := (shortCell_mem hρ hρu k hbig a).mp ha
  have hlow : (N : ℝ)^truncatedSixthLowerAlpha/2 ≤ (a : ℝ) := by
    have hpow := pow_pos (by linarith : 0 < ρ) k.1
    linarith [hgeom.2.2.2.1]
  refine ⟨Nat.mul_pos hm0 hap.pos,?_,?_⟩
  · intro p hp
    obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    rcases hpp.dvd_mul.mp hpd with hpm | hpa
    · have hh := hf p (Nat.mem_primeFactors.mpr ⟨hpp,hpm,hm0.ne'⟩)
      have hh0 := rpow_nonneg (Nat.cast_nonneg N) truncatedSixthLowerAlpha
      linarith
    · have he : p=a := (Nat.dvd_prime hap).mp hpa |>.resolve_left hpp.ne_one
      simpa only [he] using hlow
  · rw [Nat.primeFactors_mul hm0.ne' hap.ne_zero]
    have hc := card_union_le (longProduct t).primeFactors a.primeFactors
    have haC : a.primeFactors.card=1 := by simp [hap]
    omega

/-- Multiplicity-preserving scalar mass of a whole actual rectangle. -/
def cellMass (N : ℕ) (e : Bool) (ξ ρ : ℝ) (k : Key) : ℝ :=
  ∑ m ∈ products (longCell N e ξ ρ k), ∑ a ∈ shortCell ρ k,
    alpha (longCell N e ξ ρ k) m*beta N a

/-- The full-cofactor correction has 21 distinct-prime payments, including a
and every prime divisor of rough n. It is not the three-prime U8 correction. -/
def fullEulerCorrection (N : ℕ) : ℝ :=
  (1+1/((N : ℝ)^truncatedSixthLowerAlpha/2-2))^21

theorem cellMass_labels (N : ℕ) (e : Bool) (ξ ρ : ℝ) (k : Key) :
    cellMass N e ξ ρ k = ∑ _t ∈ longCell N e ξ ρ k, ∑ a ∈ shortCell ρ k, beta N a := by
  rw [alpha_sum (longCell N e ξ ρ k) (fun _ => ∑ a ∈ shortCell ρ k, beta N a)]
  simp only [cellMass,mul_sum]

theorem cell_euler_upper {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hEven : Even N) (hbigN : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2)
    {k : Key} (hk : k ∈ occupied N e ξ ρ) :
    (∑ m ∈ products (longCell N e ξ ρ k), ∑ a ∈ shortCell ρ k,
      alpha (longCell N e ξ ρ k) m*beta N a*
        (∏ p ∈ properPrimes N, (1-progressionDensity (m*a) p))) ≤
      g9BaseEuler (properPrimes N)*fullEulerCorrection N*cellMass N e ξ ρ k := by
  have hg := occupied_geometry hξ hρ hρu hk
  have hbig : 3 ≤ ρ^k.1 := by linarith [hg.2.2.2.1]
  let L : ℝ := (N : ℝ)^truncatedSixthLowerAlpha/2
  let C : ℝ := 1+1/(L-2)
  have hC : 1 ≤ C := by dsimp [C,L]; have := one_div_nonneg.mpr (show 0 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2-2 by linarith); linarith
  have hP := fouvryG9SievePrimes_odd hEven (sqrt N)
  unfold cellMass
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  by_cases hz : beta N a = 0
  · simp [hz]
  obtain ⟨hm0,hrough,hcard⟩ := cell_full_cofactor_support hξ hρ hρu hk hbig hm ha hz
  have hpoint : ∀ p ∈ properPrimes N,
      1-progressionDensity (m*a) p ≤
        (1-1/((p : ℝ)-1))*(if p ∣ m*a then C else 1) := by
    intro p hp
    rw [progressionDensity_prime _ (hP p hp).1]
    by_cases hd : p ∣ m*a
    · rw [if_neg (fun hh => (hP p hp).1.coprime_iff_not_dvd.mp hh hd),if_pos hd,sub_zero]
      exact g9_euler_factor_payment hbigN (hrough p (Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hd,hm0.ne'⟩))
    · rw [if_pos ((hP p hp).1.coprime_iff_not_dvd.mpr hd),if_neg hd,mul_one]
  have hsub : (properPrimes N).filter (fun p => p ∣ m*a) ⊆ (m*a).primeFactors := by
    intro p hp
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hd,hm0.ne'⟩
  have hprod : (∏ p ∈ properPrimes N, (1-progressionDensity (m*a) p)) ≤
      g9BaseEuler (properPrimes N)*fullEulerCorrection N := by
    calc
      _ ≤ ∏ p ∈ properPrimes N, (1-1/((p : ℝ)-1))*(if p ∣ m*a then C else 1) :=
        prod_le_prod (fun p hp => sub_nonneg.mpr (progressionDensity_prime_nonneg_lt_one
          (m*a) (hP p hp).1 (hP p hp).2).2.le) hpoint
      _ = g9BaseEuler (properPrimes N)*C^((properPrimes N).filter (fun p => p ∣ m*a)).card := by
        rw [prod_mul_distrib,← prod_filter]
        simp only [prod_const,g9BaseEuler]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hC ((card_le_card hsub).trans hcard))
        (g9_baseEuler_nonneg _ (fun p hp => (hP p hp).2))
  simpa only [mul_comm (g9BaseEuler (properPrimes N)*fullEulerCorrection N)] using
    mul_le_mul_of_nonneg_left hprod (mul_nonneg (alpha_nonneg _ _) (beta_nonneg _ _))

#print axioms cell_full_cofactor_support
#print axioms cell_euler_upper
end Wu08FirstPrimeFour.Normalization
