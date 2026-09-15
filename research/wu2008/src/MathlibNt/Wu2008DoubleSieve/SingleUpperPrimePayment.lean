import MathlibNt.Wu2008DoubleSieve.SingleUpperQuadrature

namespace Wu2008DoubleSieve.SingleUpperPrimePayment
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperQuadrature
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The coefficient-one upper bound consumes the genuine logarithmic
integral remainder, rather than assuming a new li asymptotic. -/
theorem trueLi_upper {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      logarithmicIntegral N ≤ (1+τ)*(N : ℝ)/log N := by
  obtain ⟨C,hC,hrem⟩ := MathlibNt.SieveTheory.LiuWeight.eventually_abs_liuLogarithmicIntegralRemainder_le 0
  obtain ⟨T,hT⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hrem)
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨S,hS⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (C/τ)))
  refine ⟨max 4 (max T S), le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh := hT N ((le_max_left T S).trans ((le_max_right _ _).trans hN))
    (by exact_mod_cast (show 2 ≤ N by omega))
  have hb : C ≤ τ*log (N : ℝ) := by
    have h := (div_le_iff₀ hτ).mp
      (hS N ((le_max_right T S).trans ((le_max_right _ _).trans hN)))
    simpa only [mul_comm] using h
  have hp := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (N : ℝ)/log (N : ℝ)^2 by positivity)
  have he : τ*log (N : ℝ)*((N : ℝ)/log (N : ℝ)^2) = τ*N/log N := by field_simp
  rw [he] at hp
  have hrem' : |logarithmicIntegral N-(N : ℝ)/log N| ≤ C*N/log (N : ℝ)^2 := hh
  have hh' := (abs_le.mp hrem').2
  rw [← mul_div_assoc] at hp
  calc
    _ ≤ (N : ℝ)/log N + C*N/log (N : ℝ)^2 := by linarith
    _ ≤ (N : ℝ)/log N + τ*N/log N := add_le_add le_rfl hp
    _ = _ := by ring

/-- One full closed prime mass, including both atoms, stays bounded.
The scale change is exact and the threshold precedes moving endpoints. -/
theorem reciprocal_mass_bound : ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    ∀ a b : ℝ, 1/15 ≤ a → a ≤ b → b ≤ 1/3 →
      (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ)) ≤ 5 := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(2/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (ht.eventually (primeOrdered_reciprocal_uniform 1 (by norm_num)))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN a b ha hab hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := hT N ((le_max_right _ _).trans hN) (3/2*a) (3/2*b)
    (by linarith) (by linarith) (by linarith)
  have he (t : ℝ) : ((N : ℝ)^(2/3 : ℝ))^(3/2*t) = (N : ℝ)^t := by
    rw [← rpow_mul hN0.le, show (2/3 : ℝ)*(3/2*t) = t by ring]
  simp only [he] at h
  have hi := (primeOrdered_exponent_density_bounds (A := 3/2*a) (B := 3/2*b)
    (by linarith) (by linarith) (by linarith)).2
  linarith [(abs_lt.mp h).2]

/-- A pointwise correction pays p-2 with its actual positive denominator. -/
theorem reciprocal_sub_two {p τ : ℝ} (hτ : 0 < τ) (hp : 2+2/τ ≤ p) :
    2 < p ∧ 1/(p-2) ≤ (1+τ)/p := by
  have hp2 : 2 < p := lt_of_lt_of_le (by have := div_pos (by norm_num : (0 : ℝ) < 2) hτ; linarith) hp
  refine ⟨hp2, ?_⟩
  apply (div_le_div_iff₀ (by linarith : 0 < p-2) (by linarith : 0 < p)).mpr
  have hh := (div_le_iff₀ hτ).mp (show 2/τ ≤ p-2 by linarith)
  nlinarith

/-- A single threshold pays both the p-2 and the phi(p)=p-1 correction
uniformly for every later prime in the enlarged exponent slab. -/
theorem denominator_payment {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ p : ℕ,
      p.Prime → (N : ℝ)^(1/15 : ℝ) ≤ p →
      2 < p ∧ 1/((p : ℝ)-2) ≤ (1+τ)/p ∧
        1/(Nat.totient p : ℝ) ≤ (1+τ)/p := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(1/15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2+2/τ)))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN p hpp hp
  have hb := reciprocal_sub_two hτ ((hT N ((le_max_right _ _).trans hN)).trans hp)
  have hp2 : 2 < p := by exact_mod_cast hb.1
  refine ⟨hp2,hb.2, ?_⟩
  rw [Nat.totient_prime hpp, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  exact (one_div_le_one_div_of_le (by linarith : 0 < (p : ℝ)-2) (by linarith)).trans hb.2

/-- Positivity needed when the coprimality mask is enlarged. -/
theorem weight_nonneg {δ t : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (1/15 : ℝ) (1/3)) : 0 ≤ weight δ t := by
  have hs := argument_mem hδ hδhi ht
  have hs0 : 0 < ((1/2-δ)-t)/truncatedSixthLowerAlpha := by linarith [hs.1]
  have hA : 0 ≤ wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha) := by
    unfold wuUpperCoefficient
    have := MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_pos hs0
    positivity
  exact div_nonneg hA (by linarith [ht.2])

end Wu2008DoubleSieve.SingleUpperPrimePayment
