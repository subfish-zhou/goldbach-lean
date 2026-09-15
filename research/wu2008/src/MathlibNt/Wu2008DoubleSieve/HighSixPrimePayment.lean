import MathlibNt.Wu2008DoubleSieve.HighSixNormalization
import MathlibNt.Wu2008DoubleSieve.Omega2IntegralTransform
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientDivisors

namespace Wu2008DoubleSieve.HighSix
open Finset Real Filter Set
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Exact inserted Euler weight on the original separated prime pair. -/
theorem pair_euler_split {N p q : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (he : Even N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N)
    (hq : q ∈ primeWindow N (z N δ p) (w N δ p)) :
    wuSingularSeries ((p*q)*N)/(Nat.totient (p*q) : ℝ) =
      wuSingularSeries (p*N)/((Nat.totient p : ℝ)*((q : ℝ)-2)) := by
  obtain ⟨hqp, hqN, _, _⟩ := mem_primeWindow.mp hq
  have hq2 : 2 < q := by
    have h2N : 2 ∣ N := even_iff_two_dvd.mp he
    have hqn : q ≠ 2 := by
      intro h; subst q
      exact (hqp.coprime_iff_not_dvd.mp hqN) h2N
    have := hqp.two_le
    omega
  have hqpnd : ¬q ∣ p := by
    intro hd
    rcases (Nat.dvd_prime (mem_primeWindow.mp hp).1).mp hd with h | h
    · exact hqp.ne_one h
    · exact (Nat.ne_of_lt (inner_lt_outer hN hδ hδhi hp hq)) h
  rw [wu_inserted_arithmetic_weight (by omega) (mem_primeWindow.mp hp).1.pos hqp hq2 hqN,
    if_neg hqpnd]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The pure-prime integral and the genuine deleted-divisor estimate share
one ambient threshold, before the moving outer prime. No source-box premise. -/
theorem moving_prime_integral {δ B ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ p ∈ P N,
      ∀ f : ℝ → ℝ, MonotoneOn f (Icc 1 10) →
      (∀ u ∈ Icc (1 : ℝ) 10, |f u| ≤ B) →
      |(∑ q ∈ primeWindow N (z N δ p) (w N δ p),
        f (S*(1-log q/log (R N δ p))) /
          (((q : ℝ)-2)*(1-log q/log (R N δ p)))) -
        ∫ u in (1-1/s)..(1-1/S), f (S*u)/(u*(1-u))| ≤ ε := by
  obtain ⟨Q0, _, hprime⟩ := omega2_source_prime_integral_uniform hB (half_pos hε)
  obtain ⟨T1, hdelete⟩ := primeCoefficient_all_to_coprime_uniform
    (show (0 : ℝ) < 1/25 by norm_num) hB (half_pos hε)
  have hgrow : Tendsto (fun N : ℕ => (N : ℝ)^(1/2-δ-right)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [right] at *; linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp (hgrow.eventually (eventually_ge_atTop Q0))
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hN p hp f hf hfb
  have hN2 : 2 ≤ N := by omega
  have hr := ratio_bounds hN2 hδ hδhi hp
  have hprime' := hprime (R N δ p) ((hT2 N (by omega)).trans hr.2.2)
    f hf hfb s S (by norm_num [s]) (by norm_num [s,S])
    (by norm_num [S]) (by norm_num [S])
  have hb (q : ℕ) (hq : q ∈ primeWindow 1 (z N δ p) (w N δ p)) :
      |f (S*(1-log q/log (R N δ p)))| ≤ B := by
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (mem_primeWindow.mp hq).1.one_lt
    have ht := buchstab_shifted_parameter hr.1 hq1
      (show 0 < s by norm_num [s]) (show 0 < S by norm_num [S])
      (mem_primeWindow.mp hq).2.2.1 (mem_primeWindow.mp hq).2.2.2
    have hcoord := omega2_coordinate_mem (show 3 ≤ S by norm_num [S])
      (show S ≤ 5 by norm_num [S])
      (show log (R N δ p)/log q-1 ∈ Icc (1 : ℝ) 10 by
        rw [log_div (by linarith [hr.1] : R N δ p ≠ 0)
          (by linarith : (q : ℝ) ≠ 0), sub_div, div_self (log_pos hq1).ne'] at ht
        constructor <;> norm_num [s,S] at ht ⊢ <;> linarith [ht.1,ht.2])
    rw [omega2_prime_coordinate hr.1 hq1] at hcoord
    exact hfb _ hcoord
  have hd := hdelete N (by omega) (R N δ p) (z N δ p) (w N δ p)
    (fun q => f (S*(1-log q/log (R N δ p)))) hr.1
    (inner_lower_cutoff hN2 hδ hδhi hp)
    (rpow_le_rpow_of_exponent_le hr.1.le (show 1/s ≤ (1/2 : ℝ) by norm_num [s])) hb
  change |(∑ q ∈ primeWindow 1 (z N δ p) (w N δ p), _) - _| ≤ ε/2 at hprime'
  have hd' := (abs_sub_comm _ _).trans_le hd
  exact (abs_sub_le _ _ _).trans ((add_le_add hd' hprime').trans (by linarith))

end Wu2008DoubleSieve.HighSix
