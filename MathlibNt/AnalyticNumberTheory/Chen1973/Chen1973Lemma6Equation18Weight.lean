import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open Filter Finset
open scoped BigOperators

namespace ChenEq18

/-- Elementary prime-factor splitting, uniform in the integer below R. -/
theorem card_primeFactors_mul_log_le {n : ℕ} {R K : ℝ}
    (hn : 1 ≤ n) (hnR : (n : ℝ) ≤ R) (hK : 1 ≤ K) :
    (n.primeFactors.card : ℝ) * Real.log K ≤
      K * Real.log K + Real.log R := by
  classical
  let S := n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ K)
  let T := n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ K)
  have hp (p : ℕ) (hp : p ∈ n.primeFactors) : 1 ≤ p :=
    (Nat.prime_of_mem_primeFactors hp).one_le
  have hS : (S.card : ℝ) ≤ K := by
    have hs : S ⊆ Finset.Icc 1 ⌊K⌋₊ := by
      intro p hpS
      obtain ⟨hpS, hpK⟩ := Finset.mem_filter.mp hpS
      exact Finset.mem_Icc.mpr ⟨hp p hpS, Nat.le_floor hpK⟩
    have hc : S.card ≤ ⌊K⌋₊ := by
      simpa using Finset.card_le_card hs
    exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (by linarith))
  have hsum : (∑ p ∈ n.primeFactors, Real.log (p : ℝ)) ≤ Real.log R := by
    rw [← Real.log_prod (fun p hp' => by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hp p hp'))))]
    have hprod : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ (n : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (by omega : 0 < n) (Nat.prod_primeFactors_dvd n)
    have hpos : 0 < ∏ p ∈ n.primeFactors, (p : ℝ) := by
      apply Finset.prod_pos
      intro p hp'
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hp p hp')
    exact Real.log_le_log hpos (hprod.trans hnR)
  have hT : (T.card : ℝ) * Real.log K ≤ Real.log R := by
    calc
      (T.card : ℝ) * Real.log K = ∑ p ∈ T, Real.log K := by simp
      _ ≤ ∑ p ∈ T, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hpT
        exact Real.log_le_log (by linarith) (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hpT).2))
      _ ≤ ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp' _
        exact Real.log_nonneg (by exact_mod_cast hp p hp')
      _ ≤ Real.log R := hsum
  have hcard : (S.card : ℝ) + T.card = n.primeFactors.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := n.primeFactors)
      (fun p : ℕ => (p : ℝ) ≤ K)
  have hsmall := mul_le_mul_of_nonneg_right hS (Real.log_nonneg hK)
  rw [← hcard, add_mul]
  exact add_le_add hsmall hT

lemma log_three_lt_four_thirds : Real.log 3 < (4 : ℝ) / 3 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).mpr
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)
  linarith

/-- An elementary exponential-domination cutoff in the log-log coordinate. -/
lemma eventually_aux : ∀ᶠ t : ℝ in atTop,
    1 ≤ t ∧ t * Real.exp (t / 2) ≤ Real.exp t / 4 := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  refine ⟨ht1, ?_⟩
  have ht0 : 0 ≤ t := by linarith
  simp only [pow_one, Real.norm_eq_abs, abs_of_nonneg ht0,
    abs_of_pos (Real.exp_pos _)] at ht
  have hm := mul_le_mul_of_nonneg_right ht (Real.exp_pos (t / 2)).le
  have he : Real.exp (1 / 2 * t) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    t * Real.exp (t / 2) ≤
        (1 / 4 * Real.exp (1 / 2 * t)) * Real.exp (t / 2) := hm
    _ = Real.exp t / 4 := by rw [mul_assoc, he]; ring

/-- The uniform form of Chen's equation (18); the threshold precedes n. -/
theorem uniform_prime_factor_bound : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ R →
      (3 : ℝ) ^ n.primeFactors.card ≤
        Real.exp (3 * Real.log R / Real.log (Real.log R)) := by
  obtain ⟨T, hT⟩ := (Filter.eventually_atTop.mp eventually_aux)
  refine ⟨Real.exp (Real.exp (max T 1)), ?_⟩
  intro R hR n hn hnR
  have hRpos : 0 < R := (Real.exp_pos _).trans_le hR
  have hlog : Real.exp (max T 1) ≤ Real.log R := by
    simpa using Real.log_le_log (Real.exp_pos _) hR
  have hlogpos : 0 < Real.log R := (Real.exp_pos _).trans_le hlog
  have htt : max T 1 ≤ Real.log (Real.log R) := by
    simpa using Real.log_le_log (Real.exp_pos _) hlog
  set t := Real.log (Real.log R) with htdef
  obtain ⟨ht1, htaux⟩ := hT t ((le_max_left _ _).trans htt)
  have htpos : 0 < t := by linarith
  have hexpt : Real.exp t = Real.log R := Real.exp_log hlogpos
  have hK : 1 ≤ Real.exp (t / 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hc := card_primeFactors_mul_log_le hn hnR hK
  rw [Real.log_exp] at hc
  rw [hexpt] at htaux
  -- Splitting at K = exp (t / 2) and using the cutoff bounds the number of factors.
  have hclog : (n.primeFactors.card : ℝ) * t ≤ (9 / 4 : ℝ) * Real.log R := by
    nlinarith only [hc, htaux]
  have hlog3pos : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hweighted : (n.primeFactors.card : ℝ) * Real.log 3 * t ≤ 3 * Real.log R := by
    have h1 := mul_le_mul_of_nonneg_left hclog hlog3pos
    have h2 := mul_le_mul_of_nonneg_right log_three_lt_four_thirds.le hlogpos.le
    nlinarith only [h1, h2]
  have hfinal : (n.primeFactors.card : ℝ) * Real.log 3 ≤ 3 * Real.log R / t :=
    (le_div_iff₀ htpos).mpr hweighted
  calc
    (3 : ℝ) ^ n.primeFactors.card = Real.exp ((n.primeFactors.card : ℝ) * Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ Real.exp (3 * Real.log R / Real.log (Real.log R)) := Real.exp_le_exp.mpr hfinal

end ChenEq18

namespace AnalyticNumberTheory.LargeSieve

/-- Includes level zero, and does not require any branch or pair parameters. -/
lemma chenEq18_actual_conductor_bounds {x L level d : ℕ}
    (hd : d ∈ chen1973Lemma6ConductorBlock x L level) :
    1 ≤ d ∧ d ≤ L * 2 ^ level := by
  unfold chen1973Lemma6ConductorBlock at hd
  split_ifs at hd with hlevel
  · subst level
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hd
    simpa using And.intro (Nat.le_of_lt hd.1.1) hd.1.2
  · simp only [chen1973Lemma6DyadicShell, Finset.mem_filter, Finset.mem_Ioc] at hd
    exact ⟨Nat.le_of_lt hd.1.1.1, hd.1.1.2⟩

/-- The existing Eq19I is a finite maximum W, NOT the printed exponential I.
This theorem supplies the missing upper bridge without changing that definition. -/
theorem chenEq18_actual_W_sq_uniform : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
    ∀ x L level : ℕ, ((L * 2 ^ level : ℕ) : ℝ) ≤ R →
      chen1973Lemma6Eq19I x L level ^ 2 ≤
        Real.exp (6 * Real.log R / Real.log (Real.log R)) := by
  classical
  obtain ⟨R₀, hR₀⟩ := ChenEq18.uniform_prime_factor_bound
  refine ⟨max R₀ 1, ?_⟩
  intro R hR x L level hcell
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  have hb := hR₀ R ((le_max_left _ _).trans hR)
  have hone : 1 ≤ Real.exp (3 * Real.log R / Real.log (Real.log R)) := by
    simpa using hb 1 le_rfl (by simpa using hR1)
  have hW : chen1973Lemma6Eq19I x L level ≤
      Real.exp (3 * Real.log R / Real.log (Real.log R)) := by
    unfold chen1973Lemma6Eq19I
    apply Finset.max'_le
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · simpa using (Finset.mem_singleton.mp ha ▸ hone)
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hd1, hdup⟩ := chenEq18_actual_conductor_bounds hd
      exact hb d hd1 ((Nat.cast_le.mpr hdup).trans hcell)
  calc
    chen1973Lemma6Eq19I x L level ^ 2 ≤
        Real.exp (3 * Real.log R / Real.log (Real.log R)) ^ 2 :=
      pow_le_pow_left₀ (chen1973Lemma6Eq19I_pos x L level).le hW 2
    _ = Real.exp (6 * Real.log R / Real.log (Real.log R)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- A single x-threshold works before ALL actual-cell parameters, including level zero.
Here Q₀ = 2^level (log x)^100, and the right-hand side is literally the printed I. -/
theorem chenEq18_actual_W_sq_le_source_I : ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
    ∀ L level : ℕ, (L : ℝ) ≤ Real.log x ^ (100 : ℕ) →
      chen1973Lemma6Eq19I x L level ^ 2 ≤
        Real.exp (6 * Real.log ((2 : ℝ) ^ level * Real.log x ^ (100 : ℕ)) /
          Real.log (Real.log ((2 : ℝ) ^ level * Real.log x ^ (100 : ℕ)))) := by
  obtain ⟨R₀, hR₀⟩ := chenEq18_actual_W_sq_uniform
  refine ⟨Real.exp (max R₀ 1), ?_⟩
  intro x hx L level hL
  have hlog : max R₀ 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hx
  have hlog1 : 1 ≤ Real.log x := (le_max_right _ _).trans hlog
  have hp : Real.log x ≤ Real.log x ^ (100 : ℕ) := by
    simpa using pow_le_pow_right₀ hlog1 (by norm_num : (1 : ℕ) ≤ 100)
  have hpow : (1 : ℝ) ≤ 2 ^ level := one_le_pow₀ (by norm_num)
  have hlogpow : 0 ≤ Real.log x ^ (100 : ℕ) := by positivity
  have hQ : R₀ ≤ (2 : ℝ) ^ level * Real.log x ^ (100 : ℕ) := by
    calc
      R₀ ≤ Real.log x := (le_max_left _ _).trans hlog
      _ ≤ Real.log x ^ (100 : ℕ) := hp
      _ ≤ (2 : ℝ) ^ level * Real.log x ^ (100 : ℕ) := le_mul_of_one_le_left hlogpow hpow
  apply hR₀ _ hQ x L level
  push_cast
  calc
    (L : ℝ) * (2 : ℝ) ^ level ≤ Real.log x ^ (100 : ℕ) * (2 : ℝ) ^ level :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ = _ := mul_comm _ _

end AnalyticNumberTheory.LargeSieve
