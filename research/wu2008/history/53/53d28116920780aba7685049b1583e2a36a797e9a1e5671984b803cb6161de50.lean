import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientContinuous
import MathlibNt.Wu2008DoubleSieve.BoxMassUpper

/-!
# Paying the final prime cell at the square-root endpoint

The old Abel estimate samples one extra point `b+1`. We apply it only
through `b-1` and pay the last prime and true-li cell separately.
Thus `b ≤ sqrt q` suffices, including the source endpoint s=2.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem primeCoefficient_last_cell_le {f : ℝ → ℝ} {q B : ℝ}
    (hB : 0 ≤ B) (hfb : ∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B)
    {a n : ℕ} (ha : 4 ≤ a) (han : a ≤ n) (hq : 1 < q)
    (hb : ((n + 1 : ℕ) : ℝ) ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log (a : ℝ) - 1 ≤ 10) :
    |primeCoefficientQuadratureError f q n (n + 1)| ≤
      (1 + 1 / log (a : ℝ)) * (4 * B / (a : ℝ)) := by
  have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hanR : (a : ℝ) ≤ n := by exact_mod_cast han
  have hnR : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have hdom := wuPrime_continuous_argument_mem hq (by linarith : 1 < (a : ℝ))
    (show ((n + 1 : ℕ) : ℝ) ∈ Set.Icc (a : ℝ) (n + 1 : ℕ) from
      ⟨hanR.trans hnR, le_rfl⟩) hb haq
  have hk := reboxing_prime_weight_le_four_div hq (haR.trans (hanR.trans hnR)) hb
  have hw : |wuPrimeCoefficientWeight f q (n + 1)| ≤ 4 * B / (a : ℝ) := by
    unfold wuPrimeCoefficientWeight
    rw [div_eq_mul_inv, abs_mul,
      abs_of_nonneg (show 0 ≤ ((((n + 1 : ℕ) : ℝ) - 2) *
        (1 - log (n + 1 : ℕ) / log q))⁻¹ by simpa only [one_div] using hk.1)]
    rw [← one_div]
    calc
      _ ≤ B * (1 / ((((n + 1 : ℕ) : ℝ) - 2) * (1 - log (n + 1 : ℕ) / log q))) :=
        mul_le_mul_of_nonneg_right (hfb _ hdom) hk.1
      _ ≤ B * (4 / (n + 1 : ℕ)) := mul_le_mul_of_nonneg_left hk.2 hB
      _ ≤ B * (4 / (a : ℝ)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) (by linarith) (hanR.trans hnR)) hB
      _ = _ := by ring
  have hli0 : 0 ≤ logarithmicIntegral (n + 1 : ℕ) - logarithmicIntegral n := by
    have h := box_trueLi_sub_lower (show (2 : ℝ) ≤ n by linarith) hnR
    exact (div_nonneg (sub_nonneg.mpr hnR) (log_pos (by linarith : 1 < ((n + 1 : ℕ) : ℝ))).le).trans h
  have hli1 : logarithmicIntegral (n + 1 : ℕ) - logarithmicIntegral n ≤ 1 / log (a : ℝ) := by
    apply (box_trueLi_sub_upper (show (2 : ℝ) ≤ n by linarith) hnR).trans
    push_cast
    rw [add_sub_cancel_left]
    exact one_div_le_one_div_of_le (log_pos (by linarith))
      (log_le_log (by linarith) hanR)
  have heq : primeCoefficientQuadratureError f q n (n + 1) =
      (if (n + 1).Prime then wuPrimeCoefficientWeight f q (n + 1) else 0) -
      (logarithmicIntegral (n + 1 : ℕ) - logarithmicIntegral n) *
        wuPrimeCoefficientWeight f q (n + 1) := by
    simp [primeCoefficientQuadratureError, Finset.sum_filter]
  rw [heq]
  apply (abs_sub _ _).trans
  have hprime : |if (n + 1).Prime then wuPrimeCoefficientWeight f q (n + 1) else 0| ≤
      4 * B / (a : ℝ) := by
    split_ifs
    · exact hw
    · simp only [abs_zero]
      positivity
  rw [abs_mul, abs_of_nonneg hli0]
  have hmul := mul_le_mul hli1 hw (abs_nonneg _) (by positivity : 0 ≤ 1 / log (a : ℝ))
  nlinarith only [hprime, hmul]

/-- The global PNT quadrature with no extra sample beyond `b`. The last
cell is paid rather than extending the coefficient past its domain. -/
theorem primeCoefficient_global_trueLi_quadrature_endpoint :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℕ, ∀ (f : ℝ → ℝ) (B q : ℝ),
      MonotoneOn f (Set.Icc 1 10) → 0 ≤ B →
      (∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B) →
      ∀ a b : ℕ, X0 ≤ a → 4 ≤ a → a ≤ b →
        1 ≤ log (a : ℝ) → 1 < q → 2 ≤ log q →
        (b : ℝ) ≤ q ^ (1 / 2 : ℝ) →
        log q / log (a : ℝ) - 1 ≤ 10 →
        |primeCoefficientQuadratureError f q a b| ≤ C * B / log (a : ℝ) := by
  obtain ⟨C, hC, X0, hglobal⟩ := primeCoefficient_global_trueLi_quadrature
  refine ⟨C + 8, by linarith, X0, ?_⟩
  intro f B q hf hB hfb a b hXa ha hab hla hq hlq hqb haq
  by_cases he : a = b
  · subst b
    simp only [primeCoefficientQuadratureError, Finset.Ico_self, filter_empty,
      sum_empty, sub_self, abs_zero]
    positivity
  have hab' : a ≤ b - 1 := by omega
  have hb1 : b - 1 + 1 = b := by omega
  have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have harg : log q / log (a + 1 : ℕ) - 1 ≤ 10 := by
    apply le_trans _ haq
    exact sub_le_sub_right
      (div_le_div_of_nonneg_left (log_pos hq).le (by linarith)
        (log_le_log (by linarith) (by push_cast; linarith))) 1
  have hg := hglobal f B q hf hB hfb a (b - 1) hXa (by omega) hab' hq hlq
    (by simpa only [hb1] using hqb) harg
  have hl := primeCoefficient_last_cell_le hB hfb ha hab' hq
    (by simpa only [hb1] using hqb) haq
  rw [hb1] at hl
  have hinv : 1 / log (a : ℝ) ≤ 1 := (div_le_one (by linarith)).2 hla
  have hlogle : log (a : ℝ) ≤ a := by
    linarith [log_le_sub_one_of_pos (show (0 : ℝ) < a by linarith)]
  have hpay : (1 + 1 / log (a : ℝ)) * (4 * B / (a : ℝ)) ≤
      8 * B / log (a : ℝ) := by
    calc
      _ ≤ 2 * (4 * B / (a : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 8 * B / (a : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by linarith) hlogle
  rw [← primeCoefficientQuadratureError_add f q hab' (by omega : b - 1 ≤ b)]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ C * B / log (a : ℝ) + 8 * B / log (a : ℝ) := add_le_add hg (hl.trans hpay)
    _ = _ := by ring

/-- Actual all-prime sum versus the continuous integral, uniformly over
the complete bounded-monotone class. Only `b ≤ sqrt q` is required. -/
theorem primeCoefficient_global_continuous :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℕ, ∀ (f : ℝ → ℝ) (B q : ℝ),
      MonotoneOn f (Set.Icc 1 10) → 0 ≤ B →
      (∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B) →
      ∀ a b : ℕ, X0 ≤ a → 4 ≤ a → a ≤ b →
        1 ≤ log (a : ℝ) → 1 < q → 2 ≤ log q →
        (b : ℝ) ≤ q ^ (1 / 2 : ℝ) →
        log q / log (a : ℝ) - 1 ≤ 10 →
        |(∑ n ∈ (Finset.Ico a b).filter (fun n => (n + 1).Prime),
            wuPrimeCoefficientWeight f q (n + 1)) -
          ∫ x in (a : ℝ)..b, wuPrimeRealWeight f q x / log x| ≤
            C * B / log (a : ℝ) := by
  obtain ⟨C, hC, X0, hPNT⟩ := primeCoefficient_global_trueLi_quadrature_endpoint
  refine ⟨C + 12, by linarith, X0, ?_⟩
  intro f B q hf hB hfb a b hXa ha hab hla hq hlq hb haq
  have h1 := hPNT f B q hf hB hfb a b hXa ha hab hla hq hlq hb haq
  have h2 := primeCoefficient_trueLi_to_continuous hf hB hfb ha hab hq hlq hb haq
  have hsum := (abs_sub_le
    (∑ n ∈ (Finset.Ico a b).filter (fun n => (n + 1).Prime),
      wuPrimeCoefficientWeight f q (n + 1))
    (∑ n ∈ Finset.Ico a b, (logarithmicIntegral (n + 1) - logarithmicIntegral n) *
      wuPrimeCoefficientWeight f q (n + 1))
    (∫ x in (a : ℝ)..b, wuPrimeRealWeight f q x / log x)).trans (add_le_add h1 h2)
  apply hsum.trans
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hsmall : 12 * B / (a : ℝ) ≤ 12 * B :=
    div_le_self (by positivity) ha1
  have hsmall' := div_le_div_of_nonneg_right hsmall (by linarith : 0 ≤ log (a : ℝ))
  calc
    _ ≤ C * B / log (a : ℝ) + 12 * B / log (a : ℝ) := add_le_add le_rfl hsmall'
    _ = _ := by ring

end Wu2008DoubleSieve
