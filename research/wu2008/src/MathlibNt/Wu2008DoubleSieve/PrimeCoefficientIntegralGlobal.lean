import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegralVariation
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegralBounds

/-!
# A global error budget for the actual prime quadrature

Ratio-bounded blocks are split at successive doublings. Their inverse-square
logarithmic PNT errors are bounded by consecutive differences of `1 / log`.
Thus no factor depending on the number of blocks, or on the ratio of the
endpoints, survives. The quadrature still uses `a < p ≤ b` and retains the
extra `b + 1` argument required by finite summation by parts.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def primeCoefficientQuadratureError (f : ℝ → ℝ) (q : ℝ)
    (a b : ℕ) : ℝ :=
  (∑ n ∈ (Finset.Ico a b).filter (fun n => (n + 1).Prime),
    wuPrimeCoefficientWeight f q (n + 1)) -
  ∑ n ∈ Finset.Ico a b,
    (logarithmicIntegral (n + 1) - logarithmicIntegral n) *
      wuPrimeCoefficientWeight f q (n + 1)

theorem primeCoefficientQuadratureError_add (f : ℝ → ℝ) (q : ℝ)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    primeCoefficientQuadratureError f q a b +
      primeCoefficientQuadratureError f q b c =
        primeCoefficientQuadratureError f q a c := by
  unfold primeCoefficientQuadratureError
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  exact Finset.sum_Ico_consecutive _ hab hbc

private theorem doubling_block_budget {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    {a : ℕ} (ha : 3 ≤ a) :
    (C * (2 * a : ℕ) / log (2 * a : ℕ) ^ (2 : ℝ)) * (20 * B / (a + 1 : ℕ)) ≤
      (40 * B * C / log 2) * (1 / log (a : ℝ) - 1 / log (2 * a : ℕ)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hla : 0 < log (a : ℝ) := log_pos (by exact_mod_cast (show 1 < a by omega))
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hle : log (a : ℝ) ≤ log ((2 * a : ℕ) : ℝ) :=
    log_le_log ha0 (by push_cast; linarith)
  have hlt : 0 < log ((2 * a : ℕ) : ℝ) := hla.trans_le hle
  have hlog : log ((2 * a : ℕ) : ℝ) = log 2 + log (a : ℝ) := by
    push_cast
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne']
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, rpow_natCast]
  calc
    _ ≤ (C * (2 * a : ℕ) / log (2 * a : ℕ) ^ 2) * (20 * B / (a : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by positivity) ha0 (by push_cast; linarith))
      positivity
    _ = 40 * B * C / log (2 * a : ℕ) ^ 2 := by
      push_cast
      field_simp
      ring
    _ ≤ 40 * B * C / (log (a : ℝ) * log (2 * a : ℕ)) := by
      apply div_le_div_of_nonneg_left (by positivity) (mul_pos hla hlt)
      nlinarith
    _ = _ := by
      rw [hlog]
      field_simp
      ring_nf

/-- Global, arbitrary-length all-prime quadrature estimate. The constant
and threshold precede the whole bounded-monotone class and both endpoints.
There is no surviving `b/a` factor or unbudgeted number of blocks. -/
theorem primeCoefficient_global_trueLi_quadrature :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℕ, ∀ (f : ℝ → ℝ) (B q : ℝ),
      MonotoneOn f (Set.Icc 1 10) → 0 ≤ B →
      (∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B) →
      ∀ a b : ℕ, X0 ≤ a → 3 ≤ a → a ≤ b →
        1 < q → 2 ≤ log q →
        ((b + 1 : ℕ) : ℝ) ≤ q ^ (1 / 2 : ℝ) →
        log q / log (a + 1 : ℕ) - 1 ≤ 10 →
        |primeCoefficientQuadratureError f q a b| ≤ C * B / log (a : ℝ) := by
  obtain ⟨C, hC, X0, hPNT⟩ := primeCoefficient_trueLi_quadrature 2 (by norm_num)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨40 * C / log 2, by positivity, X0, ?_⟩
  intro f B q hf hB hfb a b hXa ha hab hq hlq hqb haq
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hla : 0 < log (a : ℝ) := log_pos (by exact_mod_cast (show 1 < a by omega))
  let K : ℝ := 40 * B * C / log 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have harg (c : ℕ) (hac : a ≤ c) : log q / log (c + 1 : ℕ) - 1 ≤ 10 := by
    apply le_trans _ haq
    have halog : 0 < log (a + 1 : ℕ) :=
      log_pos (by exact_mod_cast (show 1 < a + 1 by omega))
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_left (log_pos hq).le halog
    exact log_le_log (by exact_mod_cast (show 0 < a + 1 by omega))
      (by exact_mod_cast (show a + 1 ≤ c + 1 by omega))
  have hsteps : ∀ m : ℕ, ∀ z : ℕ, a ≤ z → z ≤ b → z ≤ 2 ^ m * a →
      |primeCoefficientQuadratureError f q a z| ≤
        K * (1 / log (a : ℝ) - 1 / log (2 ^ m * a : ℕ)) := by
    intro m
    induction m with
    | zero =>
      intro z haz _ hz
      simp only [pow_zero, one_mul] at hz
      have he : z = a := le_antisymm hz haz
      subst z
      simp [primeCoefficientQuadratureError]
    | succ m ih =>
      intro z haz hzb hz
      let c : ℕ := 2 ^ m * a
      have hac : a ≤ c := by
        have hp : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
        dsimp [c]
        nlinarith
      have hc3 : 3 ≤ c := ha.trans hac
      have hcx : X0 ≤ 2 * c := hXa.trans (hac.trans (by omega))
      have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
      have hlc : 0 < log (c : ℝ) := log_pos (by exact_mod_cast (show 1 < c by omega))
      have hnext : 2 ^ (m + 1) * a = 2 * c := by dsimp [c]; rw [pow_succ]; ring
      rw [hnext]
      have hlogstep : 1 / log (2 * c : ℕ) ≤ 1 / log (c : ℝ) :=
        one_div_le_one_div_of_le hlc
          (log_le_log hc0 (by push_cast; linarith))
      by_cases hzc : z ≤ c
      · have hi := ih z haz hzb hzc
        change _ ≤ K * (1 / log (a : ℝ) - 1 / log (c : ℝ)) at hi
        exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) hK)
      · have hcz : c ≤ z := (lt_of_not_ge hzc).le
        have hcb : c ≤ b := hcz.trans hzb
        have hi := ih c hac hcb le_rfl
        change _ ≤ K * (1 / log (a : ℝ) - 1 / log (c : ℝ)) at hi
        have hz2c : z ≤ 2 * c := by rwa [hnext] at hz
        have hzbR : ((z + 1 : ℕ) : ℝ) ≤ (b + 1 : ℕ) := by
          exact_mod_cast (show z + 1 ≤ b + 1 by omega)
        have hlocal := hPNT (2 * c) hcx f B q hf hB hfb c z hc3 hcz hz2c hq hlq
          (hzbR.trans hqb) (harg c hac)
        change |primeCoefficientQuadratureError f q c z| ≤ _ at hlocal
        have hbudget := doubling_block_budget hC.le hB hc3
        change _ ≤ K * (1 / log (c : ℝ) - 1 / log (2 * c : ℕ)) at hbudget
        rw [← primeCoefficientQuadratureError_add f q hac hcz]
        exact (abs_add_le _ _).trans (by linarith [hi, hlocal.trans hbudget])
  have hpow : b ≤ 2 ^ b * a := by
    have hbpow := (Nat.lt_two_pow_self (n := b)).le
    have ha1 : 1 ≤ a := by omega
    nlinarith
  have hfinal := hsteps b b hab le_rfl hpow
  have hbig0 : 0 < log ((2 ^ b * a : ℕ) : ℝ) := by
    apply log_pos
    exact_mod_cast (show 1 < 2 ^ b * a by omega)
  have hdrop : K * (1 / log (a : ℝ) - 1 / log (2 ^ b * a : ℕ)) ≤
      K / log (a : ℝ) := by
    have : 0 ≤ 1 / log ((2 ^ b * a : ℕ) : ℝ) := by positivity
    calc
      _ ≤ K * (1 / log (a : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      _ = _ := by ring
  calc
    _ ≤ K / log (a : ℝ) := hfinal.trans hdrop
    _ = _ := by dsimp [K]; ring

/-- The global logarithmic error bound for the actual effective
coefficients, with both thresholds preceding `N0` and every endpoint. -/
theorem wuEffectiveCoefficient_global_trueLi_quadrature (upper : Bool)
    (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 T : ℕ, ∀ N0 : ℕ, T ≤ N0 →
      ∀ q : ℝ, ∀ a b : ℕ, X0 ≤ a → 3 ≤ a → a ≤ b →
        1 < q → 2 ≤ log q →
        ((b + 1 : ℕ) : ℝ) ≤ q ^ (1 / 2 : ℝ) →
        log q / log (a + 1 : ℕ) - 1 ≤ 10 →
        |primeCoefficientQuadratureError (wuEffectiveCoefficient upper k δ N0) q a b| ≤
          C / log (a : ℝ) := by
  obtain ⟨C, hC, X0, hglobal⟩ := primeCoefficient_global_trueLi_quadrature
  have hevent : ∀ᶠ N0 : ℕ in atTop,
      MonotoneOn (wuEffectiveCoefficient upper k δ N0) (Set.Icc 1 10) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 10, |wuEffectiveCoefficient upper k δ N0 t| ≤ 11 := by
    filter_upwards [wu_effective_threshold_uniform_monotone upper k hk hδ hδhi,
      wuEffectiveCoefficient_uniform_abs_le_eleven upper k hk hδ hδhi] with N0 hm hb
    exact ⟨hm, hb⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨C * 11, by positivity, X0, T, ?_⟩
  intro N0 hN0 q a b hXa ha hab hq hlq hqb haq
  exact hglobal (wuEffectiveCoefficient upper k δ N0) 11 q (hT N0 hN0).1
    (by norm_num) (hT N0 hN0).2 a b hXa ha hab hq hlq hqb haq

/-- Uniform epsilon control of the global quadrature error. The lower
prime cutoff and improvement threshold are frozen before the coefficient.
This is not yet a quadrature-to-integral or prime-divisor-deletion theorem. -/
theorem wuEffectiveCoefficient_global_quadrature_error_small (upper : Bool)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T Y0 : ℕ, ∀ N0 : ℕ, T ≤ N0 →
      ∀ q : ℝ, ∀ a b : ℕ, Y0 ≤ a → a ≤ b →
        1 < q → 2 ≤ log q →
        ((b + 1 : ℕ) : ℝ) ≤ q ^ (1 / 2 : ℝ) →
        log q / log (a + 1 : ℕ) - 1 ≤ 10 →
        |primeCoefficientQuadratureError (wuEffectiveCoefficient upper k δ N0) q a b| ≤
          ε := by
  obtain ⟨C, _, X0, T, hglobal⟩ :=
    wuEffectiveCoefficient_global_trueLi_quadrature upper k hk hδ hδhi
  have hevent : ∀ᶠ a : ℕ in atTop, C / ε ≤ log (a : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  refine ⟨T, max 3 (max X0 M), ?_⟩
  intro N0 hN0 q a b ha hab hq hlq hqb haq
  have ha3 : 3 ≤ a := (le_max_left _ _).trans ha
  have hXa : X0 ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
  have hMa : M ≤ a := (le_max_right _ _).trans ((le_max_right _ _).trans ha)
  have hla : 0 < log (a : ℝ) := log_pos (by exact_mod_cast (show 1 < a by omega))
  apply (hglobal N0 hN0 q a b hXa ha3 hab hq hlq hqb haq).trans
  exact (div_le_iff₀ hla).2 (by
    have := (div_le_iff₀ hε).1 (hM a hMa)
    nlinarith)

end Wu2008DoubleSieve
