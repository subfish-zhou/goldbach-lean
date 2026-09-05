import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLAbelWeightVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Conditional convergence of the derivative Dirichlet series

This module combines the exact finite Abel identity, the modulus bound for character
prefix sums, and the total-variation estimate for the logarithmic cpow weight.
-/

open Complex Finset Filter Set
open scoped Topology

namespace DirichletLConditionalDerivativeSeries

open DirichletLWeakStripDerivative DirichletLAbelWeightVariation

variable {q : ℕ} [NeZero q]

/-- On positive natural numbers, the real-logarithm definition of `logCpowWeight`
is exactly the complex-logarithm weight occurring in finite Abel summation. -/
lemma logCpowWeight_nat_eq (s : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    logCpowWeight s k = -(Complex.log (k : ℂ)) * (k : ℂ) ^ (-s) := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by norm_num
  rw [logCpowWeight, cpowWeight, Complex.ofReal_log hk0, hcast]

/-- Exact finite Abel identity, stated with `logCpowWeight`. -/
lemma logCpowWeight_abel_Ico (χ : DirichletCharacter ℂ q) (s : ℂ)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    ∑ k ∈ Ico m n, logCpowWeight s k * χ k =
      logCpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k) -
        logCpowWeight s m * (∑ k ∈ range m, χ k) -
        ∑ k ∈ Ico m (n - 1),
          (logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k) *
            (∑ j ∈ range (k + 1), χ j) := by
  exact abel_Ico χ (fun k : ℕ => logCpowWeight s k) hmn

/-- Uniform finite-tail estimate for the logarithmic derivative weight. -/
lemma norm_sum_Ico_logCpowWeight_character_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    ‖∑ k ∈ Ico m n, logCpowWeight s k * χ k‖ ≤
      q * (‖logCpowWeight s (n - 1 : ℕ)‖ + ‖logCpowWeight s m‖ +
        logVariationBudget s m) := by
  rw [logCpowWeight_abel_Ico χ s hm hmn]
  calc
    _ ≤ ‖logCpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k)‖ +
          ‖logCpowWeight s m * (∑ k ∈ range m, χ k)‖ +
          ‖∑ k ∈ Ico m (n - 1),
            (logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k) *
              (∑ j ∈ range (k + 1), χ j)‖ := by
        calc
          _ ≤ ‖logCpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k) -
              logCpowWeight s m * (∑ k ∈ range m, χ k)‖ +
              ‖∑ k ∈ Ico m (n - 1),
                (logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k) *
                  (∑ j ∈ range (k + 1), χ j)‖ := norm_sub_le _ _
          _ ≤ _ := by
            have h := norm_sub_le
              (logCpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k))
              (logCpowWeight s m * (∑ k ∈ range m, χ k))
            linarith
    _ ≤ ‖logCpowWeight s (n - 1 : ℕ)‖ * q +
          ‖logCpowWeight s m‖ * q +
          ∑ k ∈ Ico m (n - 1),
            (‖logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k‖ * q) := by
      gcongr
      · rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ n
      · rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ m
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        gcongr
        exact norm_sum_range_character_le_modulus χ hχ (k + 1)
    _ = q * (‖logCpowWeight s (n - 1 : ℕ)‖ + ‖logCpowWeight s m‖ +
          ∑ k ∈ Ico m (n - 1),
            ‖logCpowWeight s (k + 1 : ℕ) - logCpowWeight s k‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ q * (‖logCpowWeight s (n - 1 : ℕ)‖ + ‖logCpowWeight s m‖ +
          logVariationBudget s m) := by
      gcongr
      simpa only [Nat.pred_eq_sub_one, Nat.cast_add, Nat.cast_one] using
        sum_norm_logCpowWeight_sub_le s hs hm (Nat.le_pred_of_lt hmn)

/-- The endpoint logarithmic cpow weight tends to zero throughout `re s > 0`. -/
lemma tendsto_norm_logCpowWeight_nat_atTop (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ‖logCpowWeight s n‖) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x / x ^ s.re) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun n : ℕ => ‖logCpowWeight s n‖) =ᶠ[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ s.re) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    rw [logCpowWeight, norm_mul, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog, cpowWeight,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    simp only [neg_re]
    rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
  exact (tendsto_congr' heq).2 hnat

/-- The explicit variation budget also vanishes at infinity. -/
lemma tendsto_logVariationBudget_nat_atTop (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => logVariationBudget s n) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hs
  have hl : Tendsto (fun x : ℝ => Real.log x / x ^ s.re) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
  have hcomb : Tendsto
      (fun x : ℝ => (1 / s.re + ‖s‖ / s.re ^ 2) * x ^ (-s.re) +
        (‖s‖ / s.re) * (Real.log x / x ^ s.re)) atTop (𝓝 0) := by
    simpa using
      ((hp.const_mul (1 / s.re + ‖s‖ / s.re ^ 2)).add
        (hl.const_mul (‖s‖ / s.re)))
  have hnat := hcomb.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun n : ℕ => logVariationBudget s n) =ᶠ[atTop]
      (fun n : ℕ => (1 / s.re + ‖s‖ / s.re ^ 2) * (n : ℝ) ^ (-s.re) +
        (‖s‖ / s.re) * (Real.log n / (n : ℝ) ^ s.re)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hdiv : Real.log (n : ℝ) / (n : ℝ) ^ s.re =
        Real.log (n : ℝ) * (n : ℝ) ^ (-s.re) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
    rw [logVariationBudget, hdiv]
    field_simp [hs.ne']
    ring
  exact (tendsto_congr' heq).2 hnat

/-- The ordinary ordered partial sums form a Cauchy sequence.  This is the correct
notion of conditional convergence for a series indexed in its natural order. -/
lemma cauchySeq_sum_range_logCpowWeight_character
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    CauchySeq (fun n : ℕ => ∑ k ∈ range n, logCpowWeight s k * χ k) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  let δ : ℝ := ε / (3 * q)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hq)
  have he := (tendsto_norm_logCpowWeight_nat_atTop s hs).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hδ)
  have hb := (tendsto_logVariationBudget_nat_atTop s hs).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hδ)
  rw [eventually_atTop] at he hb
  rcases he with ⟨Ne, hNe⟩
  rcases hb with ⟨Nb, hNb⟩
  refine ⟨max 1 (max Ne Nb), ?_⟩
  intro m hm n hn
  have hm1 : 1 ≤ m := (le_max_left 1 (max Ne Nb)).trans hm
  have hn1 : 1 ≤ n := (le_max_left 1 (max Ne Nb)).trans hn
  have hmE : Ne ≤ m := (le_max_of_le_right (le_max_left Ne Nb)).trans hm
  have hnE : Ne ≤ n := (le_max_of_le_right (le_max_left Ne Nb)).trans hn
  have hmB : Nb ≤ m := (le_max_of_le_right (le_max_right Ne Nb)).trans hm
  have hgm : ‖logCpowWeight s m‖ < δ := by
    simpa [Real.dist_eq] using hNe m hmE
  have hgn : ‖logCpowWeight s n‖ < δ := by
    simpa [Real.dist_eq] using hNe n hnE
  have hbm : logVariationBudget s m < δ := by
    have := hNb m hmB
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold logVariationBudget; positivity)] at this
    exact this
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · have htail := norm_sum_Ico_logCpowWeight_character_le χ hχ s hs hm1 hmn
    have hpredE : Ne ≤ n - 1 := hmE.trans (Nat.le_pred_of_lt hmn)
    have hgpred : ‖logCpowWeight s (n - 1 : ℕ)‖ < δ := by
      simpa [Real.dist_eq] using hNe (n - 1) hpredE
    rw [dist_eq, ← norm_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn.le]
    calc
      _ ≤ q * (‖logCpowWeight s (n - 1 : ℕ)‖ + ‖logCpowWeight s m‖ +
          logVariationBudget s m) := htail
      _ < ε := by
        calc
          _ < q * (δ + δ + δ) :=
            mul_lt_mul_of_pos_left (by linarith) hq
          _ = ε := by dsimp [δ]; field_simp; ring
  · simp [hε]
  · have htail := norm_sum_Ico_logCpowWeight_character_le χ hχ s hs hn1 hnm
    have hnB : Nb ≤ n := (le_max_of_le_right (le_max_right Ne Nb)).trans hn
    have hbn : logVariationBudget s n < δ := by
      have := hNb n hnB
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold logVariationBudget; positivity)] at this
      exact this
    have hpredE : Ne ≤ m - 1 := hnE.trans (Nat.le_pred_of_lt hnm)
    have hgpred : ‖logCpowWeight s (m - 1 : ℕ)‖ < δ := by
      simpa [Real.dist_eq] using hNe (m - 1) hpredE
    rw [dist_eq, ← Finset.sum_Ico_eq_sub _ hnm.le]
    calc
      _ ≤ q * (‖logCpowWeight s (m - 1 : ℕ)‖ + ‖logCpowWeight s n‖ +
          logVariationBudget s n) := htail
      _ < ε := by
        calc
          _ < q * (δ + δ + δ) :=
            mul_lt_mul_of_pos_left (by linarith) hq
          _ = ε := by dsimp [δ]; field_simp; ring

/-- Existence of the naturally ordered conditional sum. -/
lemma exists_tendsto_sum_range_logCpowWeight_character
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ range n, logCpowWeight s k * χ k)
      atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_sum_range_logCpowWeight_character χ hχ s hs)

/-- The canonical value of the conditionally convergent logarithmic derivative series,
defined by taking its partial sums in the natural order.  The convergence hypotheses are
arguments of the definition so that no unordered `tsum` is used in the conditional range. -/
noncomputable def orderedLogDerivativeSeries
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) : ℂ :=
  Classical.choose (exists_tendsto_sum_range_logCpowWeight_character χ hχ s hs)

/-- The naturally ordered partial sums converge to `orderedLogDerivativeSeries`. -/
lemma tendsto_sum_range_orderedLogDerivativeSeries
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ range n, logCpowWeight s k * χ k) atTop
      (𝓝 (orderedLogDerivativeSeries χ hχ s hs)) :=
  Classical.choose_spec (exists_tendsto_sum_range_logCpowWeight_character χ hχ s hs)

/-- Explicit tail bound for the canonical naturally ordered sum. -/
lemma norm_orderedLogDerivativeSeries_sub_sum_range_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖orderedLogDerivativeSeries χ hχ s hs -
        ∑ k ∈ range m, logCpowWeight s k * χ k‖ ≤
      q * (‖logCpowWeight s m‖ + logVariationBudget s m) := by
  let P : ℕ → ℂ := fun n => ∑ k ∈ range n, logCpowWeight s k * χ k
  have hP : Tendsto P atTop (𝓝 (orderedLogDerivativeSeries χ hχ s hs)) := by
    simpa only [P] using tendsto_sum_range_orderedLogDerivativeSeries χ hχ s hs
  have hleft : Tendsto (fun n => ‖P (n + 1) - P m‖) atTop
      (𝓝 ‖orderedLogDerivativeSeries χ hχ s hs - P m‖) :=
    ((hP.comp (tendsto_add_atTop_nat 1)).sub_const (P m)).norm
  have hright : Tendsto
      (fun n : ℕ => q * (‖logCpowWeight s n‖ + ‖logCpowWeight s m‖ +
        logVariationBudget s m)) atTop
      (𝓝 (q * (‖logCpowWeight s m‖ + logVariationBudget s m))) := by
    simpa only [zero_add, add_assoc] using
      ((tendsto_norm_logCpowWeight_nat_atTop s hs).add_const
        (‖logCpowWeight s m‖ + logVariationBudget s m)).const_mul (q : ℝ)
  refine le_of_tendsto_of_tendsto hleft hright ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hmn : m < n + 1 := Nat.lt_succ_of_le hn
  have htail := norm_sum_Ico_logCpowWeight_character_le χ hχ s hs hm hmn
  rw [Finset.sum_Ico_eq_sub _ hmn.le] at htail
  simpa only [P, Nat.add_sub_cancel] using htail

/-- In the half-plane of absolute convergence, the canonical naturally ordered sum
is the derivative of the analytically continued Dirichlet `L`-function. -/
lemma orderedLogDerivativeSeries_eq_deriv_LFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    orderedLogDerivativeSeries χ hχ s (by linarith) = deriv χ.LFunction s := by
  have habs : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < s.re := by
    refine (LSeries.abscissaOfAbsConv_le_of_le_const ?_).trans_lt ?_
    · exact ⟨1, fun n _ => χ.norm_le_one n⟩
    · exact_mod_cast hs
  have hsum := (LSeriesSummable_logMul_of_lt_re habs).LSeriesHasSum
  have hterm (n : ℕ) :
      -(LSeries.term (LSeries.logMul (fun k : ℕ => χ k)) s n) =
        logCpowWeight s n * χ n := by
    rcases n with _ | n
    · simp [logCpowWeight, cpowWeight]
    · rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),
        logCpowWeight_nat_eq s (Nat.succ_pos n), cpow_neg]
      dsimp only [LSeries.logMul]
      ring
  have hordered := tendsto_sum_range_orderedLogDerivativeSeries χ hχ s (by linarith)
  have hseries : Tendsto
      (fun n : ℕ => ∑ k ∈ range n, logCpowWeight s k * χ k) atTop
      (𝓝 (deriv χ.LFunction s)) := by
    have hderiv : deriv χ.LFunction s =
        -LSeries (LSeries.logMul (fun n : ℕ => χ n)) s :=
      (DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs).trans
        (LSeries_deriv habs)
    have hsum' : HasSum (fun n : ℕ => logCpowWeight s n * χ n)
        (deriv χ.LFunction s) := by
      rw [hderiv]
      exact hsum.neg.congr_fun fun n => (hterm n).symm
    exact hsum'.tendsto_sum_nat
  exact tendsto_nhds_unique hordered hseries

end DirichletLConditionalDerivativeSeries
