import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLAbelWeightVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex

/-!
# Naturally ordered conditional Dirichlet L-series

For a nonprincipal Dirichlet character, the ordinary partial sums of `χ(n)n⁻ˢ`
converge when `re s > 0`.  We retain the natural order (rather than using an
unordered `tsum`), prove an explicit Abel tail, establish compact-local uniform
convergence, and identify the resulting holomorphic function with `χ.LFunction`.
-/

open Complex Finset Filter Set
open scoped Topology

namespace DirichletLConditionalValueSeries

open DirichletLWeakStripDerivative DirichletLAbelWeightVariation

variable {q : ℕ} [NeZero q]

private lemma character_nat_zero_of_ne_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : χ (0 : ℕ) = 0 := by
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact hχ (Subsingleton.elim _ _)
  have hq0 : q ≠ 0 := NeZero.ne q
  letI : Fact (1 < q) :=
    ⟨Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hq0, hq1⟩⟩
  simpa only [Nat.cast_zero] using
    (MulChar.map_nonunit χ (a := (0 : ZMod q)) not_isUnit_zero)

/-- On natural arguments, `cpowWeight` is the usual complex Dirichlet weight. -/
lemma cpowWeight_nat_eq (s : ℂ) (k : ℕ) :
    cpowWeight s k = (k : ℂ) ^ (-s) := by
  unfold cpowWeight
  norm_num

/-- Explicit finite Abel tail for the value series. -/
lemma norm_sum_Ico_cpowWeight_character_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    ‖∑ k ∈ Ico m n, cpowWeight s k * χ k‖ ≤
      q * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
  have hab := dirichlet_cpow_abel_Ico χ s hmn
  simp_rw [← cpowWeight_nat_eq] at hab
  rw [hab]
  calc
    _ ≤ ‖cpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k)‖ +
          ‖cpowWeight s m * (∑ k ∈ range m, χ k)‖ +
          ‖∑ k ∈ Ico m (n - 1),
            (cpowWeight s (k + 1 : ℕ) - cpowWeight s k) *
              (∑ j ∈ range (k + 1), χ j)‖ := by
      calc
        _ ≤ ‖cpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k) -
              cpowWeight s m * (∑ k ∈ range m, χ k)‖ +
              ‖∑ k ∈ Ico m (n - 1),
                (cpowWeight s (k + 1 : ℕ) - cpowWeight s k) *
                  (∑ j ∈ range (k + 1), χ j)‖ := norm_sub_le _ _
        _ ≤ _ := by
          have h := norm_sub_le
            (cpowWeight s (n - 1 : ℕ) * (∑ k ∈ range n, χ k))
            (cpowWeight s m * (∑ k ∈ range m, χ k))
          linarith
    _ ≤ ‖cpowWeight s (n - 1 : ℕ)‖ * q + ‖cpowWeight s m‖ * q +
          ∑ k ∈ Ico m (n - 1),
            (‖cpowWeight s (k + 1 : ℕ) - cpowWeight s k‖ * q) := by
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
    _ = q * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
          ∑ k ∈ Ico m (n - 1),
            ‖cpowWeight s (k + 1 : ℕ) - cpowWeight s k‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ q * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
          (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
      gcongr
      simpa only [Nat.pred_eq_sub_one, Nat.cast_add, Nat.cast_one] using
        sum_norm_cpowWeight_sub_le s hs hm (Nat.le_pred_of_lt hmn)

/-- The endpoint value weight tends to zero in `re s > 0`. -/
lemma tendsto_norm_cpowWeight_nat_atTop (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ‖cpowWeight s n‖) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hs
  have hn := hp.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun n : ℕ => ‖cpowWeight s n‖) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    rw [cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    simp
  exact (tendsto_congr' heq).2 hn

/-- The explicit variation part of the tail tends to zero. -/
lemma tendsto_cpowVariationBudget_nat_atTop (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => (‖s‖ / s.re) * (n : ℝ) ^ (-s.re)) atTop (𝓝 0) := by
  simpa using (((tendsto_rpow_neg_atTop hs).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (‖s‖ / s.re))

/-- Natural-order partial sums form a Cauchy sequence throughout `re s > 0`. -/
lemma cauchySeq_sum_range_cpowWeight_character
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    CauchySeq (fun n : ℕ => ∑ k ∈ range n, cpowWeight s k * χ k) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  let δ : ℝ := ε / (3 * q)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hq)
  have he := (tendsto_norm_cpowWeight_nat_atTop s hs).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hδ)
  have hb := (tendsto_cpowVariationBudget_nat_atTop s hs).eventually
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
  have hgm : ‖cpowWeight s m‖ < δ := by
    simpa [Real.dist_eq] using hNe m hmE
  have hgn : ‖cpowWeight s n‖ < δ := by
    simpa [Real.dist_eq] using hNe n hnE
  have hbm : (‖s‖ / s.re) * (m : ℝ) ^ (-s.re) < δ := by
    have := hNb m hmB
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · have htail := norm_sum_Ico_cpowWeight_character_le χ hχ s hs hm1 hmn
    have hpredE : Ne ≤ n - 1 := hmE.trans (Nat.le_pred_of_lt hmn)
    have hgpred : ‖cpowWeight s (n - 1 : ℕ)‖ < δ := by
      simpa [Real.dist_eq] using hNe (n - 1) hpredE
    rw [dist_eq, ← norm_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn.le]
    calc
      _ ≤ q * (‖cpowWeight s (n - 1 : ℕ)‖ + ‖cpowWeight s m‖ +
          (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := htail
      _ < ε := by
        calc
          _ < q * (δ + δ + δ) := mul_lt_mul_of_pos_left (by linarith) hq
          _ = ε := by dsimp [δ]; field_simp; ring
  · simp [hε]
  · have htail := norm_sum_Ico_cpowWeight_character_le χ hχ s hs hn1 hnm
    have hnB : Nb ≤ n := (le_max_of_le_right (le_max_right Ne Nb)).trans hn
    have hbn : (‖s‖ / s.re) * (n : ℝ) ^ (-s.re) < δ := by
      have := hNb n hnB
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
      exact this
    have hpredE : Ne ≤ m - 1 := hnE.trans (Nat.le_pred_of_lt hnm)
    have hgpred : ‖cpowWeight s (m - 1 : ℕ)‖ < δ := by
      simpa [Real.dist_eq] using hNe (m - 1) hpredE
    rw [dist_eq, ← Finset.sum_Ico_eq_sub _ hnm.le]
    calc
      _ ≤ q * (‖cpowWeight s (m - 1 : ℕ)‖ + ‖cpowWeight s n‖ +
          (‖s‖ / s.re) * (n : ℝ) ^ (-s.re)) := htail
      _ < ε := by
        calc
          _ < q * (δ + δ + δ) := mul_lt_mul_of_pos_left (by linarith) hq
          _ = ε := by dsimp [δ]; field_simp; ring

lemma exists_tendsto_sum_range_cpowWeight_character
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ range n, cpowWeight s k * χ k)
      atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (cauchySeq_sum_range_cpowWeight_character χ hχ s hs)

/-- Canonical value of the conditional series, defined by its natural partial sums. -/
noncomputable def orderedValueSeries
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) : ℂ :=
  Classical.choose (exists_tendsto_sum_range_cpowWeight_character χ hχ s hs)

lemma tendsto_sum_range_orderedValueSeries
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ range n, cpowWeight s k * χ k) atTop
      (𝓝 (orderedValueSeries χ hχ s hs)) :=
  Classical.choose_spec (exists_tendsto_sum_range_cpowWeight_character χ hχ s hs)

/-- Explicit tail for the canonical natural-order value. -/
lemma norm_orderedValueSeries_sub_sum_range_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖orderedValueSeries χ hχ s hs - ∑ k ∈ range m, cpowWeight s k * χ k‖ ≤
      q * ((m : ℝ) ^ (-s.re) + (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)) := by
  let P : ℕ → ℂ := fun n => ∑ k ∈ range n, cpowWeight s k * χ k
  have hP : Tendsto P atTop (𝓝 (orderedValueSeries χ hχ s hs)) := by
    simpa only [P] using tendsto_sum_range_orderedValueSeries χ hχ s hs
  have hleft : Tendsto (fun n => ‖P (n + 1) - P m‖) atTop
      (𝓝 ‖orderedValueSeries χ hχ s hs - P m‖) :=
    ((hP.comp (tendsto_add_atTop_nat 1)).sub_const (P m)).norm
  have hright : Tendsto
      (fun n : ℕ => q * (‖cpowWeight s n‖ + ‖cpowWeight s m‖ +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re))) atTop
      (𝓝 (q * ((m : ℝ) ^ (-s.re) +
        (‖s‖ / s.re) * (m : ℝ) ^ (-s.re)))) := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hwm : ‖cpowWeight s m‖ = (m : ℝ) ^ (-s.re) := by
      rw [cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hm0]
      simp
    simpa only [zero_add, hwm, add_assoc] using
      ((tendsto_norm_cpowWeight_nat_atTop s hs).add_const
        (‖cpowWeight s m‖ + (‖s‖ / s.re) * (m : ℝ) ^ (-s.re))).const_mul (q : ℝ)
  refine le_of_tendsto_of_tendsto hleft hright ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hmn : m < n + 1 := Nat.lt_succ_of_le hn
  have htail := norm_sum_Ico_cpowWeight_character_le χ hχ s hs hm hmn
  rw [Finset.sum_Ico_eq_sub _ hmn.le] at htail
  simpa only [P, Nat.add_sub_cancel] using htail

/-- The open half-plane on which the natural-order value series converges. -/
def rightHalfPlane : Set ℂ := {s | 0 < s.re}

noncomputable def valuePartialSum (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, cpowWeight s n * χ n

noncomputable def orderedValueFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) : ℂ :=
  if hs : 0 < s.re then orderedValueSeries χ hχ s hs else 0

lemma orderedValueSeries_proof_irrel
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs ht : 0 < s.re) :
    orderedValueSeries χ hχ s hs = orderedValueSeries χ hχ s ht := by
  cases Subsingleton.elim hs ht
  rfl

lemma orderedValueFunction_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    orderedValueFunction χ hχ s = orderedValueSeries χ hχ s hs := by
  unfold orderedValueFunction
  split
  · exact orderedValueSeries_proof_irrel χ hχ s _ hs
  · contradiction

/-- Compact-window majorant requested by the Abel estimate. -/
noncomputable def compactValueTailMajorant (q : ℕ) (δ M : ℝ) (m : ℕ) : ℝ :=
  q * (m : ℝ) ^ (-δ) * (1 + M / δ)

private lemma tendsto_compactValueTailMajorant (q : ℕ) {δ M : ℝ} (hδ : 0 < δ) :
    Tendsto (compactValueTailMajorant q δ M) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop hδ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  unfold compactValueTailMajorant
  simpa [mul_assoc] using (hp.const_mul (q : ℝ)).mul_const (1 + M / δ)

private lemma compact_uniform_value_tail
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ rightHalfPlane) :
    TendstoUniformlyOn (valuePartialSum χ) (orderedValueFunction χ hχ) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp [Metric.tendstoUniformlyOn_iff]
  obtain ⟨smin, hsmin, hmin⟩ := hK.exists_isMinOn hKne continuous_re.continuousOn
  let δ : ℝ := smin.re
  have hδ : 0 < δ := hKU hsmin
  have hδK : ∀ s ∈ K, δ ≤ s.re := hmin
  obtain ⟨smax, hsmax, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let M : ℝ := ‖smax‖
  have hM : 0 ≤ M := norm_nonneg smax
  have hMK : ∀ s ∈ K, ‖s‖ ≤ M := hmax
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := (tendsto_compactValueTailMajorant q hδ (M := M)).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hε)
  rw [eventually_atTop] at hmaj
  obtain ⟨N, hN⟩ := hmaj
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  intro s hsK
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  have htail := norm_orderedValueSeries_sub_sum_range_le χ hχ s (hKU hsK) hn1
  rw [orderedValueFunction_eq χ hχ s (hKU hsK), dist_eq]
  change ‖orderedValueSeries χ hχ s (hKU hsK) - valuePartialSum χ n s‖ < ε
  refine htail.trans_lt ?_
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg (hδK s hsK))
  have hdiv : ‖s‖ / s.re ≤ M / δ :=
    div_le_div₀ hM (hMK s hsK) hδ (hδK s hsK)
  have hbound : q * ((n : ℝ) ^ (-s.re) +
      (‖s‖ / s.re) * (n : ℝ) ^ (-s.re)) ≤ compactValueTailMajorant q δ M n := by
    unfold compactValueTailMajorant
    have hp0 : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
    have hpδ0 : 0 ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg (by positivity) _
    have hd0 : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) (hKU hsK).le
    calc
      _ ≤ q * ((n : ℝ) ^ (-δ) + (M / δ) * (n : ℝ) ^ (-δ)) := by gcongr
      _ = _ := by ring
  have hnon : 0 ≤ compactValueTailMajorant q δ M n := by
    unfold compactValueTailMajorant
    positivity
  exact hbound.trans_lt (by
    have := hN n hnN
    simpa [Real.dist_eq, abs_of_nonneg hnon] using this)

/-- Natural partial sums converge locally uniformly on `re s > 0`. -/
theorem tendstoLocallyUniformlyOn_valuePartialSum
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    TendstoLocallyUniformlyOn (valuePartialSum χ) (orderedValueFunction χ hχ)
      atTop rightHalfPlane := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  · intro K hKU hK
    exact compact_uniform_value_tail χ hχ hK hKU
  · exact continuous_re.isOpen_preimage _ isOpen_Ioi

private lemma differentiable_valuePartialSum
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    Differentiable ℂ (valuePartialSum χ N) := by
  unfold valuePartialSum
  apply Differentiable.fun_sum
  intro n hn
  rcases n with _ | n
  · rw [character_nat_zero_of_ne_one χ hχ]
    simp
  · apply Differentiable.mul
    · unfold cpowWeight
      exact Differentiable.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast Nat.succ_ne_zero n))
    · fun_prop

/-- The canonical natural-order value is holomorphic on the right half-plane. -/
theorem differentiableOn_orderedValueFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (orderedValueFunction χ hχ) rightHalfPlane := by
  exact (tendstoLocallyUniformlyOn_valuePartialSum χ hχ).differentiableOn
    (Eventually.of_forall fun N =>
      (differentiable_valuePartialSum χ hχ N).differentiableOn)
    (continuous_re.isOpen_preimage _ isOpen_Ioi)

/-- In `re s > 1`, the ordered value is the ordinary L-series value. -/
lemma orderedValueSeries_eq_LFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    orderedValueSeries χ hχ s (by linarith) = χ.LFunction s := by
  have habs : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < s.re := by
    refine (LSeries.abscissaOfAbsConv_le_of_le_const ?_).trans_lt ?_
    · exact ⟨1, fun n _ => χ.norm_le_one n⟩
    · exact_mod_cast hs
  have hsum := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  have hterm (n : ℕ) : LSeries.term (fun k : ℕ => χ k) s n = cpowWeight s n * χ n := by
    rcases n with _ | n
    · rw [LSeries.term_zero, character_nat_zero_of_ne_one χ hχ]
      simp
    · rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), cpowWeight_nat_eq, cpow_neg]
      ring
  have hseries : Tendsto (fun n : ℕ => ∑ k ∈ range n, cpowWeight s k * χ k) atTop
      (𝓝 (χ.LFunction s)) := by
    rw [χ.LFunction_eq_LSeries hs]
    exact (hsum.congr_fun fun n => (hterm n).symm).tendsto_sum_nat
  exact tendsto_nhds_unique
    (tendsto_sum_range_orderedValueSeries χ hχ s (by linarith)) hseries

/-- Identity-theorem continuation: the ordered conditional value is `χ.LFunction`
throughout the full half-plane `re s > 0`. -/
theorem orderedValueSeries_eq_LFunction_of_re_pos
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    orderedValueSeries χ hχ s hs = χ.LFunction s := by
  let U : Set ℂ := rightHalfPlane
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hF : AnalyticOnNhd ℂ (orderedValueFunction χ hχ) U :=
    (differentiableOn_orderedValueFunction χ hχ).analyticOnNhd hUopen
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ |>.mono
      (subset_univ U)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U, rightHalfPlane]
  have hevent : orderedValueFunction χ hχ =ᶠ[𝓝 (2 : ℂ)] χ.LFunction := by
    filter_upwards [eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re)) (fun z hz => hz)] with z hz
    rw [orderedValueFunction_eq χ hχ z (lt_trans zero_lt_one hz)]
    exact orderedValueSeries_eq_LFunction χ hχ z hz
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq hL hpre htwo hevent
  exact (orderedValueFunction_eq χ hχ s hs).symm.trans (hall hs)

end DirichletLConditionalValueSeries
