import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalDerivativeSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex

/-!
# Analytic continuation of the conditionally convergent derivative series

The natural partial sums converge locally uniformly on `re s > 0`.  Thus their
ordered limit is holomorphic there, and the identity theorem identifies it with
the derivative of the Dirichlet `L`-function.
-/

open Complex Finset Filter Set
open scoped Topology

namespace DirichletLConditionalDerivativeAnalyticContinuation

open DirichletLConditionalDerivativeSeries DirichletLAbelWeightVariation

variable {q : ℕ} [NeZero q]

/-- The open right half-plane. -/
def rightHalfPlane : Set ℂ := {s | 0 < s.re}

/-- Natural partial sums, regarded as entire functions. -/
noncomputable def derivativePartialSum (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, logCpowWeight s n * χ n

/-- The ordered sum as a function on all of `ℂ`; outside the right half-plane its
value is immaterial.  The dependent proof argument is eliminated by this wrapper. -/
noncomputable def orderedDerivativeFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) : ℂ :=
  if hs : 0 < s.re then orderedLogDerivativeSeries χ hχ s hs else 0

/-- The value of the dependent ordered sum does not depend on the proof of
`0 < re s`.  This explicit lemma prevents dependent proof arguments from leaking
into the function-level analytic statements. -/
lemma orderedLogDerivativeSeries_proof_irrel
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ)
    (hs ht : 0 < s.re) :
    orderedLogDerivativeSeries χ hχ s hs = orderedLogDerivativeSeries χ hχ s ht := by
  have hp : hs = ht := Subsingleton.elim _ _
  cases hp
  rfl

lemma orderedDerivativeFunction_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    orderedDerivativeFunction χ hχ s = orderedLogDerivativeSeries χ hχ s hs := by
  unfold orderedDerivativeFunction
  split
  · exact orderedLogDerivativeSeries_proof_irrel χ hχ s _ hs
  · contradiction

private lemma norm_logCpowWeight_le {δ : ℝ}
    {s : ℂ} (hre : δ ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖logCpowWeight s n‖ ≤ Real.log n / (n : ℝ) ^ δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  rw [logCpowWeight, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  simp only [neg_re]
  rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
  gcongr

private lemma logVariationBudget_le {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    {s : ℂ} (hre : δ ≤ s.re) (hnorm : ‖s‖ ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    logVariationBudget s n ≤
      (1 / δ + M / δ ^ 2) * (n : ℝ) ^ (-δ) +
        (M / δ) * (Real.log n / (n : ℝ) ^ δ) := by
  have hre0 : 0 < s.re := hδ.trans_le hre
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hre)
  have hinv : 1 / s.re ≤ 1 / δ := by
    exact one_div_le_one_div_of_le hδ hre
  have hinv2 : 1 / s.re ^ 2 ≤ 1 / δ ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hδ)
    nlinarith
  have hnormdiv : ‖s‖ / s.re ≤ M / δ := by
    exact div_le_div₀ hM hnorm hδ hre
  have hnormdiv2 : ‖s‖ / s.re ^ 2 ≤ M / δ ^ 2 := by
    apply div_le_div₀ hM hnorm (sq_pos_of_pos hδ)
    nlinarith
  rw [logVariationBudget]
  have hid : Real.log (n : ℝ) / (n : ℝ) ^ δ =
      Real.log (n : ℝ) * (n : ℝ) ^ (-δ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
  rw [hid]
  calc
    _ = (1 / s.re + ‖s‖ / s.re ^ 2) * (n : ℝ) ^ (-s.re) +
          (‖s‖ / s.re) * (Real.log n * (n : ℝ) ^ (-s.re)) := by
        field_simp [hre0.ne']
        ring
    _ ≤ (1 / δ + M / δ ^ 2) * (n : ℝ) ^ (-δ) +
          (M / δ) * (Real.log n * (n : ℝ) ^ (-δ)) := by
        gcongr
    _ = _ := by ring

/-- A compact-uniform scalar majorant for the explicit Abel tail. -/
noncomputable def compactTailMajorant (q : ℕ) (δ M : ℝ) (n : ℕ) : ℝ :=
  q * (Real.log n / (n : ℝ) ^ δ +
    (1 / δ + M / δ ^ 2) * (n : ℝ) ^ (-δ) +
    (M / δ) * (Real.log n / (n : ℝ) ^ δ))

private lemma tendsto_compactTailMajorant (q : ℕ) {δ M : ℝ} (hδ : 0 < δ) :
    Tendsto (compactTailMajorant q δ M) atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ (-δ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hδ
  have hl : Tendsto (fun x : ℝ => Real.log x / x ^ δ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hpn := hp.comp hn
  have hln := hl.comp hn
  unfold compactTailMajorant
  convert (((hln.add (hpn.const_mul (1 / δ + M / δ ^ 2))).add
    (hln.const_mul (M / δ))).const_mul (q : ℝ)) using 1 <;> simp

private lemma compact_uniform_tail
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ rightHalfPlane) :
    TendstoUniformlyOn (derivativePartialSum χ) (orderedDerivativeFunction χ hχ) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp [Metric.tendstoUniformlyOn_iff]
  obtain ⟨smin, hsmin, hmin⟩ :=
    hK.exists_isMinOn hKne continuous_re.continuousOn
  let δ : ℝ := smin.re
  have hδ : 0 < δ := hKU hsmin
  have hδK : ∀ s ∈ K, δ ≤ s.re := hmin
  obtain ⟨smax, hsmax, hmax⟩ :=
    hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let M : ℝ := ‖smax‖
  have hM : 0 ≤ M := norm_nonneg smax
  have hMK : ∀ s ∈ K, ‖s‖ ≤ M := hmax
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := (tendsto_compactTailMajorant q hδ (M := M)).eventually
    (Metric.ball_mem_nhds (x := (0 : ℝ)) hε)
  rw [eventually_atTop] at hmaj
  obtain ⟨N, hN⟩ := hmaj
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  intro s hs
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  have htail := norm_orderedLogDerivativeSeries_sub_sum_range_le χ hχ s
    (hKU hs) hn1
  rw [orderedDerivativeFunction_eq χ hχ s (hKU hs)]
  rw [dist_eq]
  change ‖orderedLogDerivativeSeries χ hχ s (hKU hs) - derivativePartialSum χ n s‖ < ε
  refine htail.trans_lt ?_
  have hweight := norm_logCpowWeight_le (hδK s hs) hn1
  have hbudget := logVariationBudget_le hδ hM (hδK s hs) (hMK s hs) hn1
  have hbound : q * (‖logCpowWeight s n‖ + logVariationBudget s n) ≤
      compactTailMajorant q δ M n := by
    unfold compactTailMajorant
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
    simpa only [add_assoc] using add_le_add hweight hbudget
  have hnon : 0 ≤ compactTailMajorant q δ M n := by
    unfold compactTailMajorant
    positivity
  exact hbound.trans_lt (by
    have := hN n hnN
    simpa [Real.dist_eq, abs_of_nonneg hnon] using this)

/-- The natural partial sums converge locally uniformly throughout `re s > 0`. -/
theorem tendstoLocallyUniformlyOn_derivativePartialSum
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    TendstoLocallyUniformlyOn (derivativePartialSum χ)
      (orderedDerivativeFunction χ hχ) atTop rightHalfPlane := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  · intro K hKU hK
    exact compact_uniform_tail χ hχ hK hKU
  · exact continuous_re.isOpen_preimage _ isOpen_Ioi

omit [NeZero q] in
private lemma differentiable_derivativePartialSum
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Differentiable ℂ (derivativePartialSum χ N) := by
  unfold derivativePartialSum
  apply Differentiable.fun_sum
  intro n hn
  apply Differentiable.mul
  · rcases n with _ | n
    · simp [logCpowWeight, cpowWeight]
    · unfold logCpowWeight cpowWeight
      apply Differentiable.const_mul
      exact Differentiable.const_cpow (by fun_prop) (Or.inl (by
        exact_mod_cast Nat.succ_ne_zero n))
  · fun_prop

/-- The ordered conditional derivative series is holomorphic on the right half-plane. -/
theorem differentiableOn_orderedDerivativeFunction
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (orderedDerivativeFunction χ hχ) rightHalfPlane := by
  exact (tendstoLocallyUniformlyOn_derivativePartialSum χ hχ).differentiableOn
    (Eventually.of_forall fun N => (differentiable_derivativePartialSum χ N).differentiableOn)
    (continuous_re.isOpen_preimage _ isOpen_Ioi)

/-- Analytic continuation identifies the ordered conditionally convergent series with
`L'` on the whole half-plane `re s > 0`. -/
theorem orderedLogDerivativeSeries_eq_deriv_LFunction_of_re_pos
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    orderedLogDerivativeSeries χ hχ s hs = deriv χ.LFunction s := by
  let U : Set ℂ := rightHalfPlane
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hF : AnalyticOnNhd ℂ (orderedDerivativeFunction χ hχ) U :=
    (differentiableOn_orderedDerivativeFunction χ hχ).analyticOnNhd hUopen
  have hL : AnalyticOnNhd ℂ (deriv χ.LFunction) U :=
    ((χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).deriv.mono
      (subset_univ U)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U, rightHalfPlane]
  have hevent : orderedDerivativeFunction χ hχ =ᶠ[𝓝 (2 : ℂ)] deriv χ.LFunction := by
    filter_upwards [eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))
      (fun z hz => hz)] with z hz
    rw [orderedDerivativeFunction_eq χ hχ z (lt_trans zero_lt_one hz)]
    exact orderedLogDerivativeSeries_eq_deriv_LFunction χ hχ z hz
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq hL hpre htwo hevent
  exact (orderedDerivativeFunction_eq χ hχ s hs).symm.trans (hall hs)

end DirichletLConditionalDerivativeAnalyticContinuation
