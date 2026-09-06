import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21VerticalEstimate
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21SourceWidth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Complex Real Filter
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Source-region geometry, extracted without changing the analytic-payments module. -/
theorem chen1973Lemma6_eq21_primeRegion_log_y
    {x : ℕ} (hx : 3 ≤ x) {pp : ℕ × ℕ}
    (hpp : pp ∈ chen1973Lemma6Eq21PrimeRegion x) :
    1 < (x : ℝ) / ((pp.1 : ℝ) * pp.2) ∧
    Real.log (x : ℝ) / 3 ≤ Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) := by
  simp only [chen1973Lemma6Eq21PrimeRegion, Finset.mem_filter] at hpp
  rcases hpp with ⟨hpair, hp₁lower, hp₁upper, hp₂lower, hp₂root⟩
  rw [chen1973Lemma5PrimePairs, Finset.mem_filter] at hpair
  rcases hpair with ⟨_, hp₁prime, hp₂prime, _⟩
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hp₁0 : (0 : ℝ) < pp.1 := by exact_mod_cast hp₁prime.pos
  have hp₂0 : (0 : ℝ) < pp.2 := by exact_mod_cast hp₂prime.pos
  let A : ℝ := (x : ℝ) ^ ((1 : ℝ) / 3)
  let y : ℝ := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hden0 : 0 < (pp.1 : ℝ) * pp.2 := mul_pos hp₁0 hp₂0
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hA3 : A ^ 3 = (x : ℝ) := by
    dsimp [A]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  have hp₂sq : (pp.2 : ℝ) ^ 2 ≤ (x : ℝ) / pp.1 := by
    exact (Real.le_sqrt (by positivity) (by positivity)).mp hp₂root
  have hp₁p₂sq : (pp.1 : ℝ) * (pp.2 : ℝ) ^ 2 ≤ (x : ℝ) := by
    simpa only [mul_comm] using (le_div_iff₀ hp₁0).mp hp₂sq
  have hp₁leA : (pp.1 : ℝ) ≤ A := by exact hp₁upper
  have hp₁p₂leA2 : (pp.1 : ℝ) * pp.2 ≤ A ^ 2 := by
    by_contra hnot
    have hlt : A ^ 2 < (pp.1 : ℝ) * pp.2 := lt_of_not_ge hnot
    have hsq := mul_self_lt_mul_self (sq_nonneg A) hlt
    have hupper : ((pp.1 : ℝ) * pp.2) * ((pp.1 : ℝ) * pp.2) ≤
        (A ^ 2) * (A ^ 2) := by
      calc
        ((pp.1 : ℝ) * pp.2) * ((pp.1 : ℝ) * pp.2) =
            (pp.1 : ℝ) * ((pp.1 : ℝ) * (pp.2 : ℝ) ^ 2) := by ring
        _ ≤ A * (x : ℝ) :=
          mul_le_mul hp₁leA hp₁p₂sq (by positivity) (le_of_lt hA0)
        _ = (A ^ 2) * (A ^ 2) := by rw [← hA3]; ring
    exact (not_lt_of_ge hupper) hsq
  have hAy : A ≤ y := by
    rw [show y = (x : ℝ) / ((pp.1 : ℝ) * pp.2) by rfl]
    apply (le_div_iff₀ hden0).2
    calc
      A * ((pp.1 : ℝ) * pp.2) ≤ A * A ^ 2 :=
        mul_le_mul_of_nonneg_left hp₁p₂leA2 (le_of_lt hA0)
      _ = (x : ℝ) := by rw [← hA3]; ring
  have hlogy : Real.log (x : ℝ) / 3 ≤ Real.log y := by
    calc
      Real.log (x : ℝ) / 3 = Real.log A := by
        dsimp [A]
        rw [Real.log_rpow hx0]
        ring
      _ ≤ Real.log y := Real.log_le_log hA0 hAy

  exact ⟨(Real.log_pos_iff hy0.le).mp (by linarith), hlogy⟩

/-- A fixed, explicit finite coefficient; no cell parameter occurs here. -/
def chen1973Lemma6Eq21UniformBudgetConstant (r : ℕ) : ℝ :=
  (2 + ∑ j ∈ Finset.range (r + 1),
    (Nat.choose r j : ℝ) * (Nat.factorial j : ℝ)) * 104 ^ (r + 1)

/-- Uniform arithmetic bound for the already-integrated kernel budget.
We deliberately discard the helpful order denominators and use a loose fixed
coefficient, rather than impose an integral-shaped premise. -/
theorem chen1973Lemma6_eq21_budget_uniform
    {x d : ℕ} (hu : 4 ≤ Real.log (x : ℝ))
    (hd : (1 : ℝ) ≤ d) (hdu : (d : ℝ) ≤ Real.log x ^ (100 : ℕ))
    (r : ℕ) :
    let a := chen1973PerronScale (x : ℝ)
    let N := chen1973PerronOrder (x : ℝ) + 1
    let D := 1 + Real.log ((d : ℝ) * (1 + a))
    let σ := chen1973Lemma6Eq21Sigma x
    (σ⁻¹ + Real.log a) * D ^ r +
      ∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * D ^ (r - j) *
        ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1)) ≤
    chen1973Lemma6Eq21UniformBudgetConstant r *
      (1 + Real.log (Real.log (x : ℝ))) ^ (r + 1) := by
  let u := Real.log (x : ℝ)
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  let D := 1 + Real.log ((d : ℝ) * (1 + a))
  let σ := chen1973Lemma6Eq21Sigma x
  let v := 1 + Real.log u
  let W := 104 * v
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by dsimp [u]; linarith)
  have hv : 1 ≤ v := by dsimp [v]; linarith
  have hW : 1 ≤ W := by dsimp [W]; linarith
  have ha : 1 ≤ a := by
    dsimp [a, chen1973PerronScale]
    exact Real.one_le_rpow (by linarith) (by positivity)
  have ha0 : 0 < a := by linarith
  have hloga : Real.log a = (11 / 10 : ℝ) * Real.log u := by
    dsimp [a, chen1973PerronScale, u]
    exact Real.log_rpow hu0 _
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogd : Real.log (d : ℝ) ≤ 100 * Real.log u := by
    calc
      _ ≤ Real.log (u ^ (100 : ℕ)) := Real.log_le_log hd0 hdu
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog1a : Real.log (1 + a) ≤ 1 + (11 / 10 : ℝ) * Real.log u := by
    calc
      _ ≤ Real.log (2 * a) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log a := Real.log_mul (by norm_num) ha0.ne'
      _ ≤ _ := by rw [hloga]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hD0 : 0 ≤ D := by
    have hprod : 1 ≤ (d : ℝ) * (1 + a) := by nlinarith
    have := Real.log_nonneg hprod
    dsimp [D]; linarith
  have hD : D ≤ W := by
    dsimp [D, W, v]
    rw [Real.log_mul hd0.ne' (by positivity : (1 + a) ≠ 0)]
    linarith
  have hsqrt : 2 ≤ Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
  have hσ : (1 / 2 : ℝ) ≤ σ := by
    have hdiv : 1 / Real.sqrt u ≤ (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num) hsqrt
    dsimp [σ, chen1973Lemma6Eq21Sigma, u] at *
    linarith
  have hσinv : σ⁻¹ ≤ 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hσ
    simpa using this
  have hhead : σ⁻¹ + Real.log a ≤ 2 * W := by
    rw [hloga]
    dsimp [W, v]
    linarith
  have hN : (1 : ℝ) ≤ N := by
    dsimp [N]; exact_mod_cast (Nat.le_add_left 1 _)
  have hterm : ∀ j ∈ Finset.range (r + 1),
      (Nat.choose r j : ℝ) * D ^ (r - j) *
        ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1)) ≤
      ((Nat.choose r j : ℝ) * (Nat.factorial j : ℝ)) * W ^ (r + 1) := by
    intro j hj
    have hpow : D ^ (r - j) ≤ W ^ (r + 1) := by
      calc
        _ ≤ W ^ (r - j) := pow_le_pow_left₀ hD0 hD _
        _ ≤ W ^ (r + 1) := pow_le_pow_right₀ hW (by omega)
    have hden : (Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1) ≤ Nat.factorial j := by
      exact div_le_self (by positivity) (one_le_pow₀ hN)
    calc
      _ ≤ (Nat.choose r j : ℝ) * W ^ (r + 1) * (Nat.factorial j : ℝ) := by
        gcongr
      _ = _ := by ring
  change (σ⁻¹ + Real.log a) * D ^ r + _ ≤ _
  calc
    _ ≤ (2 * W) * W ^ r +
        ∑ j ∈ Finset.range (r + 1),
          ((Nat.choose r j : ℝ) * (Nat.factorial j : ℝ)) * W ^ (r + 1) := by
      apply add_le_add
      · exact mul_le_mul hhead (pow_le_pow_left₀ hD0 hD r)
          (pow_nonneg hD0 _) (by linarith)
      · exact Finset.sum_le_sum hterm
    _ = (2 + ∑ j ∈ Finset.range (r + 1),
          (Nat.choose r j : ℝ) * (Nat.factorial j : ℝ)) * W ^ (r + 1) := by
      rw [← Finset.sum_mul, pow_succ]; ring
    _ = _ := by
      dsimp [chen1973Lemma6Eq21UniformBudgetConstant, W, v, u]
      rw [mul_pow]; ring

/-- Every fixed polynomial in `1 + log log x` is absorbed by `log x`.
The cutoff is independent of all conductor and prime-pair cells. -/
theorem chen1973Lemma6_eq21_eventually_loglog_pow_absorb
    (C : ℝ) (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      C * (1 + Real.log (Real.log (x : ℝ))) ^ n ≤ Real.log (x : ℝ) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlo := (isLittleO_pow_exp_pos_mul_atTop n
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto hloglog
  have heps : 0 < (1 / (|C| * 2 ^ n + 1) : ℝ) := by positivity
  filter_upwards [hlo.bound heps, hloglog.eventually_ge_atTop 1,
    hlog.eventually_gt_atTop 0] with x hbound ht hu
  let t := Real.log (Real.log (x : ℝ))
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hpow : t ^ n ≤ (1 / (|C| * 2 ^ n + 1)) * Real.exp t := by
    change ‖t ^ n‖ ≤ (1 / (|C| * 2 ^ n + 1)) * ‖Real.exp (1 * t)‖ at hbound
    simpa only [one_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ht0 n), abs_of_pos (Real.exp_pos t)] using hbound
  have hexp : Real.exp t = Real.log (x : ℝ) := Real.exp_log hu
  have hshift : (1 + t) ^ n ≤ (2 * t) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]; linarith
  change C * (1 + t) ^ n ≤ _
  calc
    _ ≤ |C| * (1 + t) ^ n := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * t) ^ n := mul_le_mul_of_nonneg_left hshift (abs_nonneg C)
    _ = (|C| * 2 ^ n) * t ^ n := by rw [mul_pow]; ring
    _ ≤ (|C| * 2 ^ n) * ((1 / (|C| * 2 ^ n + 1)) * Real.exp t) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ((|C| * 2 ^ n) / (|C| * 2 ^ n + 1)) * Real.log (x : ℝ) := by
      rw [hexp]; ring
    _ ≤ 1 * Real.log (x : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hu.le
      apply (div_le_one (by positivity)).mpr
      linarith
    _ = _ := one_mul _

/-- A single pre-cell threshold absorbs the real vertical-integral budget into
`PrimitiveVerticalEstimate 1`. The only analytic input is the actual full-height
pointwise `L'/L` bound; it is retained as a hypothesis, not claimed proved. -/
theorem chen1973Lemma6_eq21_primitiveVerticalEstimate_one_eventually_of_logDerivative_bound
    {M : ℝ} (hM : 0 ≤ M) (r : ℕ) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ t : ℝ,
          ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Eq21Line x t) χ /
            chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Eq21Line x t) χ‖ ≤
            M * (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r) →
      Chen1973Lemma6Eq21PrimitiveVerticalEstimate 1 x L B k m := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  rw [← Filter.eventually_atTop]
  filter_upwards [chen1973Lemma6_eq21_eventually_loglog_pow_absorb
      (3 * M * chen1973Lemma6Eq21UniformBudgetConstant r) (r + 1),
    hlog.eventually_ge_atTop 4, Filter.eventually_ge_atTop (3 : ℕ)] with x hsmall hu hx
  intro L B k m l₂ P H
  refine ⟨by norm_num, ?_⟩
  intro d hd χ pp hpp
  have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
  have hdle : (d : ℝ) ≤ Real.log x ^ (100 : ℕ) :=
    (show (d : ℝ) ≤ L by exact_mod_cast chen1973Lemma6_eq21_conductor_le hd).trans P.hL_lower
  have hregion := chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m hpp
  obtain ⟨hy, hlogy⟩ := chen1973Lemma6_eq21_primeRegion_log_y hx hregion
  have hbudget := chen1973Lemma6_eq21_budget_uniform hu
    (by exact_mod_cast hd1.le) hdle r
  obtain ⟨_hintegrable, hintegral⟩ :=
    chen1973Lemma6_eq21_verticalIntegral_bound_of_logDerivative_bound
      hx hd1 χ hy hM r (H d hd χ)
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  let D := 1 + Real.log ((d : ℝ) * (1 + a))
  let σ := chen1973Lemma6Eq21Sigma x
  let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  let budget := (σ⁻¹ + Real.log a) * D ^ r +
    ∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * D ^ (r - j) *
      ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1))
  change budget ≤ _ at hbudget
  change ‖((Real.log y)⁻¹ : ℂ) * chen1973Lemma6Eq21VerticalIntegral x d χ pp‖ ≤
    (M / (Real.pi * Real.log y)) * budget * y ^ σ at hintegral
  have hly : 0 < Real.log y := Real.log_pos hy
  have hpaid : M * budget ≤ Real.log y := by
    have hb := mul_le_mul_of_nonneg_left hbudget hM
    change Real.log (x : ℝ) / 3 ≤ Real.log y at hlogy
    nlinarith only [hb, hsmall, hlogy]
  have hpi : Real.log y ≤ Real.pi * Real.log y := by
    nlinarith [Real.pi_gt_three]
  have hcoef : (M / (Real.pi * Real.log y)) * budget ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    exact hpaid.trans hpi
  calc
    _ ≤ (M / (Real.pi * Real.log y)) * budget * y ^ σ := by
      simpa only [Complex.ofReal_inv] using hintegral
    _ ≤ 1 * y ^ σ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) _)

end AnalyticNumberTheory.LargeSieve
