import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21StripFinal

noncomputable section
open MeasureTheory Set Complex Real Filter
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- A fixed sublinear log-power loss is still absorbed uniformly before cells. -/
theorem chen1973Lemma6_eq21_eventually_powerLoss_loglog_absorb
    (C : ℝ) (n : ℕ) {θ : ℝ} (hθ : θ < 1) :
    ∀ᶠ x : ℕ in atTop,
      C * Real.log (x : ℝ) ^ θ * (1 + Real.log (Real.log (x : ℝ))) ^ n ≤
        Real.log (x : ℝ) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlo := (isLittleO_pow_exp_pos_mul_atTop n
    (sub_pos.mpr hθ)).comp_tendsto hloglog
  have heps : 0 < (1 / (|C| * 2 ^ n + 1) : ℝ) := by positivity
  filter_upwards [hlo.bound heps, hloglog.eventually_ge_atTop 1,
    hlog.eventually_gt_atTop 0] with x hbound ht hu
  let u := Real.log (x : ℝ)
  let t := Real.log u
  have hu0 : 0 < u := hu
  have ht0 : 0 ≤ t := by dsimp [t, u]; linarith
  have hpow : t ^ n ≤ (1 / (|C| * 2 ^ n + 1)) * Real.exp ((1 - θ) * t) := by
    change ‖t ^ n‖ ≤ (1 / (|C| * 2 ^ n + 1)) * ‖Real.exp ((1 - θ) * t)‖ at hbound
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0 n),
      abs_of_pos (Real.exp_pos _)] using hbound
  have hshift : (1 + t) ^ n ≤ (2 * t) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t, u]; linarith
  have hbase : C * (1 + t) ^ n ≤ Real.exp ((1 - θ) * t) := by
    calc
      _ ≤ |C| * (1 + t) ^ n := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (2 * t) ^ n := mul_le_mul_of_nonneg_left hshift (abs_nonneg C)
      _ = (|C| * 2 ^ n) * t ^ n := by rw [mul_pow]; ring
      _ ≤ (|C| * 2 ^ n) * ((1 / (|C| * 2 ^ n + 1)) * Real.exp ((1 - θ) * t)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((|C| * 2 ^ n) / (|C| * 2 ^ n + 1)) * Real.exp ((1 - θ) * t) := by ring
      _ ≤ 1 * Real.exp ((1 - θ) * t) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply (div_le_one (by positivity)).mpr
        linarith
      _ = _ := one_mul _
  change C * u ^ θ * (1 + t) ^ n ≤ u
  calc
    _ = u ^ θ * (C * (1 + t) ^ n) := by ring
    _ ≤ u ^ θ * Real.exp ((1 - θ) * t) :=
      mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hu0.le _)
    _ = u := by
      rw [Real.rpow_def_of_pos hu0, ← Real.exp_add]
      have he : Real.log u * θ + (1 - θ) * t = Real.log u := by dsimp [t]; ring
      rw [he, Real.exp_log hu0]

/-- Fixed sublinear loss: the cutoff remains before all cells. -/
theorem chen1973Lemma6_eq21_primitiveVerticalEstimate_one_eventually_of_powerLoss
    {M θ : ℝ} (hM : 0 ≤ M) (hθ : θ < 1) (r : ℕ) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ t : ℝ,
          ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Eq21Line x t) χ /
            chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Eq21Line x t) χ‖ ≤
            (M * Real.log (x : ℝ) ^ θ) * (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r) →
      Chen1973Lemma6Eq21PrimitiveVerticalEstimate 1 x L B k m := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  rw [← Filter.eventually_atTop]
  filter_upwards [chen1973Lemma6_eq21_eventually_powerLoss_loglog_absorb
      (3 * M * chen1973Lemma6Eq21UniformBudgetConstant r) (r + 1) hθ,
    hlog.eventually_ge_atTop 4, Filter.eventually_ge_atTop (3 : ℕ)] with x hsmall hu hx
  intro L B k m l₂ P H
  let Mx := M * Real.log (x : ℝ) ^ θ
  have hMx : 0 ≤ Mx := mul_nonneg hM (Real.rpow_nonneg (by linarith) _)
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
      hx hd1 χ hy hMx r (H d hd χ)
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
    (Mx / (Real.pi * Real.log y)) * budget * y ^ σ at hintegral
  have hly : 0 < Real.log y := Real.log_pos hy
  have hpaid : Mx * budget ≤ Real.log y := by
    have hb := mul_le_mul_of_nonneg_left hbudget hMx
    change Real.log (x : ℝ) / 3 ≤ Real.log y at hlogy
    dsimp [Mx] at hb ⊢
    nlinarith
  have hpi : Real.log y ≤ Real.pi * Real.log y := by
    nlinarith [Real.pi_gt_three]
  have hcoef : (Mx / (Real.pi * Real.log y)) * budget ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    exact hpaid.trans hpi
  calc
    _ ≤ (Mx / (Real.pi * Real.log y)) * budget * y ^ σ := by
      simpa only [Complex.ofReal_inv] using hintegral
    _ ≤ 1 * y ^ σ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) _)

/-- Source-level equation (21) with a real sublinear log-power loss.
All integral and geometric payments are internal; the full-height zero-free
input and the displayed actual strip logarithmic-derivative bound remain. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_strip_powerLoss
    {M c θ : ℝ} (hM : 0 ≤ M) (hc : 0 < c) (hθ : θ < 1) (r : ℕ) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      Chen1973Lemma6Eq21ZeroFreeInput x L c →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ s : ℂ,
          chen1973Lemma6Eq21Sigma x ≤ s.re ∧ s.re ≤ chen1973Lemma6Alpha x →
          ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤
            (M * Real.log (x : ℝ) ^ θ) *
              (1 + Real.log ((d : ℝ) * (1 + |s.im|))) ^ r) →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤
        (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  obtain ⟨x₁, hfinal⟩ :=
    chen1973Lemma6_equation21_levelZero_eventually_of_source_analytic_inputs 1 c hc
  obtain ⟨x₂, hvertical⟩ :=
    chen1973Lemma6_eq21_primitiveVerticalEstimate_one_eventually_of_powerLoss hM hθ r
  obtain ⟨x₃, horder⟩ := Filter.eventually_atTop.mp (chen1973Lemma6_eq21_order_eventually r)
  refine ⟨max x₁ (max x₂ x₃), ?_⟩
  intro x hx L B k m l₂ P hzero H
  have hx₂ : x₂ ≤ x := (le_max_left x₂ x₃).trans ((le_max_right _ _).trans hx)
  have hx₃ : x₃ ≤ x := (le_max_right x₂ x₃).trans ((le_max_right _ _).trans hx)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by have := P.hx; omega))
  let Mx := M * Real.log (x : ℝ) ^ θ
  have hMx : 0 ≤ Mx := mul_nonneg hM (Real.rpow_nonneg hlog.le _)
  have Hleft : ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
      ∀ χ : PrimitiveCharacter d, ∀ t : ℝ,
        ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Eq21Line x t) χ /
          chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Eq21Line x t) χ‖ ≤
          Mx * (1 + Real.log ((d : ℝ) * (1 + |t|))) ^ r := by
    intro d hd χ t
    have h := H d hd χ (chen1973Lemma6Eq21Line x t) (by
      simpa [chen1973Lemma6Eq21Line] using
        And.intro (le_refl (chen1973Lemma6Eq21Sigma x))
          (chen1973Lemma6_eq21_sigma_le_alpha P.hx))
    simpa only [Mx, chen1973Lemma6Eq21Line, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add] using h
  apply hfinal x ((le_max_left _ _).trans hx) L B k m l₂ P hzero
  · intro d hd χ pp hpp
    have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
    have hregion := chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m hpp
    have hy := (chen1973Lemma6_eq21_primeRegion_log_y P.hx hregion).1
    refine ⟨?_, chen1973Lemma6_eq21_alphaTerm_integrable P.hx hd1 χ (zero_lt_one.trans hy), ?_⟩
    · exact (chen1973Lemma6_eq21_verticalIntegral_bound_of_logDerivative_bound
        P.hx hd1 χ hy hMx r (Hleft d hd χ)).1
    · exact chen1973Lemma6_eq21_horizontal_decay_of_strip_logDerivative
        P.hx hd1 χ hy hMx r (horder x hx₃) (H d hd χ)
  · exact hvertical x hx₂ L B k m l₂ P Hleft

end AnalyticNumberTheory.LargeSieve
