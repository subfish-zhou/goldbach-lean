import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20ComplementaryMoments
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20CorrectedFinal

noncomputable section
set_option maxHeartbeats 2400000
open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve

/-- Height extraction preserves the conductor logarithm. -/
lemma eq20_log_height {T : ℝ} (hT : 1 ≤ T) :
    1 + Real.log T ≤ 2 * Real.sqrt T := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith : 0 < T))
  rw [Real.log_sqrt (by linarith : 0 ≤ T)] at h
  linarith

lemma eq20_derivative_height_algebra
    (Q a r W D v : ℝ) (hQ : 1 ≤ Q) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hW : 0 ≤ W) (hD : 0 ≤ D) :
    W * ((21000000 * Q^2 * (a + |v| + r)^2 *
      (1 + Real.log (Q * (1 + (a + |v| + r))))^4) / D / r^4) ≤
    (16 * 21000000 * W * Q^2 * (1+a+r)^2 *
      (1 + Real.log (Q * (1 + (1+a+r))))^4 / (D * r^4)) * (1+|v|)^4 := by
  let m := 1+a+r
  let T := 1+|v|
  let M := a+|v|+r
  let c := 1 + Real.log (Q*(1+m))
  have hm : 1 ≤ m := by dsimp [m]; linarith
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg v]
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMT : M ≤ m*T := by
    dsimp [M, m, T]
    nlinarith [mul_nonneg ha (abs_nonneg v), mul_nonneg hr (abs_nonneg v)]
  have hQT : Q*(1+M) ≤ (Q*(1+m))*T := by
    have hinner : 1+M ≤ (1+m)*T := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hinner (show 0 ≤ Q by linarith)]
  have hbase : 1 ≤ Q*(1+m) := by nlinarith
  have hc : 1 ≤ c := by
    dsimp [c]
    exact le_add_of_nonneg_right (Real.log_nonneg hbase)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog : 1 + Real.log (Q*(1+M)) ≤ c * (2*Real.sqrt T) := by
    calc
      _ ≤ 1 + Real.log ((Q*(1+m))*T) := by
        gcongr
      _ = c + Real.log T := by
        rw [Real.log_mul (by positivity : Q*(1+m) ≠ 0) (by positivity : T ≠ 0)]
        dsimp [c]
        ring
      _ ≤ c * (1+Real.log T) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (eq20_log_height hT) (by linarith)
  have hlog0 : 0 ≤ 1 + Real.log (Q*(1+M)) := by
    have hbaseM : 1 ≤ Q*(1+M) := by nlinarith
    linarith [Real.log_nonneg hbaseM]
  have hp : M^2 * (1 + Real.log (Q*(1+M)))^4 ≤
      (m*T)^2 * (c*(2*Real.sqrt T))^4 := by gcongr
  have hs : (Real.sqrt T)^2 = T := Real.sq_sqrt (by linarith)
  have hp' : M^2 * (1 + Real.log (Q*(1+M)))^4 ≤
      16*m^2*c^4*T^4 := hp.trans_eq (by
        calc
          _ = 16*m^2*c^4*T^2*((Real.sqrt T)^2)^2 := by ring
          _ = _ := by rw [hs]; ring)
  have hmult := mul_le_mul_of_nonneg_left hp'
    (show 0 ≤ W * 21000000 * Q^2 / (D*r^4) by positivity)
  dsimp [m, T, M, c] at hmult
  convert hmult using 1 <;> (try simp only [div_eq_mul_inv, mul_inv_rev]) <;> first | rfl | ring

def chen1973Lemma6Eq20BetaDerivativeCoefficient (x L level D Q : ℕ) : ℝ :=
  let β := chen1973Lemma6Beta x
  let r := 1 / (2 * Real.log (x : ℝ))
  let m0 := 1 + |β| + r
  16 * 21000000 * chen1973Lemma6Eq19I x L level * (Q : ℝ)^2 * m0^2 *
    (1 + Real.log ((Q : ℝ)*(1+m0)))^4 / ((D : ℝ)*r^4)

def chen1973Lemma6Eq20BetaLinearCoefficient (x L level B k H D Q : ℕ) : ℝ :=
  Real.sqrt (chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level *
    ((Q : ℝ) + (H : ℝ) / D) * (1 + Real.log H)) *
  Real.sqrt (Real.sqrt
    (62208 * chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level /
      Real.log x ^ 4 * ((Q : ℝ) + ((B * 2^k : ℕ) : ℝ)^2 / D) *
        ((B * 2^k : ℕ) : ℝ)^(2 - 4*chen1973Lemma6Beta x))) *
  Real.sqrt (Real.sqrt (chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q))

lemma eq20_fourth_root_height {G T : ℝ} (hG : 0 ≤ G) (hT : 0 ≤ T) :
    Real.sqrt (Real.sqrt (G*T^4)) = Real.sqrt (Real.sqrt G)*T := by
  rw [Real.sqrt_mul hG]
  have hT4 : Real.sqrt (T^4) = T^2 := by
    rw [show T^4 = (T^2)^2 by ring, Real.sqrt_sq (sq_nonneg T)]
  rw [hT4, Real.sqrt_mul (Real.sqrt_nonneg G), Real.sqrt_sq hT]

/-- Actual beta numerator, uniformly linear in height, with the S²/pair⁴/L'⁴ allocation. -/
theorem chen1973Lemma6B_eq20_beta_linear
    (x L level B k m H D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (hD : 0 < D) (hQ : 2 ≤ Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) (v : ℝ) :
    chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x + v*I) ≤
      chen1973Lemma6Eq20BetaLinearCoefficient x L level B k H D Q * (1+|v|) := by
  have hl : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hpaid := chen1973Lemma6B_eq20_beta_paid x L level B k m H D Q hx hB hD hQ hcell v
  dsimp only at hpaid
  have hd := eq20_derivative_height_algebra (Q : ℝ) |chen1973Lemma6Beta x|
    (1 / (2 * Real.log (x : ℝ))) (chen1973Lemma6Eq19I x L level) D v
    (by exact_mod_cast (show 1 ≤ Q by omega)) (abs_nonneg _) (by positivity)
    (chen1973Lemma6Eq19I_pos x L level).le (by positivity)
  change _ ≤ chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q * (1+|v|)^4 at hd
  have hG : 0 ≤ chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q := by
    unfold chen1973Lemma6Eq20BetaDerivativeCoefficient
    have := (chen1973Lemma6Eq19I_pos x L level).le
    positivity
  apply hpaid.trans
  calc
    _ ≤ _ * Real.sqrt (Real.sqrt
        (chen1973Lemma6Eq20BetaDerivativeCoefficient x L level D Q * (1+|v|)^4)) := by
      gcongr
    _ = _ := by
      rw [eq20_fourth_root_height hG (by positivity)]
      unfold chen1973Lemma6Eq20BetaLinearCoefficient
      ring


/-- A scale-preserving quadratic comparison: no `log(x)^(231/100)` payment. -/
lemma eq20_radial_factor_quadratic {u z : ℝ} {N : ℕ}
    (hz : 0 ≤ z) (hzu : z ≤ u) (hN : 2 ≤ N) :
    (1+u^N)⁻¹ ≤ 2 / (1+z^2) := by
  have hu : 0 ≤ u := hz.trans hzu
  have hz2 : z^2 ≤ u^2 := pow_le_pow_left₀ hz hzu 2
  have hden : 1+z^2 ≤ 2*(1+u^N) := by
    rcases le_total u 1 with hu1 | hu1
    · have hh : u^2 ≤ 1 := pow_le_one₀ hu hu1
      nlinarith [pow_nonneg hu N]
    · have hh : u^2 ≤ u^N := pow_le_pow_right₀ hu1 hN
      nlinarith [pow_nonneg hu N]
  rw [← one_div (1+u^N), div_le_div_iff₀ (by positivity) (by positivity)]
  simpa using hden

/-- The literal radial `|s|` pays the linear height before scaling the integral. -/
lemma eq20_linear_over_corrected_kernel
    {x : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 1/2 ≤ σ) (hv : 0 ≤ v) :
    (1+v) / chen1973Lemma6Eq17CorrectedKernel x (σ + v*I) ≤
      6 * (1+(v / chen1973PerronScale (x : ℝ))^2)⁻¹ := by
  let A := chen1973PerronScale (x : ℝ)
  let n := ‖(σ : ℂ) + v*I‖
  have hA : 0 < A := chen1973Lemma6_eq17_perronScale_pos (by omega)
  have hnσ : σ ≤ n := by
    calc
      σ = |((σ : ℂ)+v*I).re| := by simp [abs_of_nonneg (by linarith : 0 ≤ σ)]
      _ ≤ _ := Complex.abs_re_le_norm _
  have hnv : v ≤ n := by
    calc
      v = |((σ : ℂ)+v*I).im| := by simp [abs_of_nonneg hv]
      _ ≤ _ := Complex.abs_im_le_norm _
  have hn : 0 < n := by linarith
  have hlin : (1+v)/n ≤ 3 := (div_le_iff₀ hn).2 (by linarith)
  have hN : 2 ≤ chen1973PerronOrder (x : ℝ)+1 := by
    have := (chen1973Lemma6_eq17_one_le_log_and_order hx).2
    omega
  have hfac := eq20_radial_factor_quadratic
    (div_nonneg hv hA.le) (div_le_div_of_nonneg_right hnv hA.le) hN
  change (1+(n/A)^(chen1973PerronOrder (x : ℝ)+1))⁻¹ ≤ 2/(1+(v/A)^2) at hfac
  have hmul := mul_le_mul hlin hfac (by positivity) (by norm_num : (0:ℝ) ≤ 3)
  calc
    _ = ((1+v)/n) * (1+(n/A)^(chen1973PerronOrder (x : ℝ)+1))⁻¹ := by
      dsimp [n, A, chen1973Lemma6Eq17CorrectedKernel]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ 3 * (2/(1+(v/A)^2)) := hmul
    _ = _ := by dsimp [A]; ring

lemma eq20_scaled_cauchy_integrable {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun v : ℝ => (1+(v/A)^2)⁻¹) (Ioi 0) := by
  have hh := (integrableOn_Ioi_comp_mul_right_iff
    (fun v : ℝ => (1+v^2)⁻¹) 0 (inv_pos.2 hA)).2
    (by simpa using (integrable_inv_one_add_sq.integrableOn (s := Ioi (0:ℝ))))
  simpa only [div_eq_mul_inv] using hh

lemma eq20_scaled_cauchy_integral {A : ℝ} (hA : 0 < A) :
    (∫ v in Ioi (0:ℝ), (1+(v/A)^2)⁻¹) = A * (Real.pi/2) := by
  have hh := integral_comp_mul_right_Ioi (fun v : ℝ => (1+v^2)⁻¹) 0 (inv_pos.2 hA)
  simpa only [div_eq_mul_inv, zero_mul, inv_inv, smul_eq_mul,
    integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero] using hh

/-- A genuine integral theorem for the unchanged corrected kernel, preserving
`A=(log x)^(11/10)`. This generic analytic helper is consumed below by the actual
three-moment producer and an internally proved continuity theorem. -/
theorem eq20_corrected_linear_integrable_and_bound
    {x : ℕ} (hx : 3 ≤ x) {σ K : ℝ} (hσ : 1/2 ≤ σ) (hK : 0 ≤ K)
    (F : ℝ → ℝ) (hcont : Continuous F)
    (hF0 : ∀ v ∈ Ioi (0:ℝ), 0 ≤ F v)
    (hFK : ∀ v ∈ Ioi (0:ℝ), F v ≤ K*(1+v)) :
    IntegrableOn (fun v : ℝ => F v /
      chen1973Lemma6Eq17CorrectedKernel x (σ+v*I)) (Ioi 0) ∧
    (∫ v in Ioi (0:ℝ), F v / chen1973Lemma6Eq17CorrectedKernel x (σ+v*I)) ≤
      3 * Real.pi * chen1973PerronScale (x : ℝ) * K := by
  let A := chen1973PerronScale (x : ℝ)
  have hA : 0 < A := chen1973Lemma6_eq17_perronScale_pos (by omega)
  have hk (v : ℝ) : 0 < chen1973Lemma6Eq17CorrectedKernel x (σ+v*I) :=
    chen1973Lemma6_eq17_correctedKernel_pos (by omega) (by linarith)
  have hmajor : IntegrableOn (fun v : ℝ => (K*6)*(1+(v/A)^2)⁻¹) (Ioi 0) :=
    (eq20_scaled_cauchy_integrable hA).const_mul (K*6)
  have hpoint (v : ℝ) (hv : v ∈ Ioi (0:ℝ)) :
      F v / chen1973Lemma6Eq17CorrectedKernel x (σ+v*I) ≤
        (K*6)*(1+(v/A)^2)⁻¹ := by
    calc
      _ ≤ K*(1+v) / chen1973Lemma6Eq17CorrectedKernel x (σ+v*I) :=
        div_le_div_of_nonneg_right (hFK v hv) (hk v).le
      _ = K*((1+v) / chen1973Lemma6Eq17CorrectedKernel x (σ+v*I)) := by ring
      _ ≤ K*(6*(1+(v/A)^2)⁻¹) :=
        mul_le_mul_of_nonneg_left (eq20_linear_over_corrected_kernel hx hσ hv.le) hK
      _ = _ := by ring
  have hint : IntegrableOn (fun v : ℝ => F v /
      chen1973Lemma6Eq17CorrectedKernel x (σ+v*I)) (Ioi 0) := by
    apply Integrable.mono' hmajor
    · apply Continuous.aestronglyMeasurable
      apply Continuous.div hcont
      · unfold chen1973Lemma6Eq17CorrectedKernel
        fun_prop
      · exact fun v => (hk v).ne'
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hF0 v hv) (hk v).le)]
      exact hpoint v hv
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ v in Ioi (0:ℝ), (K*6)*(1+(v/A)^2)⁻¹ :=
      integral_mono_ae hint hmajor (ae_restrict_of_forall_mem measurableSet_Ioi hpoint)
    _ = (K*6)*(A*(Real.pi/2)) := by
      rw [integral_const_mul, eq20_scaled_cauchy_integral hA]
    _ = _ := by dsimp [A]; ring


/-- Continuity of the actual beta numerator; primitive conductors exceed one. -/
theorem chen1973Lemma6B_eq20_beta_continuous
    {x L level B k m H D Q : ℕ} (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    Continuous (fun v : ℝ => chen1973Lemma6B x L level B k m H
      (chen1973Lemma6Beta x+v*I)) := by
  unfold chen1973Lemma6B
  apply continuous_finsetSum
  intro d hd
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro χ hχ
  have hdmem := hcell hd
  have hd1 : 1 < d := by
    have hDd : D < d := (Finset.mem_Ioc.mp hdmem).1
    omega
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd1⟩
  have hχne : χ.1 ≠ 1 := by
    intro hχeq
    have hprim := χ.2
    rw [DirichletCharacter.IsPrimitive, hχeq,
      DirichletCharacter.conductor_one] at hprim
    omega
  have hline : Continuous (fun v : ℝ => ((chen1973Lemma6Beta x) : ℂ) + v * I) := by fun_prop
  have hL' : Continuous (fun v : ℝ =>
      chen1973PrimitiveLDeriv d ((chen1973Lemma6Beta x) + v * I) χ) := by
    unfold chen1973PrimitiveLDeriv
    split
    · exact ((χ.1.differentiable_LFunction hχne).deriv).continuous.comp hline
    · contradiction
  have hS : Continuous (fun v : ℝ =>
      chen1973Lemma6MobiusPartialSum H ((chen1973Lemma6Beta x) + v * I) χ) := by
    unfold chen1973Lemma6MobiusPartialSum
    apply continuous_finsetSum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    apply Continuous.div continuous_const
    · exact hline.const_cpow (Or.inl hn0)
    · intro v
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)
  apply Continuous.mul
  · apply Continuous.norm
    apply continuous_finsetSum
    intro pp hpp
    obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
    have hpair : (pp.1 : ℂ) * pp.2 ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hp₁.ne') (by exact_mod_cast hp₂.ne')
    by_cases hlog : Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) = 0
    · simpa [hlog] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    · apply Continuous.div continuous_const
      · exact (hline.const_cpow (Or.inl hpair)).mul continuous_const
      · intro v
        exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpair))
          (by exact_mod_cast hlog)
  · exact (hL'.mul hS).norm

/-- Explicit beta half-line budget with only one Perron scale, not a spurious
`x` normalization or a conductor-polynomial replacement of the logarithm. -/
def chen1973Lemma6Eq20BetaIntegralBudget (x L level B k H D Q : ℕ) : ℝ :=
  3 * Real.pi * Real.log x ^ ((11 : ℝ)/10) *
    chen1973Lemma6Eq20BetaLinearCoefficient x L level B k H D Q

/-- The new three moments are wired to the literal corrected beta integral.
No integrability, continuity, growth, scalar payment, or order hypothesis is
supplied by the caller. `H` is arbitrary, including zero. -/
theorem chen1973Lemma6_eq20_beta_integrable_and_budget
    (x L level B k m H D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (hD : 0 < D) (hQ : 2 ≤ Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    IntegrableOn (fun v : ℝ =>
      chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x+v*I) /
        chen1973Lemma6Eq17CorrectedKernel x (chen1973Lemma6Beta x+v*I)) (Ioi 0) ∧
    chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m H ≤
      chen1973Lemma6Eq20BetaIntegralBudget x L level B k H D Q := by
  have hl : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hβ : 1/2 ≤ chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    have hh : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hK : 0 ≤ chen1973Lemma6Eq20BetaLinearCoefficient x L level B k H D Q := by
    unfold chen1973Lemma6Eq20BetaLinearCoefficient
    positivity
  apply eq20_corrected_linear_integrable_and_bound hx hβ hK
    (fun v : ℝ => chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x+v*I))
    (chen1973Lemma6B_eq20_beta_continuous hD hcell)
  · intro v hv
    unfold chen1973Lemma6B
    positivity
  · intro v hv
    simpa only [abs_of_pos (mem_Ioi.mp hv)] using
      chen1973Lemma6B_eq20_beta_linear x L level B k m H D Q hx hB hD hQ hcell v

/-- The exact beta contribution in corrected (17)/(20), including its outer
`2 sqrt x`; no extra factor `sqrt x` is introduced. -/
theorem chen1973Lemma6_eq20_beta_contribution_budget
    (x L level B k m H D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (hD : 0 < D) (hQ : 2 ≤ Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    2 * (x : ℝ)^((1 : ℝ)/2) *
      chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m H ≤
    6 * Real.pi * (x : ℝ)^((1 : ℝ)/2) * Real.log x ^ ((11 : ℝ)/10) *
      chen1973Lemma6Eq20BetaLinearCoefficient x L level B k H D Q := by
  have hh := (chen1973Lemma6_eq20_beta_integrable_and_budget
    x L level B k m H D Q hx hB hD hQ hcell).2
  calc
    _ ≤ 2 * (x : ℝ)^((1 : ℝ)/2) *
        chen1973Lemma6Eq20BetaIntegralBudget x L level B k H D Q :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by unfold chen1973Lemma6Eq20BetaIntegralBudget; ring

end AnalyticNumberTheory.LargeSieve
