import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FiniteContourBudget
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FiniteLogDerivative
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FiniteZeroFreeProducer
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FiniteScalar

noncomputable section
open Real Filter Complex
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace AnalyticNumberTheory.LargeSieve

/-- Only literal nonvanishing on the enlarged finite rectangle. -/
def rawFiniteZeroFreeInput (x L : ℕ) : Prop :=
  ∀ d ∈ chen1973Lemma6ConductorBlock x L 0, ∀ χ : PrimitiveCharacter d,
    ∀ s : ℂ, 1 - 2 / Real.sqrt (Real.log (x : ℝ)) ≤ s.re → s.re ≤ 2 →
      |s.im| ≤ Real.log (x : ℝ)^2 + 1 → chen1973Lemma6PrimitiveLValue d s χ ≠ 0

lemma finite_sigma_geometry {x : ℕ} (hu : 64 ≤ Real.log (x : ℝ)) :
    (1:ℝ)/2 ≤ chen1973Lemma6Eq21Sigma x ∧ chen1973Lemma6Alpha x ≤ 2 := by
  have hu0 : 0 < Real.log (x : ℝ) := by linarith
  have hr := Real.sq_sqrt hu0.le
  have hr8 : 8 ≤ Real.sqrt (Real.log (x : ℝ)) := by
    nlinarith [Real.sqrt_nonneg (Real.log (x : ℝ))]
  have hi : 1 / Real.sqrt (Real.log (x : ℝ)) ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 hu0)).2
    linarith
  have hiu : 1 / Real.log (x : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hu0).2
    linarith
  constructor <;> dsimp [chen1973Lemma6Eq21Sigma, chen1973Lemma6Alpha] <;> linarith

lemma finite_power_gap {x : ℕ} {y : ℝ} (hu : 64 ≤ Real.log (x : ℝ))
    (hy : 1 < y) (hyx : y ≤ x) :
    y ^ chen1973Lemma6Alpha x ≤ y ^ chen1973Lemma6Eq21Sigma x *
      Real.exp (1 + Real.sqrt (Real.log (x : ℝ))) := by
  let u := Real.log (x : ℝ)
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hr0 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hly : Real.log y ≤ u := Real.log_le_log (by linarith) hyx
  have hgap : chen1973Lemma6Alpha x - chen1973Lemma6Eq21Sigma x =
      1/u + 1/Real.sqrt u := by
    dsimp [chen1973Lemma6Alpha, chen1973Lemma6Eq21Sigma, u]; ring
  have he : (chen1973Lemma6Alpha x - chen1973Lemma6Eq21Sigma x)*Real.log y ≤
      1 + Real.sqrt u := by
    rw [hgap]
    calc
      _ ≤ (1/u + 1/Real.sqrt u)*u := mul_le_mul_of_nonneg_left hly (by positivity)
      _ = 1 + Real.sqrt u := by
        have hr := Real.sq_sqrt hu0.le
        field_simp
        nlinarith
  calc
    _ = y ^ chen1973Lemma6Eq21Sigma x *
        y ^ (chen1973Lemma6Alpha x - chen1973Lemma6Eq21Sigma x) := by
      rw [← Real.rpow_add (by linarith : 0 < y)]
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
      rw [Real.rpow_def_of_pos (by linarith : 0 < y)]
      exact Real.exp_le_exp.mpr (by simpa [mul_comm, u] using he)

/-- Both finite-contour pieces are paid, retaining the actual smoothing floor. -/
lemma finite_star_payment {x : ℕ} {y : ℝ}
    (hu : 64 ≤ Real.log (x : ℝ)) (hy : 1 < y) (hyx : y ≤ x)
    (hly : Real.log (x : ℝ)/3 ≤ Real.log y)
    (hleft : ∀ σ : ℝ, (1:ℝ)/2 ≤ σ →
      eq21FiniteScalarMbar (Real.log (x:ℝ)) *
        (σ⁻¹ + Real.log (Real.log (x:ℝ)^2)) ≤ Real.log (x:ℝ)/3)
    (htail : 8 * Real.exp (1 + Real.sqrt (Real.log (x:ℝ))) *
      (chen1973PerronScale (x:ℝ) / Real.log (x:ℝ)^2)^
        (chen1973PerronOrder (x:ℝ)+1) * Real.log (x:ℝ)^2 ≤ 1) :
    let u := Real.log (x:ℝ)
    let σ := chen1973Lemma6Eq21Sigma x
    let α := chen1973Lemma6Alpha x
    let M := eq21FiniteScalarMbar u
    let N := chen1973PerronOrder (x:ℝ)+1
    y^σ * M * (σ⁻¹ + Real.log (u^2)) / (Real.pi * Real.log y) +
      y^α / (Real.pi * Real.log y) * (chen1973PerronScale (x:ℝ)/u^2)^N *
        (6*u^2/(N:ℝ) + (α-σ)*M/u^2) ≤ 2*y^σ := by
  dsimp only
  let u := Real.log (x:ℝ)
  let σ := chen1973Lemma6Eq21Sigma x
  let α := chen1973Lemma6Alpha x
  let M := eq21FiniteScalarMbar u
  let N := chen1973PerronOrder (x:ℝ)+1
  let r := (chen1973PerronScale (x:ℝ)/u^2)^N
  change y^σ*M*(σ⁻¹+Real.log (u^2))/(Real.pi*Real.log y) +
    y^α/(Real.pi*Real.log y)*r*(6*u^2/(N:ℝ)+(α-σ)*M/u^2) ≤ 2*y^σ
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hu1 : 1 ≤ u := by dsimp [u]; linarith
  have hu2 : 1 ≤ u^2 := one_le_pow₀ hu1
  have hM0 : 0 ≤ M := by
    dsimp [M, eq21FiniteScalarMbar]
    have := Real.log_nonneg hu1
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 32)
    positivity
  have hMs : M ≤ u/3 := by
    have hh := hleft 1 (by norm_num)
    have hl := Real.log_nonneg hu2
    simp only [inv_one] at hh
    change M*(1+Real.log (u^2)) ≤ u/3 at hh
    exact (le_mul_of_one_le_right hM0 (by linarith only [hl])).trans hh
  have hσ := (finite_sigma_geometry hu).1
  have hα := (finite_sigma_geometry hu).2
  have hσα : 0 ≤ α-σ := by
    change 0 ≤ (1+1/u)-(1-1/Real.sqrt u)
    have : 0 ≤ 1/u := by positivity
    have : 0 ≤ 1/Real.sqrt u := by positivity
    linarith
  have hgap : α-σ ≤ 2 := by change (1:ℝ)/2 ≤ σ at hσ; change α ≤ 2 at hα; linarith
  have hN : (1:ℝ) ≤ N := by dsimp [N]; exact_mod_cast Nat.le_add_left 1 _
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hden1 : 1 ≤ Real.pi*Real.log y := by
    have hpi := Real.pi_gt_three
    have hly1 : 1 ≤ Real.log y := by dsimp [u] at hu0; linarith
    nlinarith
  have hden0 : 0 < Real.pi*Real.log y := by linarith
  have hlypi : Real.log y ≤ Real.pi*Real.log y := by
    have := Real.pi_gt_three
    have := Real.log_pos hy
    nlinarith
  have hleftpay : y^σ*M*(σ⁻¹+Real.log (u^2))/(Real.pi*Real.log y) ≤ y^σ := by
    apply (div_le_iff₀ hden0).2
    calc
      _ = y^σ * (M*(σ⁻¹+Real.log (u^2))) := by ring
      _ ≤ y^σ * (u/3) := mul_le_mul_of_nonneg_left (hleft σ hσ) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hly.trans hlypi) (by positivity)
  have hbracket : 6*u^2/(N:ℝ)+(α-σ)*M/u^2 ≤ 8*u^2 := by
    have hn : 6*u^2/(N:ℝ) ≤ 6*u^2 := (div_le_self (by positivity) hN)
    have hm : (α-σ)*M/u^2 ≤ 2*u^2 := by
      apply (div_le_iff₀ (pow_pos hu0 2)).2
      calc
        _ ≤ 2*(u/3) := mul_le_mul hgap hMs hM0 (by norm_num)
        _ ≤ 2*u^2 := by nlinarith only [hu1, sq_nonneg (u-1)]
        _ ≤ 2*u^2*u^2 := le_mul_of_one_le_right (by positivity) hu2
    calc
      _ ≤ 6*u^2 + 2*u^2 := add_le_add hn hm
      _ = _ := by ring
  have hr : 0 ≤ r := by dsimp [r, chen1973PerronScale]; positivity
  have hb0 : 0 ≤ 6*u^2/(N:ℝ)+(α-σ)*M/u^2 := by positivity
  have hright : y^α/(Real.pi*Real.log y)*r*(6*u^2/(N:ℝ)+(α-σ)*M/u^2) ≤ y^σ := by
    calc
      _ ≤ (y^σ * Real.exp (1+Real.sqrt u))*r*(8*u^2) := by
        apply mul_le_mul _ hbracket hb0 (by positivity)
        apply mul_le_mul_of_nonneg_right _ hr
        exact (div_le_self (by positivity) hden1).trans (finite_power_gap hu hy hyx)
      _ = y^σ * (8*Real.exp (1+Real.sqrt u)*r*u^2) := by ring
      _ ≤ y^σ * 1 := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := mul_one _
  simpa only [two_mul] using add_le_add hleftpay hright

/-- Uniform actual-term estimate, derived only from finite raw nonvanishing. -/
theorem chen1973Lemma6_eq21_actualTerm_two_eventually_of_finiteZeroFree :
    ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      rawFiniteZeroFreeInput x L →
      ∀ d ∈ chen1973Lemma6ConductorBlock x L 0, ∀ χ : PrimitiveCharacter d,
      ∀ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1*pp.2 : ℕ) : ZMod d)‖ /
          Real.log ((x:ℝ)/((pp.1:ℝ)*pp.2)) ≤
        2*((x:ℝ)/((pp.1:ℝ)*pp.2))^chen1973Lemma6Eq21Sigma x := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  rw [← Filter.eventually_atTop]
  filter_upwards [hlog.eventually_ge_atTop 64,
    chen1973Lemma6_eq21_finite_left_budget_eventually,
    chen1973Lemma6_eq21_finite_tail_eventually 8 2 (by norm_num)] with x hu hl ht
  intro L B k m l₂ P hz d hd χ pp hpp
  have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
  have hdL : (d:ℝ) ≤ L := by exact_mod_cast chen1973Lemma6_eq21_conductor_le hd
  have hdu : (d:ℝ) ≤ Real.log (x:ℝ)^100 := hdL.trans P.hL_lower
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  obtain ⟨hy, hly⟩ := chen1973Lemma6_eq21_primeRegion_log_y P.hx
    (chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m hpp)
  have hyx : (x:ℝ)/((pp.1:ℝ)*pp.2) ≤ x := by
    apply div_le_self (by positivity)
    have h1 : (1:ℝ) ≤ pp.1 := by exact_mod_cast hp₁
    have h2 : (1:ℝ) ≤ pp.2 := by exact_mod_cast hp₂
    nlinarith
  have hu0 : 0 < Real.log (x:ℝ) := by linarith
  have hu1 : 1 ≤ Real.log (x:ℝ) := by linarith
  have hM : 0 ≤ eq21FiniteScalarMbar (Real.log (x:ℝ)) := by
    unfold eq21FiniteScalarMbar
    have := Real.log_nonneg hu1
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 32)
    positivity
  have hzero : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ Real.log (x:ℝ)^2 →
      chen1973Lemma6PrimitiveLValue d s χ ≠ 0 := by
    intro s hs ha him
    apply hz d hd χ s
    · dsimp [chen1973Lemma6Eq21Sigma] at hs
      have hh : 1 - 2 / Real.sqrt (Real.log (x:ℝ)) ≤
          1 - 1 / Real.sqrt (Real.log (x:ℝ)) := by
        apply sub_le_sub_left
        exact div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
      exact hh.trans hs
    · exact ha.trans (finite_sigma_geometry hu).2
    · linarith
  have hderiv : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ Real.log (x:ℝ)^2 →
      ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤
      eq21FiniteScalarMbar (Real.log (x:ℝ)) := by
    intro s hs ha him
    exact Eq21FiniteLogDerivative.norm_primitive_logDeriv_le_uniform hd1 χ hu hdu
      (hz d hd χ) s hs ha him
  exact (Eq21FiniteContour_truncated_term_bound P.hx hd1 χ hp₁ hp₂ hy
    (one_le_pow₀ hu1) hM hzero hderiv).trans
      (finite_star_payment hu hy hyx hly hl ht)

/-- Actual finite character and prime-pair sums; no shifted whole-line object. -/
lemma finite_actual_Nm_le_four {x L B k m l₂ : ℕ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hterm : ∀ d ∈ chen1973Lemma6ConductorBlock x L 0, ∀ χ : PrimitiveCharacter d,
      ∀ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1*pp.2 : ℕ) : ZMod d)‖ /
          Real.log ((x:ℝ)/((pp.1:ℝ)*pp.2)) ≤
        2*((x:ℝ)/((pp.1:ℝ)*pp.2))^chen1973Lemma6Eq21Sigma x) :
    chen1973Lemma6NmBlockActual x L 0 B k m ≤
      4*Real.log (x:ℝ)^200*chen1973Lemma6Eq21PrimeSum x := by
  classical
  let f := fun (d : ℕ) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) =>
    (((Real.log ((x:ℝ)/((pp.1:ℝ)*pp.2)))⁻¹ : ℝ) : ℂ) *
      chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1*pp.2 : ℕ) : ZMod d)
  have hinner : ∀ d ∈ chen1973Lemma6ConductorBlock x L 0, ∀ χ : PrimitiveCharacter d,
      ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m, f d χ pp‖ ≤
        2*chen1973Lemma6Eq21PrimeSum x := by
    intro d hd χ
    calc
      _ ≤ ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m, ‖f d χ pp‖ := norm_sum_le _ _
      _ ≤ ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          2*((x:ℝ)/((pp.1:ℝ)*pp.2))^chen1973Lemma6Eq21Sigma x := by
        apply Finset.sum_le_sum
        intro pp hpp
        have hy := (chen1973Lemma6_eq21_primeRegion_log_y P.hx
          (chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m hpp)).1
        have he : ‖f d χ pp‖ =
            ‖chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1*pp.2 : ℕ) : ZMod d)‖ /
              Real.log ((x:ℝ)/((pp.1:ℝ)*pp.2)) := by
          dsimp [f]
          rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_inv, abs_of_pos (Real.log_pos hy)]
          ring
        rw [he]
        exact hterm d hd χ pp hpp
      _ ≤ ∑ pp ∈ chen1973Lemma6Eq21PrimeRegion x,
          2*((x:ℝ)/((pp.1:ℝ)*pp.2))^chen1973Lemma6Eq21Sigma x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m)
        intro pp _ _
        positivity
      _ = 2*chen1973Lemma6Eq21PrimeSum x := by
        unfold chen1973Lemma6Eq21PrimeSum
        rw [Finset.mul_sum]
  have hchars : ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
      ‖∑ χ : PrimitiveCharacter d, star (χ.1 (x : ZMod d)) *
        ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m, f d χ pp‖ ≤
      Fintype.card (PrimitiveCharacter d) * (2*chen1973Lemma6Eq21PrimeSum x) := by
    intro d hd
    calc
      _ ≤ ∑ χ : PrimitiveCharacter d, ‖star (χ.1 (x : ZMod d)) *
        ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m, f d χ pp‖ := norm_sum_le _ _
      _ ≤ ∑ _χ : PrimitiveCharacter d, (2*chen1973Lemma6Eq21PrimeSum x) := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul, norm_star]
        calc
          _ ≤ 1 * ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m, f d χ pp‖ :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ.1 _) (norm_nonneg _)
          _ ≤ _ := by simpa only [one_mul] using hinner d hd χ
      _ = _ := by simp
  unfold chen1973Lemma6NmBlockActual
  calc
    _ ≤ ∑ d ∈ chen1973Lemma6ConductorBlock x L 0,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * (3:ℝ)^d.primeFactors.card/d *
        (Fintype.card (PrimitiveCharacter d) * (2*chen1973Lemma6Eq21PrimeSum x)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hchars d hd) (by positivity)
    _ = chen1973Lemma6Eq21ConductorMass x L * (2*chen1973Lemma6Eq21PrimeSum x) := by
      unfold chen1973Lemma6Eq21ConductorMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ (2*Real.log (x:ℝ)^200) * (2*chen1973Lemma6Eq21PrimeSum x) := by
      apply mul_le_mul_of_nonneg_right (chen1973Lemma6_eq21_conductorMass_le_log200 P)
      exact mul_nonneg (by norm_num) (chen1973Lemma6_eq21_primeSum_nonneg x)
    _ = _ := by ring

/-- Equation (21) for actual Nm under only the finite nonvanishing rectangle. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_finiteZeroFree :
    ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      rawFiniteZeroFreeInput x L →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤ (x:ℝ)/Real.log (x:ℝ)^20 := by
  obtain ⟨Xt, hterm⟩ := chen1973Lemma6_eq21_actualTerm_two_eventually_of_finiteZeroFree
  obtain ⟨Cpair, _, hmertens⟩ := chen1973Lemma6_eq21_primeReciprocalMass_bounded
  rw [← Filter.eventually_atTop]
  filter_upwards [Filter.eventually_ge_atTop Xt,
    chen1973Lemma6_eq21_eventually_exp_log220_le_one (4*Cpair)] with x hxt hlarge
  intro L B k m l₂ P hz
  have hNm := finite_actual_Nm_le_four P (hterm x hxt L B k m l₂ P hz)
  have hprime := chen1973Lemma6_eq21_primeSum_exponential_decay Cpair hmertens P.hx
  have hlog : 0 < Real.log (x:ℝ) := by linarith [P.hlog_one]
  rw [le_div_iff₀ (pow_pos hlog 20)]
  calc
    _ ≤ (4*Real.log (x:ℝ)^200*chen1973Lemma6Eq21PrimeSum x)*Real.log (x:ℝ)^20 := by gcongr
    _ ≤ (4*Real.log (x:ℝ)^200*(Cpair*(x:ℝ)*Real.exp (-Real.sqrt (Real.log (x:ℝ))/3)))*
        Real.log (x:ℝ)^20 := by gcongr
    _ = (x:ℝ)*((4*Cpair)*Real.exp (-Real.sqrt (Real.log (x:ℝ))/3)*Real.log (x:ℝ)^220) := by ring
    _ ≤ (x:ℝ)*1 := by gcongr
    _ = _ := mul_one _

/-- Fixed-c quadratic L(1) data produce the finite rectangle. No Siegel lower
bound itself is asserted, and c is fixed before the threshold. -/
theorem finite_rawInput_of_fixedSiegel (c : ℝ) (hc : 0 < c) :
    ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0, ∀ χ : PrimitiveCharacter d,
        χ.1^2 = 1 → c*(d:ℝ)^(-(1/10000:ℝ)) ≤
          (chen1973Lemma6PrimitiveLValue d 1 χ).re) → rawFiniteZeroFreeInput x L := by
  obtain ⟨X₀, hX⟩ := Eq21FiniteZeroFreeProducer.finiteRectangle_of_fixedSiegel c hc
  refine ⟨X₀, ?_⟩
  intro x hx L B k m l₂ P hs d hd χ s hlo hhi him
  have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd1⟩
  have hdL : (d:ℝ) ≤ L := by exact_mod_cast chen1973Lemma6_eq21_conductor_le hd
  have hdu := hdL.trans P.hL_lower
  have hSiegel : χ.1^2 = 1 → c*(d:ℝ)^(-(1/10000:ℝ)) ≤ (χ.1.LFunction 1).re := by
    intro hquad
    simpa only [chen1973Lemma6PrimitiveLValue, dif_pos hd1] using hs d hd χ hquad
  have hz := hX x hx d hd1 hdu χ.1 χ.2 hSiegel s hlo hhi him
  simpa only [chen1973Lemma6PrimitiveLValue, dif_pos hd1] using hz

/-- Final actual Nm bound, conditional solely on fixed-c raw quadratic L(1)
lower bounds. All analytic finite-contour and nonquadratic inputs are derived. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_fixedSiegel
    (c : ℝ) (hc : 0 < c) :
    ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0, ∀ χ : PrimitiveCharacter d,
        χ.1^2 = 1 → c*(d:ℝ)^(-(1/10000:ℝ)) ≤
          (chen1973Lemma6PrimitiveLValue d 1 χ).re) →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤ (x:ℝ)/Real.log (x:ℝ)^20 := by
  obtain ⟨Xf, hf⟩ := chen1973Lemma6_equation21_levelZero_eventually_of_finiteZeroFree
  obtain ⟨Xs, hs⟩ := finite_rawInput_of_fixedSiegel c hc
  refine ⟨max Xf Xs, ?_⟩
  intro x hx L B k m l₂ P hSiegel
  exact hf x ((le_max_left _ _).trans hx) L B k m l₂ P
    (hs x ((le_max_right _ _).trans hx) L B k m l₂ P hSiegel)

/-- Literal Dirichlet L-function formulation of the fixed-c terminal. The
local NeZero instance is derived from actual block membership, not assumed. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_rawQuadraticL1
    (c : ℝ) (hc : 0 < c) :
    ∃ X₀ : ℕ, ∀ x ≥ X₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      (∀ (d : ℕ) (hd : d ∈ chen1973Lemma6ConductorBlock x L 0),
        let : NeZero d := ⟨Nat.ne_zero_of_lt (chen1973Lemma6_eq21_one_lt_conductor hd)⟩
        ∀ χ : PrimitiveCharacter d, χ.1^2 = 1 →
          c*(d:ℝ)^(-(1/10000:ℝ)) ≤ (χ.1.LFunction 1).re) →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤ (x:ℝ)/Real.log (x:ℝ)^20 := by
  obtain ⟨X₀, hX⟩ := chen1973Lemma6_equation21_levelZero_eventually_of_fixedSiegel c hc
  refine ⟨X₀, ?_⟩
  intro x hx L B k m l₂ P hs
  apply hX x hx L B k m l₂ P
  intro d hd χ hquad
  have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
  simpa only [chen1973Lemma6PrimitiveLValue, dif_pos hd1] using hs d hd χ hquad

end AnalyticNumberTheory.LargeSieve
