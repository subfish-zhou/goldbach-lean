import MathlibNt.Wu2004MeanValue.MovingKernel

noncomputable section
open Classical Complex Finset MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

private theorem polynomial_differentiable {q : ℕ} (S : Finset ℕ) (A : ℕ → ℂ)
    (χ : PrimitiveCharacter q) (hS : ∀ a ∈ S, 0 < a) :
    Differentiable ℂ (polynomial S A χ) :=
  panFinitePolynomial_differentiable S (fun a => A a * χ.1 (a : ZMod q)) hS

private theorem row_continuous {q : ℕ} (V : Finset ℕ) (A B : ℕ → ℂ)
    (v : ℕ → ℕ) (χ : PrimitiveCharacter q) (σ : ℝ) (hσ : 0 < σ)
    (hV : ∀ n ∈ V, 0 < n) (a : ℕ) (ha : 0 < a) :
    Continuous (fun t =>
      ((A a * χ.1 (a : ZMod q) / (a : ℂ) ^ liuPanPerronLine σ t) *
        polynomial V B χ (liuPanPerronLine σ t)) *
        (liuPanPerronHalfStep (v a) : ℂ) ^ liuPanPerronLine σ t /
        liuPanPerronLine σ t) := by
  have hline : Continuous (liuPanPerronLine σ) := by unfold liuPanPerronLine; fun_prop
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hY : (liuPanPerronHalfStep (v a) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfStep_pos _).ne'
  have hne (t : ℝ) : liuPanPerronLine σ t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [liuPanPerronLine] at this
    linarith
  exact ((((continuous_const.div
    ((differentiable_id.const_cpow (Or.inl ha0)).continuous.comp hline)
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl ha0))).mul
    ((polynomial_differentiable V B χ hV).continuous.comp hline)).mul
    ((differentiable_id.const_cpow (Or.inl hY)).continuous.comp hline)).div hline hne)

/-- Exact finite-sum interchange and common-power factorization. The profile
is shared across all characters; no modulus-dependent coefficients occur. -/
theorem movingPerronIntegral_eq_integral {q : ℕ} (S V : Finset ℕ)
    (A B : ℕ → ℂ) (v : ℕ → ℕ) (x : ℕ) (χ : PrimitiveCharacter q)
    (σ T : ℝ) (hσ : 0 < σ) (hS : ∀ a ∈ S, 0 < a) (hV : ∀ n ∈ V, 0 < n) :
    movingPerronIntegral S V A B v χ σ T =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t in -T..T,
          polynomial S (movingCoefficient A v x (liuPanPerronLine σ t)) χ
            (liuPanPerronLine σ t) *
          polynomial V B χ (liuPanPerronLine σ t) *
          (liuPanPerronHalfStep x : ℂ) ^ liuPanPerronLine σ t /
            liuPanPerronLine σ t := by
  have hrow (a : ℕ) (ha : a ∈ S) :
      liuPanTruncatedPerronIntegral {a} V A B χ.1 σ T (v a) =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t in -T..T,
            (A a * χ.1 (a : ZMod q) / (a : ℂ) ^ liuPanPerronLine σ t) *
              polynomial V B χ (liuPanPerronLine σ t) *
              (liuPanPerronHalfStep (v a) : ℂ) ^ liuPanPerronLine σ t /
                liuPanPerronLine σ t := by
    unfold liuPanTruncatedPerronIntegral
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [perron_polynomial_eq {a} A (by
      intro n hn
      simpa only [mem_singleton.mp hn] using hS a ha) χ (liuPanPerronLine σ t),
      perron_polynomial_eq V B hV χ (liuPanPerronLine σ t)]
    have hexp : Complex.exp (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep (v a))) =
        (liuPanPerronHalfStep (v a) : ℂ) ^ liuPanPerronLine σ t := by
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (halfStep_pos _).ne'),
        ← Complex.ofReal_log (halfStep_pos _).le, mul_comm]
    rw [hexp]
    simp only [polynomial, sum_singleton]
    ring
  have hpoint (t : ℝ) :
      polynomial S (movingCoefficient A v x (liuPanPerronLine σ t)) χ
          (liuPanPerronLine σ t) *
        polynomial V B χ (liuPanPerronLine σ t) *
        (liuPanPerronHalfStep x : ℂ) ^ liuPanPerronLine σ t /
          liuPanPerronLine σ t =
      ∑ a ∈ S,
        (A a * χ.1 (a : ZMod q) / (a : ℂ) ^ liuPanPerronLine σ t) *
          polynomial V B χ (liuPanPerronLine σ t) *
          (liuPanPerronHalfStep (v a) : ℂ) ^ liuPanPerronLine σ t /
            liuPanPerronLine σ t := by
    simp only [polynomial, sum_mul, sum_div]
    apply sum_congr rfl
    intro a _
    have hp := movingCoefficient_power A v x a (liuPanPerronLine σ t)
    calc
      _ = (movingCoefficient A v x (liuPanPerronLine σ t) a *
          (liuPanPerronHalfStep x : ℂ) ^ liuPanPerronLine σ t) *
          (χ.1 (a : ZMod q) / (a : ℂ) ^ liuPanPerronLine σ t *
            ∑ n ∈ V, B n * χ.1 (n : ZMod q) / (n : ℂ) ^ liuPanPerronLine σ t) /
            liuPanPerronLine σ t := by ring
      _ = _ := by rw [hp]; ring
  unfold movingPerronIntegral
  rw [sum_congr rfl hrow]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum
    (fun a ha => (row_continuous V A B v χ σ hσ hV a (hS a ha)).intervalIntegrable (-T) T),
    mul_sum]

def movingShortKernel {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  movingG f v x m A₁ A₂ k χ s * panShortF₁ m H χ s *
    (liuPanPerronHalfStep x : ℂ) ^ s / s

def movingLongKernel {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (T : ℝ) (s : ℂ) : ℂ :=
  movingG f v x m A₁ A₂ k χ s * longF₂ m H T χ s *
    (liuPanPerronHalfStep x : ℂ) ^ s / s

def movingShortIntegral {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (σ T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -T..T, movingShortKernel f v x m H A₁ A₂ k χ (liuPanPerronLine σ t)

def movingLongIntegral {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (σ T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -T..T, movingLongKernel f v x m H A₁ A₂ k χ T (liuPanPerronLine σ t)

theorem movingShortKernel_differentiableOn {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) :
    DifferentiableOn ℂ (movingShortKernel f v x m H A₁ A₂ k χ) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hY : (liuPanPerronHalfStep x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfStep_pos x).ne'
  exact (((movingG_differentiable f v x m A₁ A₂ k χ s).mul
    (panShortF₁_differentiable m H χ s)).mul
    (differentiableAt_id.const_cpow (Or.inl hY))).div
    differentiableAt_id hs0 |>.differentiableWithinAt

theorem movingShortKernel_line_continuous {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t => movingShortKernel f v x m H A₁ A₂ k χ (liuPanPerronLine σ t)) := by
  apply ContinuousOn.comp_continuous
    (movingShortKernel_differentiableOn f v x m H A₁ A₂ k χ).continuousOn
    (by unfold liuPanPerronLine; fun_prop)
  intro t
  simpa [liuPanPerronLine] using hσ

theorem movingLongKernel_line_continuous {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (T σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t => movingLongKernel f v x m H A₁ A₂ k χ T
      (liuPanPerronLine σ t)) := by
  have hline : Continuous (liuPanPerronLine σ) := by unfold liuPanPerronLine; fun_prop
  have hne (t : ℝ) : liuPanPerronLine σ t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [liuPanPerronLine] at this
    linarith
  have hY : (liuPanPerronHalfStep x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfStep_pos x).ne'
  exact ((((movingG_differentiable f v x m A₁ A₂ k χ).continuous.comp hline).mul
    ((longF₂_differentiable m H T χ).continuous.comp hline)).mul
    ((differentiable_id.const_cpow (Or.inl hY)).continuous.comp hline)).div hline hne

/-- Both finite prime polynomials are retained in the actual moving integral. -/
theorem moving_perron_eq_short_add_long {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) {σ T : ℝ}
    (hσ : 0 < σ) (hH : H ≤ ⌊T⌋₊) :
    movingPerronIntegral
      (Ioc (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂)) (Icc 1 ⌊T⌋₊)
      (panSourceG f m) (panSourceD m) v χ σ T =
      movingShortIntegral f v x m H A₁ A₂ k χ σ T +
        movingLongIntegral f v x m H A₁ A₂ k χ σ T := by
  rw [movingPerronIntegral_eq_integral _ _ _ _ v x χ σ T hσ
    (fun a ha => (Nat.zero_le _).trans_lt (mem_Ioc.mp ha).1)
    (fun n hn => (mem_Icc.mp hn).1)]
  have hcoeff (s : ℂ) :
      movingCoefficient (panSourceG f m) v x s = panSourceG (movingCoefficient f v x s) m := by
    funext a
    unfold movingCoefficient panSourceG
    split_ifs <;> simp
  simp_rw [hcoeff, full_prime_polynomial_split m H _ hH]
  change _ = _
  have hpoint (t : ℝ) :
      polynomial (Ioc (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂))
        (panSourceG (movingCoefficient f v x (liuPanPerronLine σ t)) m) χ
        (liuPanPerronLine σ t) *
        (panShortF₁ m H χ (liuPanPerronLine σ t) +
          polynomial (Ioc H ⌊T⌋₊) (panSourceD m) χ (liuPanPerronLine σ t)) *
        (liuPanPerronHalfStep x : ℂ) ^ liuPanPerronLine σ t / liuPanPerronLine σ t =
      movingShortKernel f v x m H A₁ A₂ k χ (liuPanPerronLine σ t) +
        movingLongKernel f v x m H A₁ A₂ k χ T (liuPanPerronLine σ t) := by
    unfold movingShortKernel movingLongKernel movingG panDyadicG longF₂ polynomial
    ring
  simp_rw [hpoint]
  unfold movingShortIntegral movingLongIntegral
  rw [intervalIntegral.integral_add
    ((movingShortKernel_line_continuous f v x m H A₁ A₂ k χ σ hσ).intervalIntegrable (-T) T)
    ((movingLongKernel_line_continuous f v x m H A₁ A₂ k χ T σ hσ).intervalIntegrable (-T) T),
    mul_add]

end Wu2004MeanValue