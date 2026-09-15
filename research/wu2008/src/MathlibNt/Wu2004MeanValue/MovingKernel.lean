import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerPerronAssembly

/-!
# A common moving product cutoff

The profile depends on the source coordinate, but not on the conductor or
character. Its Mellin coefficient is an entire function of the spectral
parameter; it is not treated as a constant when shifting a contour.
-/

noncomputable section
open Classical Complex Finset MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

def movingCoefficient (f : ℕ → ℂ) (v : ℕ → ℕ) (x : ℕ) (s : ℂ) (a : ℕ) : ℂ :=
  f a * ((liuPanPerronHalfStep (v a) / liuPanPerronHalfStep x : ℝ) : ℂ) ^ s

theorem movingCoefficient_norm_le (f : ℕ → ℂ) (v : ℕ → ℕ) (x : ℕ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hv : ∀ a, v a ≤ x) {s : ℂ} (hs : 0 ≤ s.re) :
    ∀ a, ‖movingCoefficient f v x s a‖ ≤ 1 := by
  intro a
  have hratio : 0 < liuPanPerronHalfStep (v a) / liuPanPerronHalfStep x :=
    div_pos (halfStep_pos _) (halfStep_pos _)
  have hratio1 : liuPanPerronHalfStep (v a) / liuPanPerronHalfStep x ≤ 1 := by
    apply (div_le_one (halfStep_pos _)).mpr
    have : (v a : ℝ) ≤ x := by exact_mod_cast hv a
    unfold liuPanPerronHalfStep
    linarith
  rw [movingCoefficient, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hratio]
  exact mul_le_one₀ (hf a) (by positivity)
    (Real.rpow_le_one hratio.le hratio1 hs)

theorem movingCoefficient_differentiable (f : ℕ → ℂ) (v : ℕ → ℕ) (x a : ℕ) :
    Differentiable ℂ (fun s => movingCoefficient f v x s a) := by
  have hne : ((liuPanPerronHalfStep (v a) / liuPanPerronHalfStep x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos (halfStep_pos _) (halfStep_pos _)).ne'
  exact (differentiable_const _).mul (differentiable_id.const_cpow (Or.inl hne))

theorem movingCoefficient_power (f : ℕ → ℂ) (v : ℕ → ℕ) (x a : ℕ) (s : ℂ) :
    movingCoefficient f v x s a * (liuPanPerronHalfStep x : ℂ) ^ s =
      f a * (liuPanPerronHalfStep (v a) : ℂ) ^ s := by
  unfold movingCoefficient
  rw [mul_assoc, ← Complex.mul_cpow_ofReal_nonneg
    (div_pos (halfStep_pos _) (halfStep_pos _)).le (halfStep_pos _).le]
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (halfStep_pos x).ne']

def movingAmplitude {q : ℕ} (A B : ℕ → ℂ) (v : ℕ → ℕ) (L U : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ a ∈ Ioc L U, A a * χ.1 (a : ZMod q) *
    ∑ n ∈ Icc 1 (v a / a), B n * χ.1 (n : ZMod q)

def movingPerronIntegral {q : ℕ} (S V : Finset ℕ) (A B : ℕ → ℂ)
    (v : ℕ → ℕ) (χ : PrimitiveCharacter q) (σ T : ℝ) : ℂ :=
  ∑ a ∈ S, liuPanTruncatedPerronIntegral {a} V A B χ.1 σ T (v a)

theorem movingAmplitude_eq_hyperbolas {q : ℕ} (A B : ℕ → ℂ)
    (v : ℕ → ℕ) (L U M : ℕ) (χ : PrimitiveCharacter q)
    (hv : ∀ a ∈ Ioc L U, v a ≤ M) :
    movingAmplitude A B v L U χ =
      ∑ a ∈ Ioc L U, liuPanPerronHyperbolaSum {a} (Icc 1 M) A B χ.1 (v a) := by
  apply sum_congr rfl
  intro a ha
  have ha0 : 0 < a := (Nat.zero_le L).trans_lt (mem_Ioc.mp ha).1
  have hset : Ioc (a - 1) a = {a} := by ext n; simp; omega
  have h := source_amplitude_eq_hyperbola A B (v a) (a - 1) a M χ (hv a ha)
  simpa only [panSourceCharacterAmplitude, hset, sum_singleton] using h

/-- Only the truncation remainder is estimated rowwise; reciprocal product
weights are retained even at the exponential prime cutoff. -/
theorem moving_error_le_harmonic {q x : ℕ} {T : ℝ}
    (S V : Finset ℕ) (A B : ℕ → ℂ) (v : ℕ → ℕ) (χ : PrimitiveCharacter q)
    (hS : ∀ a ∈ S, 0 < a) (hV : ∀ n ∈ V, 0 < n)
    (hA : ∀ a ∈ S, ‖A a‖ ≤ 1) (hB : ∀ n ∈ V, ‖B n‖ ≤ 1)
    (hx : 1 ≤ Real.log x) (hv : ∀ a ∈ S, 1 ≤ v a ∧ v a ≤ x) (hT : 0 < T) :
    ‖(∑ a ∈ S, liuPanPerronHyperbolaSum {a} V A B χ.1 (v a)) -
      movingPerronIntegral S V A B v χ (panSourceSigma x) T‖ ≤
      (108 * (x : ℝ) ^ 3 / T) *
        (∑ a ∈ S, (a : ℝ)⁻¹) * (∑ n ∈ V, (n : ℝ)⁻¹) := by
  unfold movingPerronIntegral
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ S, ‖liuPanTruncatedPerronError {a} V A B χ.1
        (panSourceSigma x) T (v a)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ S, (108 * (x : ℝ) ^ 3 / T) *
        (a : ℝ)⁻¹ * (∑ n ∈ V, (n : ℝ)⁻¹) := by
      apply sum_le_sum
      intro a ha
      simpa only [sum_singleton] using hyperbola_error_le_harmonic {a} V A B χ.1
        (by intro u hu; simpa only [mem_singleton.mp hu] using hS a ha)
        hV (by intro u hu; simpa only [mem_singleton.mp hu] using hA a ha)
        hB hx (hv a ha).1 (hv a ha).2 hT
    _ = _ := by rw [← sum_mul, ← mul_sum]

/-- Genuine Perron truncation for arbitrary source-coordinate cutoffs, with
the same inverse-square error as the fixed-cutoff producer. -/
theorem moving_amplitude_perron {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (v : ℕ → ℕ) (m L U : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hv : ∀ a ∈ Ioc L U, 1 ≤ v a ∧ v a ≤ x)
    (hUx : U ≤ x) :
    ‖movingAmplitude (panSourceG f m) (panSourceD m) v L U χ -
      movingPerronIntegral (Ioc L U) (Icc 1 ⌊panSourceHeight x⌋₊)
        (panSourceG f m) (panSourceD m) v χ (panSourceSigma x) (panSourceHeight x)‖ ≤
      324 * ((x : ℝ) ^ 2)⁻¹ := by
  have hxlog : 1 ≤ Real.log (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast source_pos_of_log hxlog
  have hx0 : (0 : ℝ) < x := by linarith
  have hT : 0 < panSourceHeight x := Real.exp_pos _
  have hS : Ioc L U ⊆ Icc 1 x := by
    intro a ha
    have := mem_Ioc.mp ha
    exact mem_Icc.mpr ⟨by omega, this.2.trans hUx⟩
  have hN : 0 < (⌊panSourceHeight x⌋₊ : ℝ) := by
    have := (source_pos_of_log hxlog).trans_le (sourceHeight_floor_ge hxlog)
    exact_mod_cast this
  have hlogx : Real.log (x : ℝ) ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hEU : (∑ a ∈ Ioc L U, (a : ℝ)⁻¹) ≤ x :=
    (harmonic_energy_le_log _ x hS).trans (by linarith)
  have hEV : (∑ n ∈ Icc 1 ⌊panSourceHeight x⌋₊, (n : ℝ)⁻¹) ≤ 3 * (x : ℝ) ^ 2 := by
    have hlogT := Real.log_le_log hN (Nat.floor_le hT.le)
    rw [show Real.log (panSourceHeight x) = 2 * (Real.log x) ^ 2 by
      simp only [panSourceHeight, Real.log_exp]] at hlogT
    have hsquare : (Real.log (x : ℝ)) ^ 2 ≤ (x : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    refine (harmonic_energy_le_log _ _ (fun _ h => h)).trans ?_
    nlinarith
  rw [movingAmplitude_eq_hyperbolas _ _ _ _ _ _ χ
    (fun a ha => (hv a ha).2.trans (sourceHeight_floor_ge hxlog))]
  calc
    _ ≤ (108 * (x : ℝ) ^ 3 / panSourceHeight x) *
        (∑ a ∈ Ioc L U, (a : ℝ)⁻¹) *
        (∑ n ∈ Icc 1 ⌊panSourceHeight x⌋₊, (n : ℝ)⁻¹) :=
      moving_error_le_harmonic _ _ _ _ v χ
        (fun a ha => (mem_Icc.mp (hS ha)).1)
        (fun n hn => (mem_Icc.mp hn).1)
        (fun _ _ => panSourceG_norm_le f hf _ _)
        (fun _ _ => panSourceD_norm_le _ _) hxlog hv hT
    _ ≤ (108 * (x : ℝ) ^ 3 / panSourceHeight x) * x * (3 * (x : ℝ) ^ 2) := by
      gcongr
    _ = 324 * (x : ℝ) ^ 6 / panSourceHeight x := by ring
    _ ≤ 324 * (x : ℝ) ^ 6 / (x : ℝ) ^ 8 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (sourceHeight_ge_pow 8 hxlog (by norm_num; linarith))
    _ = _ := by field_simp

def movingG {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ) (x m A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  panDyadicG (movingCoefficient f v x s) m A₁ A₂ k χ s

/-- The actual moving source polynomial is entire. In particular, its
spectral coefficient is differentiated rather than frozen. -/
theorem movingG_differentiable {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) :
    Differentiable ℂ (movingG f v x m A₁ A₂ k χ) := by
  unfold movingG panDyadicG
  apply Differentiable.fun_sum
  intro a ha
  have ha0 : (a : ℂ) ≠ 0 := by
    exact_mod_cast ((Nat.zero_le _).trans_lt (mem_Ioc.mp ha).1).ne'
  have hcoeff : Differentiable ℂ (fun s => panSourceG (movingCoefficient f v x s) m a) := by
    unfold panSourceG
    split_ifs
    · exact movingCoefficient_differentiable f v x a
    · exact differentiable_const _
  exact (hcoeff.mul_const _).div (differentiable_id.const_cpow (Or.inl ha0))
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl ha0))

end Wu2004MeanValue