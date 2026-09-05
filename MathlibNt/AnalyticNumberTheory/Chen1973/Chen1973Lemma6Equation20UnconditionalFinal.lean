import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17CorrectedAssembly
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19FixedPowerEnvelopes
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19SourceParameters
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20CorrectedFinal
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (20): unconditional analytic final

This leaf removes the former continuity, growth, scalar-payment, and contour
premises.  Its two coefficients are explicit fixed-power expressions.  The
alpha coefficient is obtained from the corrected-kernel `21/10` envelope; the
beta coefficient keeps a multiplicative `2,4,4` Hölder estimate and
the fourth-power corrected-kernel envelope.
-/

noncomputable section
set_option maxHeartbeats 2400000

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- Literal source data for a positive-level complementary equation-(20) cell. -/
structure Chen1973Lemma6Eq20ComplementarySourceParameters
    (x L B lastD level k : ℕ) : Prop where
  hx : 3 ≤ x
  horder_four : 4 ≤ chen1973PerronOrder (x : ℝ) + 1
  hL : 0 < L
  hB : 0 < B
  hlevel : 1 ≤ level
  hlog_one : 1 ≤ Real.log x
  hL_lower : (L : ℝ) ≤ Real.log x ^ (100 : ℕ)
  hL_upper : Real.log x ^ (100 : ℕ) < L + 1
  hB_lower : (B : ℝ) ≤ (x : ℝ) ^ ((13 : ℝ) / 30)
  hB_upper : (x : ℝ) ^ ((13 : ℝ) / 30) < B + 1
  hcell : chen1973Lemma6Eq20Cell x L B lastD level k

/-- Lower endpoint of the literal positive-level conductor cell. -/
def chen1973Lemma6Eq20SourceD (L level : ℕ) : ℕ :=
  L * 2 ^ (level - 1)

/-- Upper endpoint of the literal positive-level conductor cell. -/
def chen1973Lemma6Eq20SourceQ (L level : ℕ) : ℕ :=
  L * 2 ^ level

lemma chen1973Lemma6Eq20SourceD_pos
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    0 < chen1973Lemma6Eq20SourceD L level := by
  unfold chen1973Lemma6Eq20SourceD
  exact Nat.mul_pos P.hL (pow_pos (by omega) _)

lemma chen1973Lemma6Eq20SourceQ_ge_two
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    2 ≤ chen1973Lemma6Eq20SourceQ L level := by
  unfold chen1973Lemma6Eq20SourceQ
  have hp : 2 ≤ 2 ^ level := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) P.hlevel)
  exact le_trans hp (Nat.le_mul_of_pos_left _ P.hL)

lemma chen1973Lemma6Eq20SourceD_lt_Q
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    chen1973Lemma6Eq20SourceD L level < chen1973Lemma6Eq20SourceQ L level := by
  unfold chen1973Lemma6Eq20SourceD chen1973Lemma6Eq20SourceQ
  apply Nat.mul_lt_mul_of_pos_left
  · exact Nat.pow_lt_pow_right (by omega) (Nat.sub_lt P.hlevel (by omega))
  · exact P.hL

/-- The actual conductor block lies in the source positive-level interval. -/
theorem chen1973Lemma6_eq20_conductorBlock_subset_source_Ioc
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    chen1973Lemma6ConductorBlock x L level ⊆
      Finset.Ioc (chen1973Lemma6Eq20SourceD L level)
        (chen1973Lemma6Eq20SourceQ L level) := by
  intro d hd
  unfold chen1973Lemma6ConductorBlock at hd
  rw [if_neg (Nat.ne_of_gt P.hlevel)] at hd
  simp only [chen1973Lemma6DyadicShell, Finset.mem_filter] at hd
  apply Finset.mem_Ioc.mpr
  have hlev : level - 1 + 1 = level := Nat.sub_add_cancel P.hlevel
  exact ⟨by simpa [chen1973Lemma6Eq20SourceD] using hd.1.2.1,
    by simpa [chen1973Lemma6Eq20SourceQ, hlev] using hd.1.2.2⟩

/-- Closed-interval form used by the fourth-moment producer. -/
theorem chen1973Lemma6_eq20_conductorBlock_subset_source_Icc
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k) :
    chen1973Lemma6ConductorBlock x L level ⊆
      Finset.Icc 2 (chen1973Lemma6Eq20SourceQ L level) := by
  intro d hd
  have h := chen1973Lemma6_eq20_conductorBlock_subset_source_Ioc P hd
  exact Finset.mem_Icc.mpr ⟨by
    have hD := chen1973Lemma6Eq20SourceD_pos P
    exact Nat.succ_le_iff.mpr (lt_of_le_of_lt hD (Finset.mem_Ioc.mp h).1),
    (Finset.mem_Ioc.mp h).2⟩

/-- Explicit alpha half-line bound; there is no caller-supplied growth,
continuity, or integral-payment premise. -/
def chen1973Lemma6Eq20UnconditionalFirstBound
    (x L level B k m H D Q : ℕ) : ℝ :=
  (2 * Real.log x ^ ((231 : ℝ) / 100) / chen1973Lemma6Alpha x) *
    chen1973Lemma6Eq19FirstFixedPower x L level B k m H D Q
      (chen1973Lemma6Alpha x) *
    ∫ v in Ioi (0 : ℝ), chen1973Lemma6Eq19LinearDecay v

/-- The raw beta half-line coefficient supplied by fourth-power decay. -/
def chen1973Lemma6Eq20UnconditionalSecondRawBound
    (x L level B k m H D Q : ℕ) (r : ℝ) : ℝ :=
  (2 * Real.log x ^ ((22 : ℝ) / 5) / chen1973Lemma6Beta x) *
    chen1973Lemma6Eq19SecondFixedPower x L level B k m H D Q
      (chen1973Lemma6Beta x) r *
    ∫ v in Ioi (0 : ℝ), chen1973Lemma6Eq19QuadraticDecay v

/-- Raw beta budget divided by `sqrt x`. This is only a normalization;
smallness of this explicit coefficient still requires a separate proof. -/
def chen1973Lemma6Eq20UnconditionalSecondBound
    (x L level B k m H D Q : ℕ) (r : ℝ) : ℝ :=
  chen1973Lemma6Eq20UnconditionalSecondRawBound x L level B k m H D Q r *
    (x : ℝ) ^ (-(1 : ℝ) / 2)

private lemma secondRaw_eq_normalized
    {x L level B k m H D Q : ℕ} {r : ℝ} (hx : 0 < x) :
    chen1973Lemma6Eq20UnconditionalSecondRawBound x L level B k m H D Q r =
      chen1973Lemma6Eq20UnconditionalSecondBound x L level B k m H D Q r *
        (x : ℝ) ^ ((1 : ℝ) / 2) := by
  unfold chen1973Lemma6Eq20UnconditionalSecondBound
  rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast hx)]
  norm_num

/-- The alpha integral is bounded by the derived fixed `21/10` envelope. -/
theorem chen1973Lemma6_eq20_first_integral_unconditional
    {x L level B k m H D Q : ℕ}
    (hx : 3 ≤ x) (hH : 0 < H) (hD : 0 < D) (hDQ : D < Q)
    (horder : 3 ≤ chen1973PerronOrder (x : ℝ) + 1)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq20CorrectedFirstIntegral x L level B k m H ≤
      chen1973Lemma6Eq20UnconditionalFirstBound x L level B k m H D Q := by
  let G := chen1973Lemma6Eq19FirstFixedPower x L level B k m H D Q
    (chen1973Lemma6Alpha x)
  have hα : 1 ≤ chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    linarith [one_div_pos.mpr hl]
  have hfixed := chen1973Lemma6_eq19_first_fixedPower_integrable_and_bound
    x L level B k m H D Q (chen1973Lemma6Alpha x) hx hH hD hDQ hα horder hcell
  have hpoint : ∀ v ∈ Ioi (0 : ℝ),
      chen1973Lemma6A x L level B k m H (chen1973Lemma6Alpha x + v * I) ≤
        G * (1 + v) := by
    intro v hv
    exact chen1973Lemma6_eq19_first_le_fixedPower x L level B k m H D Q
      (chen1973Lemma6Alpha x) v hH hD hDQ hα (mem_Ioi.mp hv).le hcell
  have hkpos : ∀ v : ℝ, 0 < chen1973Lemma6Eq17CorrectedKernel x
      (chen1973Lemma6Alpha x + v * I) := fun v =>
    chen1973Lemma6_eq17_correctedKernel_pos (by omega : 1 < x)
      (lt_of_lt_of_le zero_lt_one hα)
  have hmeasA : AEStronglyMeasurable (fun v : ℝ =>
      chen1973Lemma6A x L level B k m H ((chen1973Lemma6Alpha x) + v * I) /
        chen1973Lemma6Eq17CorrectedKernel x ((chen1973Lemma6Alpha x) + v * I)) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · unfold chen1973Lemma6A
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
      have hline : Continuous (fun v : ℝ => ((chen1973Lemma6Alpha x) : ℂ) + v * I) := by fun_prop
      have hL : Continuous (fun v : ℝ =>
          chen1973Lemma6PrimitiveLValue d ((chen1973Lemma6Alpha x) + v * I) χ) := by
        unfold chen1973Lemma6PrimitiveLValue
        split
        · exact (χ.1.differentiable_LFunction hχne).continuous.comp hline
        · contradiction
      have hS : Continuous (fun v : ℝ =>
          chen1973Lemma6MobiusPartialSum H ((chen1973Lemma6Alpha x) + v * I) χ) := by
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
      · exact (continuous_const.sub (hL.mul hS)).norm
    · unfold chen1973Lemma6Eq17CorrectedKernel
      fun_prop
    · intro v
      exact (chen1973Lemma6_eq17_correctedKernel_pos
        (x := x) (v := v) (show 1 < x by omega) (lt_of_lt_of_le zero_lt_one hα)).ne'
  have hint : IntegrableOn (fun v : ℝ =>
      chen1973Lemma6A x L level B k m H (chen1973Lemma6Alpha x + v * I) /
        chen1973Lemma6Eq17CorrectedKernel x (chen1973Lemma6Alpha x + v * I)) (Ioi 0) := by
    apply Integrable.mono' hfixed.1 hmeasA.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (by unfold chen1973Lemma6A; positivity) (hkpos v).le)]
    exact div_le_div_of_nonneg_right (hpoint v hv) (hkpos v).le
  unfold chen1973Lemma6Eq20CorrectedFirstIntegral
    chen1973Lemma6Eq20UnconditionalFirstBound
  exact (integral_mono_ae hint hfixed.1
    (ae_restrict_of_forall_mem measurableSet_Ioi fun v hv =>
      div_le_div_of_nonneg_right (hpoint v hv) (hkpos v).le)).trans hfixed.2

/-- The beta integral is bounded by the derived multiplicative `2,4,4`
fourth-power envelope and is displayed with its `x¹ᐟ²` normalization. -/
theorem chen1973Lemma6_eq20_second_integral_unconditional
    {x L level B k m H D Q : ℕ} {r : ℝ}
    (hx : 3 ≤ x) (hD : 0 < D) (hQ : 2 ≤ Q) (hr : 0 < r)
    (horder : 4 ≤ chen1973PerronOrder (x : ℝ) + 1)
    (hcellIoc : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q)
    (hcellIcc : chen1973Lemma6ConductorBlock x L level ⊆ Icc 2 Q)
    (hdom : ∀ t : ℝ, Chen1973Lemma3Domain
      (chen1973Lemma6Beta x + t * I) (chen1973Lemma6Beta x) t)
    (hsphere : ∀ t : ℝ, ∀ z ∈ Metric.sphere (chen1973Lemma6Beta x + t * I) r,
      Chen1973Lemma3Domain z z.re z.im) :
    chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m H ≤
      chen1973Lemma6Eq20UnconditionalSecondBound x L level B k m H D Q r *
        (x : ℝ) ^ ((1 : ℝ) / 2) := by
  let G := chen1973Lemma6Eq19SecondFixedPower x L level B k m H D Q
    (chen1973Lemma6Beta x) r
  have hβ : 0 < chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    linarith [one_div_pos.mpr hl]
  have hfixed := chen1973Lemma6_eq19_second_fixedPower_integrable_and_bound
    x L level B k m H D Q (chen1973Lemma6Beta x) r hx hβ horder
  have hpoint : ∀ v ∈ Ioi (0 : ℝ),
      chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x + v * I) ≤
        G * (1 + v) ^ 2 := by
    intro v hv
    apply chen1973Lemma6_eq19_second_le_fixedPower
      x L level B k m H D Q (chen1973Lemma6Beta x) r v hD hQ hr (mem_Ioi.mp hv).le
      hcellIoc hcellIcc
    · intro t ht
      exact hdom t
    · intro z hz
      exact hsphere v z hz
  have hkpos : ∀ v : ℝ, 0 < chen1973Lemma6Eq17CorrectedKernel x
      (chen1973Lemma6Beta x + v * I) := fun v =>
    chen1973Lemma6_eq17_correctedKernel_pos (by omega : 1 < x) hβ
  have hmeasB : AEStronglyMeasurable (fun v : ℝ =>
      chen1973Lemma6B x L level B k m H ((chen1973Lemma6Beta x) + v * I) /
        chen1973Lemma6Eq17CorrectedKernel x ((chen1973Lemma6Beta x) + v * I)) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · unfold chen1973Lemma6B
      apply continuous_finsetSum
      intro d hd
      apply Continuous.mul continuous_const
      apply continuous_finsetSum
      intro χ hχ
      have hdmem := hcellIoc hd
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
    · unfold chen1973Lemma6Eq17CorrectedKernel
      fun_prop
    · intro v
      exact (chen1973Lemma6_eq17_correctedKernel_pos
        (x := x) (v := v) (show 1 < x by omega) hβ).ne'
  have hint : IntegrableOn (fun v : ℝ =>
      chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x + v * I) /
        chen1973Lemma6Eq17CorrectedKernel x (chen1973Lemma6Beta x + v * I)) (Ioi 0) := by
    apply Integrable.mono' hfixed.1 hmeasB.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (by unfold chen1973Lemma6B; positivity) (hkpos v).le)]
    exact div_le_div_of_nonneg_right (hpoint v hv) (hkpos v).le
  have hraw : chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m H ≤
      chen1973Lemma6Eq20UnconditionalSecondRawBound x L level B k m H D Q r := by
    unfold chen1973Lemma6Eq20CorrectedSecondIntegral
      chen1973Lemma6Eq20UnconditionalSecondRawBound
    exact (integral_mono_ae hint hfixed.1
      (ae_restrict_of_forall_mem measurableSet_Ioi fun v hv =>
        div_le_div_of_nonneg_right (hpoint v hv) (hkpos v).le)).trans hfixed.2
  rw [secondRaw_eq_normalized (show 0 < x by omega)] at hraw
  exact hraw

/-- Final corrected equation-(20) complementary-cell estimate.  All former
continuity, growth, scalar-payment, and contour parameters are absent.  The two
max-cutoff branches are instantiated explicitly, and the upstream
contour inequality is supplied by the unconditional corrected equation-(17)
assembly. -/
theorem chen1973Lemma6_equation20_unconditional_final
    {x L B lastD level k m : ℕ} {ε r : ℝ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (hr : 0 < r)
    (hdom : ∀ t : ℝ, Chen1973Lemma3Domain
      (chen1973Lemma6Beta x + t * I) (chen1973Lemma6Beta x) t)
    (hsphere : ∀ t : ℝ, ∀ z ∈ Metric.sphere (chen1973Lemma6Beta x + t * I) r,
      Chen1973Lemma3Domain z z.re z.im) :
    let H := chen1973Lemma6Equation20H x level k ε
    let D := chen1973Lemma6Eq20SourceD L level
    let Q := chen1973Lemma6Eq20SourceQ L level
    chen1973Lemma6NmBlockActual x L level B k m ≤
      12 * (x : ℝ) * Real.log x ^ 2 *
          chen1973Lemma6Eq20UnconditionalFirstBound x L level B k m H D Q +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
          (chen1973Lemma6Eq20UnconditionalSecondBound x L level B k m H D Q r *
            (x : ℝ) ^ ((1 : ℝ) / 2)) := by
  dsimp
  let H := chen1973Lemma6Equation20H x level k ε
  let D := chen1973Lemma6Eq20SourceD L level
  let Q := chen1973Lemma6Eq20SourceQ L level
  have hHfirst := chen1973Lemma6Equation20H_first_le x level k ε
  have hHsecond := chen1973Lemma6Equation20H_second_le x level k ε
  have hxOne : 1 < x := lt_of_lt_of_le (by omega) P.hx
  have hxNat : 0 < x := lt_trans (by omega) hxOne
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hxNat
  have hfirstPos : 0 < (2 : ℝ) ^ (2 * (level : ℝ) - k) *
      (x : ℝ) ^ (-(13 : ℝ) / 30) * Real.log x ^ 400 *
        chen1973Lemma6Equation20Ilx x level := by
    have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hxOne)
    unfold chen1973Lemma6Equation20Ilx
    positivity
  have hsecondPos : 0 < (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := Real.rpow_pos_of_pos hx0 _
  have hHposR : (0 : ℝ) < H := by
    dsimp [H]
    exact lt_of_lt_of_le (lt_max_of_lt_left hfirstPos) (max_le hHfirst hHsecond)
  have hH : 0 < H := by exact_mod_cast hHposR
  have hD : 0 < D := chen1973Lemma6Eq20SourceD_pos P
  have hQ : 2 ≤ Q := chen1973Lemma6Eq20SourceQ_ge_two P
  have hDQ : D < Q := chen1973Lemma6Eq20SourceD_lt_Q P
  have hIoc : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q :=
    chen1973Lemma6_eq20_conductorBlock_subset_source_Ioc P
  have hIcc : chen1973Lemma6ConductorBlock x L level ⊆ Icc 2 Q :=
    chen1973Lemma6_eq20_conductorBlock_subset_source_Icc P
  have hA := chen1973Lemma6_eq20_first_integral_unconditional
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m)
    (H := H) (D := D) (Q := Q)
    P.hx hH hD hDQ (le_trans (by omega) P.horder_four) hIoc
  have hB := chen1973Lemma6_eq20_second_integral_unconditional
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m)
    (H := H) (D := D) (Q := Q) (r := r)
    P.hx hD hQ hr P.horder_four hIoc hIcc hdom hsphere
  have h17 := chen1973Lemma6_equation17_corrected_radial_unconditional
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m) (H := H)
    P.hx P.hlevel
  unfold chen1973Lemma6Eq17CorrectedRadialFirstIntegral
    chen1973Lemma6Eq17CorrectedRadialSecondIntegral
    chen1973Lemma6Eq17CorrectedRadialKernel at h17
  exact h17.trans (add_le_add
    (mul_le_mul_of_nonneg_left hA (by positivity))
    (mul_le_mul_of_nonneg_left hB (by positivity)))

private theorem eq20_beta_domain {x : ℕ} (hx : 3 ≤ x) (t : ℝ) :
    Chen1973Lemma3Domain (chen1973Lemma6Beta x + t * I)
      (chen1973Lemma6Beta x) t := by
  constructor
  · rfl
  · unfold chen1973Lemma6Beta
    have hl : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hi : 0 < 1 / Real.log (x : ℝ) := one_div_pos.mpr hl
    linarith

private theorem eq20_beta_sphere_domain {x : ℕ} (hx : 3 ≤ x) (v : ℝ)
    {z : ℂ} (hz : z ∈ Metric.sphere (chen1973Lemma6Beta x + v * I) (1 / (2 * Real.log x) : ℝ)) :
    Chen1973Lemma3Domain z z.re z.im := by
  constructor
  · apply Complex.ext <;> simp
  · have hre : |z.re - chen1973Lemma6Beta x| ≤
        ‖z - (chen1973Lemma6Beta x + v * I)‖ := by
      simpa using Complex.abs_re_le_norm (z - (chen1973Lemma6Beta x + v * I))
    have hnorm : ‖z - (chen1973Lemma6Beta x + v * I)‖ =
        (1 / (2 * Real.log x) : ℝ) := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [hnorm] at hre
    have hl : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hrpos : 0 < (1 / (2 * Real.log x) : ℝ) := by positivity
    unfold chen1973Lemma6Beta at hre
    rw [abs_le] at hre
    have heq : 1 / Real.log (x : ℝ) = 2 * (1 / (2 * Real.log x) : ℝ) := by
      field_simp
    rw [heq] at hre
    linarith

/-- Corrected actual equation-(20) budget, with the Cauchy radius and both
beta-domain obligations proved internally. The right-hand side is the explicit
fixed-power budget, not an `x / log(x)^20` estimate. Only the literal source
packet and epsilon are supplied by the caller. -/
theorem chen1973Lemma6_equation20_corrected_actual_budget
    {x L B lastD level k m : ℕ}
    (P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k)
    (ε : ℝ) :
    let H := chen1973Lemma6Equation20H x level k ε
    let D := chen1973Lemma6Eq20SourceD L level
    let Q := chen1973Lemma6Eq20SourceQ L level
    chen1973Lemma6NmBlockActual x L level B k m ≤
      12 * (x : ℝ) * Real.log x ^ 2 *
          chen1973Lemma6Eq20UnconditionalFirstBound x L level B k m H D Q +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
          (chen1973Lemma6Eq20UnconditionalSecondBound x L level B k m H D Q (1 / (2 * Real.log x)) *
            (x : ℝ) ^ ((1 : ℝ) / 2)) := by
  have hx := P.hx
  have hl : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hr : 0 < (1 / (2 * Real.log x) : ℝ) := by positivity
  exact chen1973Lemma6_equation20_unconditional_final (ε := ε) P hr
    (eq20_beta_domain P.hx) (fun t z hz => eq20_beta_sphere_domain P.hx t hz)

end AnalyticNumberTheory.LargeSieve
