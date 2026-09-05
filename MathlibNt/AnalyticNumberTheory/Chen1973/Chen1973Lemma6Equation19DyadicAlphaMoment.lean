import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation14DyadicTail
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19DyadicPairEnergy

noncomputable section
open Classical Complex Finset
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve

/-- Full actual equation-(14) moment: dyadic finite polynomial plus actual PV remainder. -/
theorem chen1973Lemma6_equation14_dyadic_log_power
    (H D Q : ℕ) (s : ℂ) (hH : 2 ≤ H) (hD : 0 < D) (hDQ : D < Q)
    (hs : 1 ≤ s.re) :
    (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2) ≤
      2 * chen1973Lemma6Eq14DyadicConstant *
          ((Q : ℝ) / H + 1 / D) *
          (1 + Real.log (H + 1 : ℕ)) ^ 5 +
        2 * (Q : ℝ) *
          ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
            (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
              (1 + Real.log H)) ^ 2 := by
  have hHpos : 0 < H := by omega
  let F : (d : ℕ) → PrimitiveCharacter d → ℂ := fun d χ =>
    ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
      chen1973Lemma6CHWeightedCoefficient H s m * χ.1 (m : ZMod d)
  let R : (d : ℕ) → PrimitiveCharacter d → ℂ := fun d χ =>
    (chen1973PrimitiveLValue d s χ -
      chen1973Lemma6NaturalLPolynomial H s χ) *
        chen1973Lemma6NaturalMobiusPolynomial H s χ
  have hp (d : ℕ) (χ : PrimitiveCharacter d) :
      ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2 ≤
        2 * ‖F d χ‖ ^ 2 + 2 * ‖R d χ‖ ^ 2 := by
    rw [chen1973Lemma6_oneSubLS_eq_CH_sub_remainder hHpos]
    change ‖F d χ - R d χ‖ ^ 2 ≤ _
    have hn := norm_sub_le (F d χ) (R d χ)
    have hsquare : ‖F d χ - R d χ‖ ^ 2 ≤
        (‖F d χ‖ + ‖R d χ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖F d χ‖ - ‖R d χ‖)]
  have hfinite := chen1973Lemma6_CH_polynomial_moment_fixed_log_five H D Q s hH hD hs
  have hR := chen1973Lemma6_equation14_remainderMoment_final_scalar
    H D Q s hHpos hD hDQ hs
  calc
    _ ≤ ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          (2 * ‖F d χ‖ ^ 2 + 2 * ‖R d χ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ hχ => hp d χ) (by positivity)
    _ = 2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖F d χ‖ ^ 2) +
        2 * chen1973Lemma6Equation14RemainderMoment H D Q s := by
      change _ = 2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖F d χ‖ ^ 2) +
        2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖R d χ‖ ^ 2)
      simp_rw [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      have hmul (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
      simp_rw [hmul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (chen1973Lemma6Eq14DyadicConstant *
        ((Q : ℝ) / H + 1 / D) * (1 + Real.log (H + 1 : ℕ)) ^ 5) +
        2 * ((Q : ℝ) * ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re))) * (1 + Real.log H)) ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [F] using hfinite) (by norm_num))
        (mul_le_mul_of_nonneg_left hR (by norm_num))
    _ = _ := by ring

/-- Transport the complete dyadic alpha moment to the actual conductor weights. -/
theorem chen1973Lemma6_eq19_oneSub_second_moment_dyadic
    (x L level H D Q : ℕ) (s : ℂ) (hH : 2 ≤ H) (hD : 0 < D)
    (hDQ : D < Q) (hs : 1 ≤ s.re)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq19OneSubSecondMoment x L level H s ≤
      chen1973Lemma6Eq19I x L level *
        (2 * chen1973Lemma6Eq14DyadicConstant *
            ((Q : ℝ) / H + 1 / D) *
            (1 + Real.log (H + 1 : ℕ)) ^ 5 +
          2 * (Q : ℝ) *
            ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
              (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
                (1 + Real.log H)) ^ 2) := by
  unfold chen1973Lemma6Eq19OneSubSecondMoment
  change (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
      chen1973Lemma6Eq19Weight d *
        ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2) ≤ _
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (1 / (d.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2 := by
      apply chen1973Lemma6_eq19_weight_transport
      intro d
      positivity
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hcell
        intro d hd hdnot
        positivity
      · exact (chen1973Lemma6Eq19I_pos x L level).le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (chen1973Lemma6_equation14_dyadic_log_power H D Q s hH hD hDQ hs)
      (chen1973Lemma6Eq19I_pos x L level).le

/-- Explicit complete alpha-moment budget; both summands are proved above. -/
def chen1973Lemma6Eq14DyadicBudget (H D Q : ℕ) (s : ℂ) : ℝ :=
  2 * chen1973Lemma6Eq14DyadicConstant * ((Q : ℝ) / H + 1 / D) *
      (1 + Real.log (H + 1 : ℕ)) ^ 5 +
    2 * (Q : ℝ) * ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
      (((H + 1 : ℕ) : ℝ) ^ (-s.re))) * (1 + Real.log H)) ^ 2

/-- The actual alpha numerator now consumes both genuinely dyadic producers.
No `x²` pair interval and no `H²/D` finite-polynomial loss remains. -/
theorem chen1973Lemma6_eq19_A_le_dyadic_moments
    (x L level B k m H D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (σ v : ℝ) (hσ : 1 ≤ σ) (hH : 2 ≤ H) (hD : 0 < D) (hDQ : D < Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6A x L level B k m H (σ + v * I) ≤
      Real.sqrt (9 * chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level /
        Real.log x ^ 2 * ((Q : ℝ) + ((B * 2 ^ k : ℕ) : ℝ) / D) *
          ((B * 2 ^ k : ℕ) : ℝ) ^ (1 - 2 * σ)) *
      Real.sqrt (chen1973Lemma6Eq19I x L level *
        chen1973Lemma6Eq14DyadicBudget H D Q (σ + v * I)) := by
  have hp := chen1973Lemma6_eq19_dyadic_pair_second_moment_scalar
    x L level B k m D Q hx hB σ v (by linarith) hD hcell
  have ho := chen1973Lemma6_eq19_oneSub_second_moment_dyadic
    x L level H D Q (σ + v * I) hH hD hDQ (by simpa using hσ) hcell
  have ha := chen1973Lemma6A_le_moment_product x L level B k m H (σ + v * I)
  change chen1973Lemma6A x L level B k m H (σ + v * I) ≤
    Real.sqrt (chen1973Lemma6Eq19PairSecondMoment x L level B k m (σ + v * I)) *
    Real.sqrt (chen1973Lemma6Eq19OneSubSecondMoment x L level H (σ + v * I)) at ha
  exact ha.trans (mul_le_mul (Real.sqrt_le_sqrt hp) (Real.sqrt_le_sqrt ho)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end AnalyticNumberTheory.LargeSieve
