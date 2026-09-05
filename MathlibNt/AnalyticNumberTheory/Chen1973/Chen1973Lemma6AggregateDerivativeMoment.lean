import MathlibNt.AnalyticNumberTheory.LargeSieve.AggregateCauchyFourthMoment
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma3WeightedFourthMoment
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19MomentTransport

noncomputable section
open Complex Finset
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

lemma totient_block_sum_le_weighted (D Q : ℕ) (hD : 0 < D)
    (A : ℕ → ℝ) (hA : ∀ q, 0 ≤ A q) :
    (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) * A q) ≤
      (∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * A q) / D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  apply (le_div_iff₀ hDr).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ q ∈ Ioc D Q, ((q : ℝ) / q.totient) * A q := by
      apply Finset.sum_le_sum
      intro q hq
      have hDq : (D : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Ioc.mp hq).1.le
      calc
        _ = ((D : ℝ) / q.totient) * A q := by ring
        _ ≤ _ := by gcongr; exact hA q
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have := Finset.mem_Ioc.mp hq
        exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
      · intro q hq hn
        exact mul_nonneg (by positivity) (hA q)

lemma primitiveLValue_differentiable (q : ℕ) (χ : PrimitiveCharacter q) :
    Differentiable ℂ (fun z => chen1973PrimitiveLValue q z χ) := by
  by_cases hq : 1 < q
  · letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
    simpa only [chen1973PrimitiveLValue, dif_pos hq] using
      χ.1.differentiable_LFunction (chen1973_primitive_ne_one hq χ)
  · simp only [chen1973PrimitiveLValue, dif_neg hq]
    exact differentiable_const _

lemma primitiveLValue_deriv (q : ℕ) (χ : PrimitiveCharacter q) (s : ℂ) :
    deriv (fun z => chen1973PrimitiveLValue q z χ) s = chen1973PrimitiveLDeriv q s χ := by
  by_cases hq : 1 < q
  · simp only [chen1973PrimitiveLValue, chen1973PrimitiveLDeriv, dif_pos hq]
  · simp only [chen1973PrimitiveLValue, chen1973PrimitiveLDeriv, dif_neg hq, deriv_const]

/-- Actual primitive L-functions: the reciprocal-totient block fourth moment
on a circle is controlled before applying Cauchy to the whole finite ℓ⁴ family. -/
theorem primitive_LDeriv_fourth_block_cauchy
    (D Q : ℕ) (s : ℂ) (r M : ℝ) (hD : 0 < D) (hQ : 2 ≤ Q)
    (hr : 0 < r)
    (hsphere : ∀ z ∈ Metric.sphere s r, Chen1973Lemma3Domain z z.re z.im)
    (hnorm : ∀ z ∈ Metric.sphere s r, ‖z‖ ≤ M) :
    (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q,
      ‖chen1973PrimitiveLDeriv q s χ‖ ^ 4) ≤
      (21000000 * (Q : ℝ) ^ 2 * M ^ 2 *
        (1 + Real.log ((Q : ℝ) * (1 + M))) ^ 4) / D / r ^ 4 := by
  let J := (q : {q : ℕ // q ∈ Ioc D Q}) × PrimitiveCharacter q.1
  let F : J → ℂ → ℂ := fun j z => chen1973PrimitiveLValue j.1.1 z j.2
  let w : J → ℝ := fun j => 1 / (j.1.1.totient : ℝ)
  let B : ℝ := (21000000 * (Q : ℝ) ^ 2 * M ^ 2 *
    (1 + Real.log ((Q : ℝ) * (1 + M))) ^ 4) / D
  have hflatten (G : (q : ℕ) → PrimitiveCharacter q → ℝ) :
      (∑ j : J, w j * G j.1.1 j.2) =
        ∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q, G q χ := by
    rw [Fintype.sum_sigma]
    simp only [w, ← Finset.mul_sum]
    exact (Finset.sum_subtype (Ioc D Q) (fun _ => Iff.rfl)
      (fun q => (1 / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q, G q χ)).symm
  have hcircle : ∀ z ∈ Metric.sphere s r, ∑ j : J, w j * ‖F j z‖ ^ 4 ≤ B := by
    intro z hz
    have hbound := primitiveWeightedFourthMoment_corrected_endpoint
      (chen1973Lemma2_equationTwo_of_fareyEquationFour chen1973FareyEquationFour)
      z hQ (hsphere z hz)
    have hblock := totient_block_sum_le_weighted D Q hD
      (fun q => ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveLValue q z χ‖ ^ 4)
      (fun q => Finset.sum_nonneg fun χ hχ => by positivity)
    have hlog0 : 0 ≤ Real.log ((Q : ℝ) * (1 + ‖z‖)) := by
      apply Real.log_nonneg
      have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
      nlinarith [norm_nonneg z]
    have hlog : Real.log ((Q : ℝ) * (1 + ‖z‖)) ≤
        1 + Real.log ((Q : ℝ) * (1 + M)) := by
      have hm := Real.log_le_log (by positivity : 0 < (Q : ℝ) * (1 + ‖z‖))
        (show (Q : ℝ) * (1 + ‖z‖) ≤ (Q : ℝ) * (1 + M) by gcongr; exact hnorm z hz)
      linarith
    have hfinal : (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q,
        ‖chen1973PrimitiveLValue q z χ‖ ^ 4) ≤ B := by
      calc
        _ ≤ primitiveWeightedFourthMoment Q z / D := hblock
        _ ≤ (21000000 * (Q : ℝ) ^ 2 * ‖z‖ ^ 2 *
            Real.log ((Q : ℝ) * (1 + ‖z‖)) ^ 4) / D := by gcongr
        _ ≤ B := by
          dsimp [B]
          gcongr
          exact hnorm z hz
    change (∑ j : J, w j * ‖chen1973PrimitiveLValue j.1.1 z j.2‖ ^ 4) ≤ B
    rw [hflatten (fun q χ => ‖chen1973PrimitiveLValue q z χ‖ ^ 4)]
    exact hfinal
  have h := aggregate_weighted_cauchy_fourth F w (fun j => by dsimp [w]; positivity)
    s r B hr (by dsimp [B]; positivity)
    (fun j => primitiveLValue_differentiable j.1.1 j.2) hcircle
  simp only [F, primitiveLValue_deriv] at h
  rw [hflatten (fun q χ => ‖chen1973PrimitiveLDeriv q s χ‖ ^ 4)] at h
  exact h

/-- All heights, with the circle hypotheses derived from the actual band.
The conductor cost is `Q²/D`, not an extra count of individual characters. -/
theorem primitive_LDeriv_fourth_block_vertical
    (D Q : ℕ) (σ t r : ℝ) (hD : 0 < D) (hQ : 2 ≤ Q)
    (hr : 0 < r) (hband : (1 : ℝ) / 2 ≤ σ - r) :
    (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q,
      ‖chen1973PrimitiveLDeriv q (σ + t * I) χ‖ ^ 4) ≤
      (21000000 * (Q : ℝ) ^ 2 * (|σ| + |t| + r) ^ 2 *
        (1 + Real.log ((Q : ℝ) * (1 + (|σ| + |t| + r)))) ^ 4) / D / r ^ 4 := by
  apply primitive_LDeriv_fourth_block_cauchy D Q (σ + t * I) r
    (|σ| + |t| + r) hD hQ hr
  · intro z hz
    refine ⟨by apply Complex.ext <;> simp, ?_⟩
    have hnorm : ‖z - (σ + t * I)‖ = r := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hre := Complex.abs_re_le_norm (z - (σ + t * I))
    have hre' : |z.re - σ| ≤ r := by simpa [hnorm] using hre
    have hlo := (abs_le.mp hre').1
    linarith
  · intro z hz
    have hnorm : ‖z - (σ + t * I)‖ = r := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hc : ‖(σ : ℂ) + t * I‖ ≤ |σ| + |t| := by
      calc
        _ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = _ := by simp
    calc
      ‖z‖ = ‖(z - (σ + t * I)) + (σ + t * I)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (σ + t * I)‖ + ‖(σ : ℂ) + t * I‖ := norm_add_le _ _
      _ ≤ r + (|σ| + |t|) := by rw [hnorm]; exact add_le_add le_rfl hc
      _ = _ := by ring

/-- Actual equation-(19) conductor weights applied only after the aggregate
reciprocal-totient bound. The logarithm is kept, not enlarged to a conductor power. -/
theorem chen1973Lemma6_eq19_LDeriv_fourth_aggregate
    (x L level D Q : ℕ) (σ t r : ℝ) (hD : 0 < D) (hQ : 2 ≤ Q)
    (hr : 0 < r) (hband : (1 : ℝ) / 2 ≤ σ - r)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq19LDerivFourthMoment x L level (σ + t * I) ≤
      chen1973Lemma6Eq19I x L level *
        ((21000000 * (Q : ℝ) ^ 2 * (|σ| + |t| + r) ^ 2 *
          (1 + Real.log ((Q : ℝ) * (1 + (|σ| + |t| + r)))) ^ 4) / D / r ^ 4) := by
  let F : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    ‖chen1973PrimitiveLDeriv d (σ + t * I) χ‖ ^ 4
  have hF : ∀ d, 0 ≤ F d := fun d => Finset.sum_nonneg fun χ hχ => by positivity
  have hw := chen1973Lemma6_eq19_weight_transport (x := x) (L := L) (level := level) F hF
  change chen1973Lemma6Eq19LDerivFourthMoment x L level (σ + t * I) ≤ _ at hw
  apply hw.trans
  apply mul_le_mul_of_nonneg_left _ (chen1973Lemma6Eq19I_pos x L level).le
  calc
    _ ≤ ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) * F d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hcell
      intro d hd hnot
      exact mul_nonneg (by positivity) (hF d)
    _ ≤ _ := primitive_LDeriv_fourth_block_vertical D Q σ t r hD hQ hr hband

/-- Chen's actual beta line, with the Cauchy radius and band paid internally. -/
theorem chen1973Lemma6_eq19_LDeriv_fourth_beta
    (x L level D Q : ℕ) (hx : 3 ≤ x) (hD : 0 < D) (hQ : 2 ≤ Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) (t : ℝ) :
    let β := chen1973Lemma6Beta x
    let r : ℝ := 1 / (2 * Real.log (x : ℝ))
    chen1973Lemma6Eq19LDerivFourthMoment x L level (β + t * I) ≤
      chen1973Lemma6Eq19I x L level *
        ((21000000 * (Q : ℝ) ^ 2 * (|β| + |t| + r) ^ 2 *
          (1 + Real.log ((Q : ℝ) * (1 + (|β| + |t| + r)))) ^ 4) / D / r ^ 4) := by
  dsimp only
  have hl : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hr : 0 < (1 / (2 * Real.log (x : ℝ)) : ℝ) := by positivity
  apply chen1973Lemma6_eq19_LDeriv_fourth_aggregate x L level D Q
    (chen1973Lemma6Beta x) t (1 / (2 * Real.log (x : ℝ))) hD hQ hr _ hcell
  unfold chen1973Lemma6Beta
  have heq : 1 / Real.log (x : ℝ) = 2 * (1 / (2 * Real.log (x : ℝ))) := by field_simp
  linarith

end AnalyticNumberTheory.LargeSieve
