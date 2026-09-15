import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceIntegral
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitLogCaps

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSource
open HighUnit

/-- Explicit unit corrections; these do not redefine the original I integrals. -/
noncomputable def unitLogCap20 (a2 a b : ℝ) : ℝ :=
  Real.log (a/a2) * Real.log (b/a)^3 / (24*a)
noncomputable def unitLogCap21 (a b : ℝ) : ℝ := Real.log (b/a)^5 / (720*a)

/-- Original same-sigma logarithmic mass, before any sieve-density payment. -/
noncomputable def unitLogMass {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) /
      ((d : ℝ) * Real.log ((N : ℝ) ^ (1/2-δ) / d))

/-- Both J main sums are bounded using the same actual phi and unchanged weights. -/
theorem boxed_integral_pair_log_cap {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hbox : wuSourceBox k δ N i Δ V) {a2 a b : ℝ}
    (ha : 1/10 ≤ a2) (haa : a2 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/2) :
    let W := convolutionWuWindows N Δ V
    boxedIntegral20 N δ W (fun _ => a2) (fun _ => a) (fun _ => b) +
      boxedIntegral21 N δ W (fun _ => a) (fun _ => b) ≤
    (unitLogCap20 a2 a b + unitLogCap21 a b) * unitLogMass N δ W := by
  dsimp only
  unfold boxedIntegral20 boxedIntegral21 unitLogMass
  rw [← mul_add, ← Finset.sum_add_distrib]
  calc
    _ ≤ (N : ℝ) * ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) /
          ((d : ℝ) * Real.log ((N : ℝ) ^ (1/2-δ) / d))) *
            (unitLogCap20 a2 a b + unitLogCap21 a b) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro d hd
      have hR := (omega3XPhi_source_bounds hN hδ hδhi hbox hd).2.1
      have hw : 0 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) /
          ((d : ℝ) * Real.log ((N : ℝ) ^ (1/2-δ) / d)) :=
        div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg d) (Real.log_pos hR).le)
      have hc := add_le_add (J20_log_cap ha haa hab hb (omega3XPhi N d δ))
        (J21_log_cap (ha.trans haa) hab hb (omega3XPhi N d δ))
      simpa only [unitLogCap20, unitLogCap21, mul_add] using
        mul_le_mul_of_nonneg_left hc hw
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Mother parameters supply all compact order conditions needed by the actual J caps. -/
theorem parameter_log_cap_bounds {p : SecondFunctionalParameters}
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    1/10 ≤ 1/p.kappa2 ∧ 1/p.kappa2 ≤ 1/p.kappa3 ∧
      1/p.kappa3 ≤ 1/p.s ∧ 1/p.s ≤ 1/2 := by
  have h3 : 0 < p.kappa3 := by linarith [hp.s_le_kappa3]
  exact ⟨(parameter_outer_bounds hp hs).1,
    one_div_le_one_div_of_le h3 hp.kappa3_lt_kappa2.le,
    one_div_le_one_div_of_le (by linarith) hp.s_le_kappa3,
    (parameter_outer_bounds hp hs).2.2⟩

/-- The correction in the original five-parameter notation, with exact algebra. -/
theorem unitLogCap_parameters (p : SecondFunctionalParameters) :
    unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) =
      p.kappa3 / 24 * Real.log (p.kappa2/p.kappa3) * Real.log (p.kappa3/p.s)^3 ∧
    unitLogCap21 (1/p.kappa3) (1/p.s) =
      p.kappa3 / 720 * Real.log (p.kappa3/p.s)^5 := by
  simp [unitLogCap20, unitLogCap21, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Literal unit sources with explicit corrections, retaining the original common threshold.
The error is on N/log N reciprocal mass, not Theta; no sieve density is asserted. -/
theorem mother_unit_pair_log_cap (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let a0 := fun d => wuLocalCutoff N δ d p.S
      let a1 := fun d => wuLocalCutoff N δ d p.kappa1
      let a2 := fun d => wuLocalCutoff N δ d p.kappa2
      let a3 := fun d => wuLocalCutoff N δ d p.kappa3
      let b := fun d => wuLocalCutoff N δ d p.s
      FourPrimeUnit.source N W a0 a1 a2 a3 b word20 +
        FourPrimeUnit.source N W a0 a1 a2 a3 b word21 ≤
      (unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
        unitLogCap21 (1/p.kappa3) (1/p.s)) * unitLogMass N δ W +
        epsilon * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T,hT4,hT⟩ := mother_unit_pair_integral k hδ hδhi he
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hbox p hp hs
  obtain ⟨ha,haa,hab,hb⟩ := parameter_log_cap_bounds hp hs
  have hc := boxed_integral_pair_log_cap (by omega) hδ hδhi hbox ha haa hab hb
  have hu := hT N hN i Δ V hbox p hp hs
  dsimp only at hc hu ⊢
  exact hu.trans (by linarith [hc])

end Wu2008DoubleSieve.HighUnitSource
