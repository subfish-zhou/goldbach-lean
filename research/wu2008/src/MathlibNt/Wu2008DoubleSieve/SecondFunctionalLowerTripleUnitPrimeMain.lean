import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitPrimeFinite

namespace Wu2008DoubleSieve.LowerTripleGroupedUnit
open Finset Real LiLiuPrereqBuchstab LowerTripleGroupedFinite
open scoped Classical

/-- The actual two-endpoint model, not an upper-prefix majorant. -/
noncomputable def intervalMain (L U : ℝ) : ℝ :=
  if L ≤ U then U/log U - L/log L else 0

/-- Every endpoint is compared to the same full pair error scale. -/
theorem endpoint_model_le {N η z X : ℝ} (hN : 1 < N) (hη : 0 < η)
    (hz : N^η ≤ z) (hzX : z ≤ X) : z/log z ≤ X/(η*log N) := by
  have hpow : 1 < N^η := one_lt_rpow hN hη
  have hz1 : 1 < z := hpow.trans_le hz
  have hlog : η*log N ≤ log z := by
    rw [← log_rpow (by linarith : 0 < N)]
    exact log_le_log (by positivity) hz
  have hbase : 0 < η*log N := mul_pos hη (log_pos hN)
  exact (div_le_div_of_nonneg_left (by linarith) hbase hlog).trans
    (div_le_div_of_nonneg_right hzX hbase.le)

/-- PNT is consumed at both moving closed-prefix endpoints, with tau/2 internally. -/
theorem interval_uniform_upper {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ L U X : ℝ,
      (N : ℝ)^η ≤ L → U ≤ X → 0 ≤ X →
      prefixDifference L U ≤ intervalMain L U + τ*(X/(η*log N)) := by
  obtain ⟨R0,hR0,hpnt⟩ := secondFunctional_primePrefix_threshold η hη (τ/2) (by positivity)
  refine ⟨max 4 ⌈R0⌉₊,le_max_left _ _,?_⟩
  intro N hN L U X hL hUX hX
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNR : R0 ≤ (N : ℝ) := (Nat.le_ceil R0).trans (by exact_mod_cast (le_max_right 4 ⌈R0⌉₊).trans hN)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 ≤ X/(η*log N) := div_nonneg hX (mul_pos hη (log_pos hN1)).le
  by_cases h : L ≤ U
  · have hU := hL.trans h
    have hP := hpnt N hNR U hU
    have hQ := hpnt N hNR L hL
    have hmU := endpoint_model_le hN1 hη hU hUX
    have hmL := endpoint_model_le hN1 hη hL (h.trans hUX)
    have heU := (abs_le.mp hP).2
    have heL := (abs_le.mp hQ).1
    have hcU := mul_le_mul_of_nonneg_left hmU (show 0 ≤ τ/2 by positivity)
    have hcL := mul_le_mul_of_nonneg_left hmL (show 0 ≤ τ/2 by positivity)
    simp only [prefixDifference,intervalMain,if_pos h]
    linarith
  · simp only [prefixDifference,intervalMain,if_neg h,zero_add]
    exact mul_nonneg hτ.le hscale

noncomputable def unitPrimeMain {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ x ∈ actualPairs N δ P j d,
      intervalMain (actualLower N δ P j d x) (actualUpper N δ P j d x)

/-- Full original sigma and pair support, without a nonunit feasibility gate. -/
noncomputable def unitPrimeError {i : ℕ} (N : ℕ) (η δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ x ∈ actualPairs N δ P j d, ((N : ℝ)/denominator d x)/(η*log N)

/-- Tau precedes the common threshold; all boxes, parameters and six bands follow it. -/
theorem unitMass_prime_main (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ P : SecondFunctionalParameters, P.MotherAdmissible → ∀ j : Fin 6,
        unitMass N δ Δ V P j ≤ unitPrimeMain N δ Δ V P j +
          τ*unitPrimeError N (wuLocalExponent k δ/10) δ Δ V P j := by
  have hη : 0 < wuLocalExponent k δ/10 := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T,hT,hscalar⟩ := interval_uniform_upper hη hτ
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb P hP j
  have hterm : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ x ∈ actualPairs N δ P j d,
      prefixDifference (actualLower N δ P j d x) (actualUpper N δ P j d x) ≤
        intervalMain (actualLower N δ P j d x) (actualUpper N δ P j d x) +
        τ*(((N : ℝ)/denominator d x)/((wuLocalExponent k δ/10)*log N)) := by
    intro d hd x hx
    have hdp := boxConvolutionSupport_pos
      (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd
    have hD : 0 < denominator d x := denominator_pos hdp hx
    have hq := (HighNonunit.mother_window_lower (by omega : 2 ≤ N) hδ hδhi hb P hP hd
      (mem_pairs.mp hx).2.1).2
    apply hscalar N hN
    · exact hq.trans (le_max_left _ _)
    · exact min_le_right _ _
    · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hD.le)
  rw [unitMass_pair_prefix]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ∑ x ∈ actualPairs N δ P j d,
          (intervalMain (actualLower N δ P j d x) (actualUpper N δ P j d x) +
            τ*(((N : ℝ)/denominator d x)/((wuLocalExponent k δ/10)*log N))) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (sum_le_sum (hterm d hd)) (Nat.cast_nonneg _)
    _ = _ := by
      unfold unitPrimeMain unitPrimeError
      simp only [sum_add_distrib,← mul_sum,mul_add,mul_left_comm]

/-- All six original bands, with one tau on their complete summed error. -/
theorem unitMass_six_prime_main (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ P : SecondFunctionalParameters, P.MotherAdmissible →
        (∑ j : Fin 6, unitMass N δ Δ V P j) ≤
          (∑ j : Fin 6, unitPrimeMain N δ Δ V P j) +
            τ*∑ j : Fin 6, unitPrimeError N (wuLocalExponent k δ/10) δ Δ V P j := by
  obtain ⟨T,hT,h⟩ := unitMass_prime_main k hδ hδhi hτ
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb P hP
  simpa only [sum_add_distrib,← mul_sum] using
    sum_le_sum (s := (univ : Finset (Fin 6))) (fun j _ => h N hN i Δ V hb P hP j)

end Wu2008DoubleSieve.LowerTripleGroupedUnit
