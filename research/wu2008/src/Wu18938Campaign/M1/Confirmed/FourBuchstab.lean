import Wu18938Campaign.M1.Confirmed.FourPurification
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeFiniteErrorPayment

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Four

open Wu2008DoubleSieve FourPrimeNonunit Finset Real LiLiuPrereqBuchstab
open scoped Classical

theorem mass_scalar (m : ℕ) {η δ τ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (roughFamily N δ Δ V p j).mass ≤
        finiteBuchstabMain N δ Δ V p j + τ * finiteErrorMass N δ Δ V p j := by
  obtain ⟨T,hT,hscalar⟩ := NonunitRoughUniform.uniform_upper
    (show 0 < η / 10 by positivity) hτ
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j
  let W := convolutionWuWindows N Δ V
  have hterm : ∀ d ∈ boxConvolutionSupport W,
      ∀ t ∈ actualPrimeTuples N δ p j d,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.1).erase 1).card : ℝ) ≤
      if tupleProduct d t * t.1 ≤ N then
        (buchstab (log ((N : ℝ)/tupleProduct d t)/log t.1)+τ) *
          ((N : ℝ)/tupleProduct d t)/log t.1 else 0 := by
    intro d hd t ht
    have hD := tupleProduct_pos (hb.support_pos hd) ht
    have hD1 : (1 : ℝ) ≤ tupleProduct d t := by exact_mod_cast hD
    have hx : (N : ℝ)/tupleProduct d t ≤ N := div_le_self (Nat.cast_nonneg N) hD1
    have hy := (hb.mother_window_large (by omega) hη hδ p hp hd (mem_primeTuples.mp ht).1).2
    obtain ⟨hz,hu⟩ := hscalar N hN _ _ hx hy
    by_cases hg : tupleProduct d t * t.1 ≤ N
    · rw [if_pos hg]
      exact hu ((legal_gate_iff N d t hD).mp hg)
    · rw [if_neg hg, hz (lt_of_not_ge (fun h => hg ((legal_gate_iff N d t hD).mpr h)))]
      norm_num
  rw [rough_mass_tuple_dictionary]
  change (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ t ∈ actualPrimeTuples N δ p j d,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.1).erase 1).card : ℝ)) ≤ _
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ t ∈ actualPrimeTuples N δ p j d,
          if tupleProduct d t * t.1 ≤ N then
            (buchstab (log ((N : ℝ)/tupleProduct d t)/log t.1)+τ) *
              ((N : ℝ)/tupleProduct d t)/log t.1 else 0 := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (sum_le_sum (hterm d hd)) (Nat.cast_nonneg _)
    _ = _ := by
      unfold finiteBuchstabMain finiteErrorMass legalPrimeTuples
      simp only [sum_filter, mul_sum, Finset.mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro t _
      split_ifs <;> ring

theorem tuple_cube {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {j : Fin 4} {t : PrimeTuple} (ht : t ∈ actualPrimeTuples N δ p j d) :
    ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d) := by
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hR := (hb.support_geometry hN hη hδ hd).2.2.1
  have hS : 0 < p.S := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (hp.one_le_s.trans (hp.s_le_kappa3.trans (hp.kappa3_lt_kappa2.le.trans
      (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hlo : R ^ (1 / 10 : ℝ) ≤ wuLocalCutoff N δ d p.S :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le hS hp.S_le_ten)
  have hhi : wuLocalCutoff N δ d p.s ≤ R ^ (1 / 2 : ℝ) :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (by norm_num) hs)
  obtain ⟨h3,h2,h1,_,_,hq⟩ := mem_primeTuples.mp ht
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hh.1,hlo.trans hh.2.2.1,hh.2.2.2.le.trans hhi⟩
  have hupper : lastUpper (fun d => wuLocalCutoff N δ d p.kappa3)
      (fun d => wuLocalCutoff N δ d p.s) (FourPrimeUnit.word j) d ≤ R ^ (1 / 2 : ℝ) := by
    unfold lastUpper
    split_ifs
    · exact rpow_le_rpow_of_exponent_le hR.le
        (one_div_le_one_div_of_le (by norm_num) (hs.trans hp.s_le_kappa3))
    · exact hhi
  intro r hr
  simp only [tupleList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw _ h1
  · exact hw _ h2
  · exact hw _ h3
  · exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hq.1,hlo.trans ((mem_primeWindow.mp h3).2.2.1.trans
        (by exact_mod_cast hq.2.1.le)),hq.2.2.2.trans hupper⟩

theorem finite_error {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 4)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d), 1 / (q : ℝ)) ≤ 5) :
    finiteErrorMass N δ Δ V p j ≤
      5 ^ 4 / (η / 10) * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have hη' : 0 < η / 10 := by positivity
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ t ∈ legalPrimeTuples N δ p j d, ((N : ℝ) / tupleProduct d t) / log t.1) ≤
      ((N : ℝ) / d) / ((η / 10) * log N) * 5 ^ 4 := by
    have hrec := tuple_reciprocal_le (legalPrimeTuples N δ p j d)
      (fun t ht => tuple_cube hb (by omega) hη hδ p hp hs hd (mem_filter.mp ht).1) (hmass d hd)
    calc
      _ ≤ ∑ t ∈ legalPrimeTuples N δ p j d,
          (((N : ℝ) / d) / ((η / 10) * log N)) * (1 / ((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have hp' := hb.mother_window_large (by omega) hη hδ p hp hd
          (mem_primeTuples.mp (mem_filter.mp ht).1).1
        have hy := log_le_log (rpow_pos_of_pos (by positivity : (0 : ℝ) < N) (η / 10)) hp'.2
        rw [log_rpow (by positivity : (0 : ℝ) < N)] at hy
        have heq : ((N : ℝ) / tupleProduct d t) / log t.1 =
            ((N : ℝ) / d) * (1 / ((tupleList t).prod : ℝ)) / log t.1 := by
          simp only [tupleProduct_literal, Nat.cast_mul]
          ring
        rw [heq]
        calc
          _ ≤ ((N : ℝ) / d) * (1 / ((tupleList t).prod : ℝ)) / ((η / 10) * log N) :=
            div_le_div_of_nonneg_left (by positivity) (mul_pos hη' hlogN) hy
          _ = _ := by ring
      _ = (((N : ℝ) / d) / ((η / 10) * log N)) *
          (∑ t ∈ legalPrimeTuples N δ p j d, 1 / ((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold finiteErrorMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      (((N : ℝ) / d) / ((η / 10) * log N) * 5 ^ 4) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem mass_paid (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 4,
      (roughFamily N δ Δ V p j).mass ≤ finiteBuchstabMain N δ Δ V p j +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let C : ℝ := 5 ^ 4 / (η / 10)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T0, hT04, ht⟩ := mass_scalar m hη hδ (show 0 < ε / C by positivity)
  obtain ⟨T1, _, hm⟩ := roughBox_cube_mass m (δ := δ) hη
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp hs j
  have h0 := ht N (by omega) i Δ V hb p hp j
  have h1 := mul_le_mul_of_nonneg_left
    (finite_error hb (by omega) hη hδ p hp hs j (hm N (by omega) i Δ V hb))
    (show 0 ≤ ε / C by positivity)
  have hcancel : (ε / C) * (C * ((N : ℝ) / log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) =
      ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    field_simp
  rw [hcancel] at h1
  linarith only [h0, h1]

theorem finite_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).primeMass ≤ finiteBuchstabMain N δ Δ V p j *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let A := (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith) (by positivity))
    (div_pos (by norm_num) (by linarith))
  obtain ⟨T0,hT04,h0⟩ := rough_density m hη hδ hδhi hρ (half_pos he)
  obtain ⟨T1,_,h1⟩ := mass_paid m hη hδ (div_pos he hA)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb p hp hs j
  have hN4 : 4 ≤ N := by omega
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hd := h0 N (by omega) heven i Δ V hb p hp j
  have hr := h1 N (by omega) i Δ V hb p hp hs j
  have ht := mul_le_mul_of_nonneg_left (roughBox_reciprocal_theta hb hN4 hη hδ) he.le
  have hh := mul_le_mul_of_nonneg_right hr (mul_nonneg hA.le hC)
  simp only [add_mul] at hh
  have hcancel : ((ε / A) * ((N : ℝ) / log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) *
      (A * (wuSingularSeries N / log N)) =
      ε * (wuSingularSeries N / log N * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by field_simp
  rw [hcancel] at hh
  rw [mul_div_assoc] at hd ⊢
  linarith only [hd, hh, ht]

end Wu18938Campaign.M1.Confirmed.Four
