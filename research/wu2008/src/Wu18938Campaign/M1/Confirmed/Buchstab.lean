import Wu18938Campaign.M1.Confirmed.Purification
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteErrorPayment
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem roughBox_rough_mass_scalar (m : ℕ) {η δ τ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      (roughFamily N δ Δ V p high).mass ≤
        finiteBuchstabMain N δ Δ V p high + τ * finiteErrorMass N δ Δ V p high := by
  obtain ⟨T, hT4, hscalar⟩ :=
    NonunitRoughUniform.uniform_upper (show 0 < η / 10 by positivity) hτ
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp high
  let W := convolutionWuWindows N Δ V
  have hterm (d : ℕ) (hd : d ∈ boxConvolutionSupport W)
      (t : PrimeTuple) (ht : t ∈ actualPrimeTuples N δ p high d) :
      (((roughNumbers ((N : ℝ) / tupleProduct d t) t.2.1).erase 1).card : ℝ) ≤
        if tupleProduct d t * t.2.1 ≤ N then
          (buchstab (log ((N : ℝ) / tupleProduct d t) / log t.2.1) + τ) *
            ((N : ℝ) / tupleProduct d t) / log t.2.1 else 0 := by
    have hD := tupleProduct_pos (hb.support_pos hd) ht
    have hx : (N : ℝ) / tupleProduct d t ≤ N :=
      div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hD)
    have hy := (hb.mother_window_large (by omega) hη hδ p hp hd
      (mem_primeTuples.mp ht).2.1).2
    obtain ⟨hz, hu⟩ := hscalar N hN _ _ hx hy
    by_cases hg : tupleProduct d t * t.2.1 ≤ N
    · rw [if_pos hg]
      exact hu ((legal_gate_iff N d t hD).mp hg)
    · rw [if_neg hg, hz (lt_of_not_ge (fun h => hg ((legal_gate_iff N d t hD).mpr h)))]
      norm_num
  rw [roughFamily_mass_dictionary]
  change (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ t ∈ actualPrimeTuples N δ p high d,
      (((roughNumbers ((N : ℝ) / tupleProduct d t) t.2.1).erase 1).card : ℝ)) ≤ _
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ t ∈ actualPrimeTuples N δ p high d,
          if tupleProduct d t * t.2.1 ≤ N then
            (buchstab (log ((N : ℝ) / tupleProduct d t) / log t.2.1) + τ) *
              ((N : ℝ) / tupleProduct d t) / log t.2.1 else 0 :=
      sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left
        (sum_le_sum (hterm d hd)) (Nat.cast_nonneg _))
    _ = _ := by
      unfold finiteBuchstabMain finiteErrorMass legalPrimeTuples
      simp only [sum_filter, mul_sum, Finset.mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro t _
      split_ifs <;> ring

theorem roughBox_tuple_cube {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {high : Bool} {t : PrimeTuple} (ht : t ∈ actualPrimeTuples N δ p high d) :
    ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d) := by
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hR := (hb.support_geometry hN hη hδ hd).2.2.1
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one
    (hp.one_le_s.trans (hp.s_le_kappa3.trans (hp.kappa3_lt_kappa2.le.trans
      (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hlo : R ^ (1 / 10 : ℝ) ≤ wuLocalCutoff N δ d p.S :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le hS hp.S_le_ten)
  have hhi : wuLocalCutoff N δ d p.s ≤ R ^ (1 / 2 : ℝ) :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (by norm_num) hs)
  obtain ⟨hpre, hp', _, _, hq⟩ := mem_primeTuples.mp ht
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mpr
      ⟨hh.1, hlo.trans hh.2.2.1, hh.2.2.2.le.trans hhi⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r (((secondFunctionalMother_tuple_mem _ _ _).mp hpre).2.2 r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hw _ hp'
    · exact (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mpr
        ⟨hq.1, hlo.trans ((mem_primeWindow.mp hp').2.2.1.trans
          (by exact_mod_cast hq.2.1.le)), hq.2.2.2.trans hhi⟩

theorem roughBox_cube_mass (m : ℕ) {η δ : ℝ} (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d), 1 / (q : ℝ)) ≤ 5 := by
  have he : ∀ᶠ R : ℝ in atTop, (∑ q ∈ primeSlabPrimes R, 1 / (q : ℝ)) ≤ 5 := by
    filter_upwards [eventually_gt_atTop 1,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
        (eventually_ge_atTop primeOrderedMertensStart),
      primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with R hR hs he
    have hh := primeSlab_interval_mass hR hs
      (by norm_num : (1 / 10 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
    change (∑ q ∈ primesIcc (R ^ (1 / 10 : ℝ)) (R ^ (1 / 2 : ℝ)), 1 / (q : ℝ)) ≤ 5
    linarith
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp he
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd
  exact hR0 _ ((hT N (by omega)).trans (hb.remaining d hd))

theorem roughBox_finite_error {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (high : Bool)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d), 1 / (q : ℝ)) ≤ 5) :
    finiteErrorMass N δ Δ V p high ≤
      5 ^ (if high then 6 else 5) / (η / 10) * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ t ∈ legalPrimeTuples N δ p high d, ((N : ℝ) / tupleProduct d t) / log t.2.1) ≤
      ((N : ℝ) / d) / ((η / 10) * log N) * 5 ^ (if high then 6 else 5) := by
    have hrec := tuple_reciprocal_le (legalPrimeTuples N δ p high d)
      (fun t ht => high_tuple_length high (mem_filter.mp ht).1)
      (fun t ht => roughBox_tuple_cube hb (by omega) hη hδ p hp hs hd (mem_filter.mp ht).1)
      (hmass d hd)
    calc
      _ ≤ ∑ t ∈ legalPrimeTuples N δ p high d,
          (((N : ℝ) / d) / ((η / 10) * log N)) * (1 / ((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have hp' := hb.mother_window_large (by omega) hη hδ p hp hd
          (mem_primeTuples.mp (mem_filter.mp ht).1).2.1
        have hy := log_le_log (rpow_pos_of_pos (by positivity : (0 : ℝ) < N) (η / 10)) hp'.2
        rw [log_rpow (by positivity : (0 : ℝ) < N)] at hy
        have heq : ((N : ℝ) / tupleProduct d t) / log t.2.1 =
            ((N : ℝ) / d) * (1 / ((tupleList t).prod : ℝ)) / log t.2.1 := by
          simp only [tupleProduct, Nat.cast_mul]
          ring
        rw [heq]
        exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hy).trans_eq (by ring)
      _ = (((N : ℝ) / d) / ((η / 10) * log N)) *
          (∑ t ∈ legalPrimeTuples N δ p high d, 1 / ((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold finiteErrorMass boxConvolutionReciprocalMass
  rw [mul_sum]
  exact sum_le_sum (fun d hd =>
    (mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)).trans_eq (by ring))

theorem roughBox_rough_mass_paid (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ high : Bool,
      (roughFamily N δ Δ V p high).mass ≤
        finiteBuchstabMain N δ Δ V p high +
          ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let C := (5 : ℝ) ^ 6 / (η / 10)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T0, hT04, hscalar⟩ := roughBox_rough_mass_scalar m hη hδ (div_pos hε hC)
  obtain ⟨T1, _, hcube⟩ := roughBox_cube_mass (δ := δ) m hη
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp hs high
  have hm := hscalar N (by omega) i Δ V hb p hp high
  have he := roughBox_finite_error hb (by omega) hη hδ p hp hs high
    (hcube N (by omega) i Δ V hb)
  have hcap : 5 ^ (if high then 6 else 5) / (η / 10) ≤ C := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    cases high <;> norm_num
  have hrec : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have he' := he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcap (by positivity)) hrec)
  have hpaid := mul_le_mul_of_nonneg_left he' (div_pos hε hC).le
  have heq : (ε / C) * (C * ((N : ℝ) / log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) =
      ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    field_simp
  rw [heq] at hpaid
  exact hm.trans (add_le_add le_rfl hpaid)

theorem roughBox_reciprocal_theta {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ) :
    wuSingularSeries N / log N * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) / 2 := by
  have h := boxTheta_lower_singular_of_support _ hN
    (fun _ hd => hb.support_pos hd) (fun d hd => (hb.support_geometry (by omega) hη hδ hd).2.2)
  have heq : 2 * (wuSingularSeries N / log N * ((N : ℝ) / log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) =
      2 * wuSingularSeries N * (N : ℝ) / log N ^ 2 *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by ring
  linarith only [h, heq]

theorem roughBox_gamma_buchstab (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ high : Bool,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V)
          (if high then 21 else 20) ≤
        actualUnit N δ p (convolutionWuWindows N Δ V) high +
          finiteBuchstabMain N δ Δ V p high *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
              wuSingularSeries N / log N) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let A := (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))
  have hdenom : 0 < 1 - 2 * δ := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨T0, hT04, hden⟩ := roughBox_gamma_rough_density m hη hδ hδhi hρ (half_pos hε)
  obtain ⟨T1, _, hmain⟩ := roughBox_rough_mass_paid m hη hδ (div_pos hε hA)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb p hp hs high
  have hN4 : 4 ≤ N := by omega
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hd := hden N (by omega) he i Δ V hb p hp high
  have hm := mul_le_mul_of_nonneg_right (hmain N (by omega) i Δ V hb p hp hs high)
    (mul_nonneg hA.le hC)
  have ht := mul_le_mul_of_nonneg_left (roughBox_reciprocal_theta hb hN4 hη hδ) hε.le
  have hcancel : (ε / A) * ((N : ℝ) / log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) *
      (A * (wuSingularSeries N / log N)) =
      ε * (wuSingularSeries N / log N * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by field_simp
  rw [add_mul, hcancel] at hm
  change _ ≤ _ + _ * (A * wuSingularSeries N / log N) + _ at hd ⊢
  rw [mul_div_assoc] at hd ⊢
  linarith only [hd, hm, ht]

end Wu18938Campaign.M1.Confirmed
