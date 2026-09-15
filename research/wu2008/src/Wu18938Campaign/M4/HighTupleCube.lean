import Wu18938Campaign.M4.HighRoughScalar
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteErrorPayment

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real Filter
open LiLiuPrereqBuchstab HighBoxRecovery
open scoped Classical

theorem tuple_cube_of_local_level {N d : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    (hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / d) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    {high : Bool} {t : PrimeTuple} (ht : t ∈ actualPrimeTuples N δ p high d) :
    ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d) := by
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hS : 0 < p.S := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (hp.one_le_s.trans (hp.s_le_kappa3.trans (hp.kappa3_lt_kappa2.le.trans
      (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hlo : R ^ (1 / 10 : ℝ) ≤ wuLocalCutoff N δ d p.S :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le hS hp.S_le_ten)
  have hhi : wuLocalCutoff N δ d p.s ≤ R ^ (1 / 2 : ℝ) :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (by norm_num) hs)
  obtain ⟨hpre, hp', _, _, hq⟩ := mem_primeTuples.mp ht
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have h := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨h.1, hlo.trans h.2.2.1, h.2.2.2.le.trans hhi⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r (((secondFunctionalMother_tuple_mem _ _ _).mp hpre).2.2 r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hw _ hp'
    · exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
        ⟨hq.1, hlo.trans ((mem_primeWindow.mp hp').2.2.1.trans
          (by exact_mod_cast hq.2.1.le)), hq.2.2.2.trans hhi⟩

theorem original_tuple_cube {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hdm : d ∈ boxConvolutionSupport (windows j N)) {high : Bool} {t : PrimeTuple}
    (ht : t ∈ actualPrimeTuples N δ (Wu04RemainingCore.row j) high d) :
    ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d) := by
  rw [support_eq] at hdm
  exact tuple_cube_of_local_level (prime_geometry j hN hd hh hdm).2.2.2.2.2.2.2
    (row_analytic j).mother (row_analytic j).two_lt_s.le ht

theorem original_cube_mass :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ d ∈ boxConvolutionSupport (windows j N),
      (∑ q ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d), 1 / (q : ℝ)) ≤ 5 := by
  have he : ∀ᶠ R : ℝ in atTop, (∑ q ∈ primeSlabPrimes R, 1 / (q : ℝ)) ≤ 5 := by
    filter_upwards [eventually_gt_atTop 1,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
        (eventually_ge_atTop primeOrderedMertensStart),
      primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with R hR hs he
    have h := primeSlab_interval_mass hR hs
      (by norm_num : (1 / 10 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
    change (∑ q ∈ primesIcc (R ^ (1 / 10 : ℝ)) (R ^ (1 / 2 : ℝ)), 1 / (q : ℝ)) ≤ 5
    linarith
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp he
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num [highEta] : (0 : ℝ) < 10 * highEta)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro δ hd hh N hN j d hdm
  rw [support_eq] at hdm
  exact hR0 _ ((hT N (by omega)).trans
    (prime_geometry j (by omega) hd hh hdm).2.2.2.2.2.2.1)

end Wu18938Campaign.M4
