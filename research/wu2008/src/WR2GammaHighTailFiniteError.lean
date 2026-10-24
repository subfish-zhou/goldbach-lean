import WR2GammaHighTailBuchstab
import WR2GammaHighLowerTripleUnitPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteErrorPayment

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit HighBoxRecovery Real Finset LiLiuPrereqBuchstab
open scoped Classical

/-- Each of the four original prime coordinates lies in the fixed logarithmic slab. -/
theorem actual_tuple_cube {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hd : d ∈ boxConvolutionSupport (windows j N))
    {k : Bool} {t : PrimeTuple}
    (ht : t ∈ actualPrimeTuples N δ (Wu04RemainingCore.row j) k d) :
    ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d) := by
  let R := (N:ℝ)^(1/2-δ)/d
  have hd' := hd
  rw [support_eq] at hd'
  have hR := (prime_geometry j hN hδ hδhi hd').2.2.2.2.2.2.2
  let p := Wu04RemainingCore.row j
  have hp := (row_analytic j).mother
  have hs := (row_analytic j).two_lt_s.le
  have hS : 0 < p.S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (hp.one_le_s.trans (hp.s_le_kappa3.trans (hp.kappa3_lt_kappa2.le.trans
      (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hlo : R^(1/10:ℝ) ≤ wuLocalCutoff N δ d p.S :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le hS hp.S_le_ten)
  have hhi : wuLocalCutoff N δ d p.s ≤ R^(1/2:ℝ) :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (by norm_num) hs)
  obtain ⟨hpre,hp',_,_,hq⟩ := mem_primeTuples.mp ht
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hh.1,hlo.trans hh.2.2.1,hh.2.2.2.le.trans hhi⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r (((secondFunctionalMother_tuple_mem _ _ _).mp hpre).2.2 r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hw _ hp'
    · exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
        ⟨hq.1,hlo.trans ((mem_primeWindow.mp hp').2.2.1.trans
          (by exact_mod_cast hq.2.1.le)),hq.2.2.2.trans hhi⟩

/-- Complete reciprocal weights control the original finite error. -/
theorem finiteErrorMass_le {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Bool)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hmass : ∀ d ∈ boxConvolutionSupport (windows j N),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    finiteErrorMass j N δ k ≤
      5^6/highEta * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N) := by
  let η := highEta
  have hη : 0 < η := by norm_num [η, highEta]
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (windows j N)) :
      (∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) k d, ((N:ℝ)/tupleProduct d t)/log t.2.1) ≤
      ((N:ℝ)/d)/(η*log N) * 5^6 := by
    have hrec := tuple_reciprocal_le (legalPrimeTuples N δ (Wu04RemainingCore.row j) k d)
      (fun t ht => tuple_length (word_length k) (mem_filter.mp ht).1)
      (fun t ht => actual_tuple_cube j (by omega) hδ hδhi hd (mem_filter.mp ht).1)
      (hmass d hd)
    have hrec := hrec.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 5)
      (show (word k).length ≤ 6 by cases k <;> norm_num [word, HighUnitSource.word20, HighUnitSource.word21]))
    calc
      _ ≤ ∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) k d,
          (((N:ℝ)/d)/(η*log N)) * (1/((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have hp' := LowerTriple.window_lower j (by omega) hδ hδhi hd
          (mem_primeTuples.mp (mem_filter.mp ht).1).2.1
        have hy := log_le_log (rpow_pos_of_pos (by positivity : (0:ℝ) < N) η) hp'.2
        rw [log_rpow (by positivity : (0:ℝ) < N)] at hy
        have heq : ((N:ℝ)/tupleProduct d t)/log t.2.1 =
            ((N:ℝ)/d) * (1/((tupleList t).prod : ℝ)) / log t.2.1 := by
          simp only [tupleProduct, Nat.cast_mul]
          ring
        rw [heq]
        calc
          _ ≤ ((N:ℝ)/d) * (1/((tupleList t).prod : ℝ)) / (η*log N) :=
            div_le_div_of_nonneg_left (by positivity) (mul_pos hη hlogN) hy
          _ = _ := by ring
      _ = (((N:ℝ)/d)/(η*log N)) *
          (∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) k d, 1/((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold finiteErrorMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (windows j N) d : ℝ) *
      (((N:ℝ)/d)/(η*log N) * 5^6) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [η]; ring

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.finiteErrorMass_le
