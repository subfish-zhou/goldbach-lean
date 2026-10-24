import WR2GammaHighLowerTripleBuchstab
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFiniteErrorPayment

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedFinite HighBoxRecovery Real Finset LiLiuPrereqBuchstab
open scoped Classical

/-- All three ordered prime labels lie in the common logarithmic slab. -/
theorem actual_tuple_cube {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hd : d ∈ boxConvolutionSupport (windows j N))
    {k : Fin 6} {t : PrimeTriple}
    (ht : t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d) :
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
  obtain ⟨hp',hq',_,_,_,hr',hl,hu⟩ := mem_primeTriples.mp ht
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hh.1,hlo.trans hh.2.2.1,hh.2.2.2.le.trans hhi⟩
  have hk3 : wuLocalCutoff N δ d p.kappa3 ≤ R^(1/2:ℝ) :=
    rpow_le_rpow_of_exponent_le hR.le
      (one_div_le_one_div_of_le (by norm_num) (hs.trans hp.s_le_kappa3))
  have huppers : ∀ j' : Fin 6,
      (LowerTripleGrouped.actualBands N δ p j' d).2.2.2.2.2 ≤ R^(1/2:ℝ) := by
    unfold LowerTripleGrouped.actualBands LowerTripleGrouped.bands
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · exact hhi
    · exact hk3
    · exact hhi
    · exact hhi
    · exact hhi
    · exact hhi
  have hupper := huppers k
  intro r hr
  simp only [tupleList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hw _ hp'
  · exact hw _ hq'
  · exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hr',hlo.trans ((mem_primeWindow.mp hq').2.2.1.trans
        ((le_max_left _ _).trans hl.le)),hu.trans hupper⟩

/-- The original reciprocal weights pay the complete nonunit scalar error. -/
theorem finiteErrorMass_le {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hmass : ∀ d ∈ boxConvolutionSupport (windows j N),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    finiteErrorMass j N δ k ≤
      5^3/highEta * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N) := by
  let η := highEta
  have hη : 0 < η := by norm_num [η, highEta]
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (windows j N)) :
      (∑ t ∈ legalPrimeTriples N δ (Wu04RemainingCore.row j) k d, ((N:ℝ)/tupleProduct d t)/log t.2.1) ≤
      ((N:ℝ)/d)/(η*log N) * 5^3 := by
    have hrec := tuple_reciprocal_le (legalPrimeTriples N δ (Wu04RemainingCore.row j) k d)
      (fun t ht => actual_tuple_cube j (by omega) hδ hδhi hd (mem_filter.mp ht).1)
      (hmass d hd)
    calc
      _ ≤ ∑ t ∈ legalPrimeTriples N δ (Wu04RemainingCore.row j) k d,
          (((N:ℝ)/d)/(η*log N)) * (1/((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have hp' := window_lower j (by omega) hδ hδhi hd
          (mem_primeTriples.mp (mem_filter.mp ht).1).2.1
        have hy := log_le_log (rpow_pos_of_pos (by positivity : (0:ℝ) < N) η) hp'.2
        rw [log_rpow (by positivity : (0:ℝ) < N)] at hy
        have heq : ((N:ℝ)/tupleProduct d t)/log t.2.1 =
            ((N:ℝ)/d) * (1/((tupleList t).prod : ℝ)) / log t.2.1 := by
          simp only [tupleProduct_literal, Nat.cast_mul]
          ring
        rw [heq]
        calc
          _ ≤ ((N:ℝ)/d) * (1/((tupleList t).prod : ℝ)) / (η*log N) :=
            div_le_div_of_nonneg_left (by positivity) (mul_pos hη hlogN) hy
          _ = _ := by ring
      _ = (((N:ℝ)/d)/(η*log N)) *
          (∑ t ∈ legalPrimeTriples N δ (Wu04RemainingCore.row j) k d, 1/((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold finiteErrorMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (windows j N) d : ℝ) *
      (((N:ℝ)/d)/(η*log N) * 5^3) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [η]; ring

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.finiteErrorMass_le
