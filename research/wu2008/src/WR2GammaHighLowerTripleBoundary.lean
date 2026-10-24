import WR2GammaHighLowerTripleClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleShiftedBoundary

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedFinite LowerTripleGroupedUnit LowerTripleGroupedBoundary
open HighBoxRecovery Real Finset LiLiuPrereqBuchstab
open scoped Classical

/-- Only the closed lower r condition is added; every original gate is retained. -/
noncomputable def unshiftedFiniteBuchstabMain (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ (legalPrimeTriples N δ (Wu04RemainingCore.row j) k d).filter (fun t =>
      (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1 ≤ (t.2.2 : ℝ)), mainWeight N d t

noncomputable def boundaryMass (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (windows j N),
    (convolutionCoeff (windows j N) d : ℝ) *
    ∑ t ∈ badTriples N δ (Wu04RemainingCore.row j) k d, mainWeight N d t

/-- In particular the r=rLo atom belongs to the retained summand. -/
theorem main_split (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) :
    finiteBuchstabMain j N δ k =
      unshiftedFiniteBuchstabMain j N δ k + boundaryMass j N δ k := by
  unfold finiteBuchstabMain unshiftedFiniteBuchstabMain boundaryMass badTriples mainWeight
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← mul_add, sum_filter, sum_filter, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro t _
  by_cases h : (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1 ≤ (t.2.2 : ℝ)
  · simp only [h, not_lt_of_ge h, if_true, if_false, add_zero]
  · simp only [h, lt_of_not_ge h, if_true, if_false, zero_add]

/-- One bad atom per labelled pair gains N^(-eta), before sigma summation. -/
theorem bad_weight_le {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hd : d ∈ boxConvolutionSupport (windows j N))
    {k : Fin 6} {t : PrimeTriple} (ht : t ∈ badTriples N δ (Wu04RemainingCore.row j) k d) :
    mainWeight N d t ≤
      (((N:ℝ)/d)/((highEta)*log N)) *
        (N:ℝ)^(-(highEta)) * (1/((t.1:ℝ)*t.2.1)) := by
  let η := highEta
  have hη : 0 < η := by norm_num [η, highEta]
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hNpos : (0:ℝ) < N := by positivity
  have hlegal := (mem_filter.mp ht).1
  have hactual := (mem_filter.mp hlegal).1
  have hdp := boxConvolutionSupport_pos
    (fun _ _ h => (mem_primeWindow.mp h).1.pos) hd
  have hq := (window_lower j (by omega) hδ hδhi hd
    (mem_primeTriples.mp hactual).2.1).2
  have hlog := log_le_log (rpow_pos_of_pos hNpos η) hq
  rw [log_rpow hNpos] at hlog
  have hrq : (t.2.1:ℝ) < t.2.2 :=
    (le_max_left _ _).trans_lt (mem_primeTriples.mp hactual).2.2.2.2.2.2.1
  have hr : 1/(t.2.2:ℝ) ≤ (N:ℝ)^(-η) := by
    rw [rpow_neg hNpos.le, ← one_div]
    exact one_div_le_one_div_of_le (rpow_pos_of_pos hNpos η) (hq.trans hrq.le)
  calc
    _ ≤ ((N:ℝ)/tupleProduct d t)/log t.2.1 := legal_weight_le hdp hlegal
    _ ≤ ((N:ℝ)/tupleProduct d t)/(η*log N) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hη hlogN) hlog
    _ = ((((N:ℝ)/d)/(η*log N)) * (1/((t.1:ℝ)*t.2.1))) * (1/(t.2.2:ℝ)) := by
      simp only [tupleProduct, Nat.cast_mul]
      ring
    _ ≤ ((((N:ℝ)/d)/(η*log N)) * (1/((t.1:ℝ)*t.2.1))) * (N:ℝ)^(-η) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

/-- The full original sigma is multiplied once, with no division by its mass. -/
theorem boundaryMass_le {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (k : Fin 6)
    (hmass : ∀ d ∈ boxConvolutionSupport (windows j N),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    boundaryMass j N δ k ≤
      (5^2/(highEta)) * (N:ℝ)^(-(highEta)) *
        ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N) := by
  let η := highEta
  have hη : 0 < η := by norm_num [η, highEta]
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (windows j N)) :
      (∑ t ∈ badTriples N δ (Wu04RemainingCore.row j) k d, mainWeight N d t) ≤
        (((N:ℝ)/d)/(η*log N)) * (N:ℝ)^(-η) * 5^2 := by
    have hrec := bad_pair_reciprocal_le (N := N) (d := d) (δ := δ) (P := Wu04RemainingCore.row j) (j := k)
    have hpair := pair_reciprocal_le (actualPairs N δ (Wu04RemainingCore.row j) k d)
      (actualPairs_subset_slab j k (by omega) hδ hδhi hd) (hmass d hd)
    calc
      _ ≤ ∑ t ∈ badTriples N δ (Wu04RemainingCore.row j) k d,
          ((((N:ℝ)/d)/(η*log N)) * (N:ℝ)^(-η)) * (1/((t.1:ℝ)*t.2.1)) :=
        sum_le_sum (fun t ht => bad_weight_le j hN hδ hδhi hd ht)
      _ = ((((N:ℝ)/d)/(η*log N)) * (N:ℝ)^(-η)) *
          (∑ t ∈ badTriples N δ (Wu04RemainingCore.row j) k d, 1/((t.1:ℝ)*t.2.1)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrec.trans hpair) (by positivity)
  unfold boundaryMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (windows j N) d : ℝ) *
        ((((N:ℝ)/d)/(η*log N)) * (N:ℝ)^(-η) * 5^2) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [η]; ring

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.main_split
#print axioms WuPaper.R2GammaHigh.LowerTriple.boundaryMass_le
