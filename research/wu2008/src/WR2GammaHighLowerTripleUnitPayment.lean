import WR2GammaHighLowerTripleUnitMain
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitPrimePayment

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedUnit HighBoxRecovery Real Finset Filter LiLiuPrereqBuchstab
open scoped Classical Topology

/-- Both original pair coordinates lie in the fixed logarithmic slab. -/
theorem actualPairs_subset_slab {N d : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hd : d ∈ boxConvolutionSupport (windows j N)) :
    actualPairs N δ (Wu04RemainingCore.row j) k d ⊆
      (primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)).product
        (primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)) := by
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
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hh.1,hlo.trans hh.2.2.1,hh.2.2.2.le.trans hhi⟩
  intro x hx
  obtain ⟨hx1,hx2,_,_⟩ := mem_pairs.mp hx
  exact mem_product.mpr ⟨hw _ hx1,hw _ hx2⟩

/-- Pay both pair coordinates while retaining the convolution mass. -/
theorem unitPrimeError_le {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hmass : ∀ d ∈ boxConvolutionSupport (windows j N),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    unitPrimeError j N highEta δ k ≤
      5^2/highEta * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (windows j N) := by
  let η := highEta
  have hη : 0 < η := by norm_num [η, highEta]
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (windows j N)) :
      (∑ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d, ((N:ℝ)/denominator d x)/(η*log N)) ≤
      ((N:ℝ)/d)/(η*log N) * 5^2 := by
    have hrec := pair_reciprocal_le (actualPairs N δ (Wu04RemainingCore.row j) k d)
      (actualPairs_subset_slab j k (by omega) hδ hδhi hd) (hmass d hd)
    calc
      _ = ∑ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d,
          (((N:ℝ)/d)/(η*log N)) * (1/((x.1:ℝ)*x.2)) := by
        apply sum_congr rfl
        intro x hx
        simp only [denominator, Nat.cast_mul]
        ring
      _ = (((N:ℝ)/d)/(η*log N)) *
          (∑ x ∈ actualPairs N δ (Wu04RemainingCore.row j) k d, 1/((x.1:ℝ)*x.2)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold unitPrimeError boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (windows j N) d : ℝ) *
      (((N:ℝ)/d)/(η*log N) * 5^2) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [η]; ring

/-- A single threshold supplies all three windows and all convolution indices. -/
theorem high_slab_mass {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ d ∈ boxConvolutionSupport (windows j N),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5 := by
  have he : ∀ᶠ R : ℝ in atTop, (∑ q ∈ primeSlabPrimes R, 1/(q:ℝ)) ≤ 5 := by
    filter_upwards [eventually_gt_atTop 1,
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).eventually
        (eventually_ge_atTop primeOrderedMertensStart),
      primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
      with R hR hs he
    have hh := primeSlab_interval_mass hR hs
      (by norm_num : (1/10:ℝ) ≤ 1/10) (by norm_num : (1/10:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1/2)
    change (∑ q ∈ primesIcc (R^(1/10:ℝ)) (R^(1/2:ℝ)), 1/(q:ℝ)) ≤ 5
    linarith
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp he
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num [highEta] : 0 < 10*highEta)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R0))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN j d hd
  have hd' := hd
  rw [support_eq] at hd'
  exact hR0 _ ((hT N ((le_max_right _ _).trans hN)).trans
    (prime_geometry j (by omega : 2 ≤ N) hδ hδhi hd').2.2.2.2.2.2.1)

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.unitPrimeError_le
#print axioms WuPaper.R2GammaHigh.LowerTriple.high_slab_mass
