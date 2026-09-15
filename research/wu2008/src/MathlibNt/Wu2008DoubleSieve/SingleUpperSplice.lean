import MathlibNt.Wu2008DoubleSieve.SingleUpperHighDensity

namespace Wu2008DoubleSieve.SingleUpperSplice
open Finset Real Filter SingleUpperCounts
open scoped Classical Topology
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def lowPrimes (N : ℕ) (δ r : ℝ) : Finset ℕ :=
  (primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r)).filter
    (fun p => (p : ℝ) < (N : ℝ)^((1/2-δ)/2))

noncomputable def highPrimes (N : ℕ) (δ r : ℝ) : Finset ℕ :=
  (primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r)).filter
    (fun p => (N : ℝ)^((1/2-δ)/2) ≤ (p : ℝ))

noncomputable def lowCount (N : ℕ) (δ r : ℝ) : ℝ :=
  ∑ p ∈ lowPrimes N δ r, (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)

noncomputable def highDensityMass (N : ℕ) (δ ρ r : ℝ) : ℝ :=
  ∑ p ∈ highPrimes N δ r,
    (logarithmicIntegral N / (Nat.totient p : ℝ)) *
      ((jr1965F (((1/2-δ)-log (p : ℝ)/log (N : ℝ))/truncatedSixthLowerAlpha)+ρ) *
        localSieveProduct N ((N : ℝ)^truncatedSixthLowerAlpha))

/-- Exact split, with every equality atom assigned to the high segment. -/
theorem count_split (N : ℕ) (δ r : ℝ) :
    (U N r : ℝ) = lowCount N δ r +
      ∑ p ∈ highPrimes N δ r,
        (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  unfold U lowCount lowPrimes highPrimes
  rw [Int.cast_sum]
  simpa only [not_lt] using (sum_filter_add_sum_filter_not
    (primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^r))
    (fun p => (p : ℝ) < (N : ℝ)^((1/2-δ)/2))
    (fun p => (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ))).symm

/-- The aggregate epsilon estimate remains uniform after any prime mask.
The threshold precedes P; no moving primewise thresholds or triangle bound. -/
theorem masked_remainder_small {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p.Coprime N ∧
        (N : ℝ)^truncatedSixthLowerAlpha ≤ (p : ℝ)) →
      |∑ p ∈ P, ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p)
        ((N : ℝ)^truncatedSixthLowerAlpha)| ≤ ε * truncatedSixthMassScale N := by
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  obtain ⟨C, hC, T, hBV⟩ := global_signed_bv ha hδ (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (C/(ε*wuSingularSeries 1))))
  refine ⟨max 4 (max T M), le_max_left _ _, ?_⟩
  intro N hN P hP
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNT : T ≤ N := (le_max_left T M).trans ((le_max_right _ _).trans hN)
  have hNM : M ≤ N := (le_max_right T M).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hbudget : C / log (N : ℝ) ≤ ε * wuSingularSeries N := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hC1)).mp (hM N hNM)
    have hs := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hseries hε.le) hlog.le
    nlinarith
  have hb := hBV N hNT P hP true (wuVariableRosserLevel N δ)
    (fun _ => (N : ℝ)^truncatedSixthLowerAlpha)
    (fun p _ => (wuVariableRosserLevel_eq_combined N p δ).le)
  have hb' : |∑ p ∈ P, ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p)
      ((N : ℝ)^truncatedSixthLowerAlpha)| ≤ C * N / log (N : ℝ)^(3 : ℕ) := by
    convert hb using 1
    norm_num
  calc
    _ ≤ C * N / log (N : ℝ)^(3 : ℕ) := hb'
    _ = (C / log (N : ℝ)) * ((N : ℝ)/log (N : ℝ)^(2 : ℕ)) := by ring
    _ ≤ (ε * wuSingularSeries N) * ((N : ℝ)/log (N : ℝ)^(2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

/-- Actual finite high-count upper; the low count is not compared to Rosser main. -/
theorem high_finite_upper {N : ℕ} {δ r : ℝ}
    (hN : 2 ≤ N) (hδ : δ ≤ 1/100) (hr : r ≤ 1/3) :
    (∑ p ∈ highPrimes N δ r,
      (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)) ≤
    (∑ p ∈ highPrimes N δ r,
      (logarithmicIntegral N / (Nat.totient p : ℝ)) *
        ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p)
          ((N : ℝ)^truncatedSixthLowerAlpha)) +
    ∑ p ∈ highPrimes N δ r,
      ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p)
        ((N : ℝ)^truncatedSixthLowerAlpha) := by
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have hpw := (mem_filter.mp hp).1
  have hg := full_level_geometry hN hδ hr hpw
  rw [← source_count (mem_primeWindow.mp hpw).1 (mem_primeWindow.mp hpw).2.2.1]
  exact ordinaryRosser_upper_finite hg.1 hg.2.2

/-- The full original count spliced at count level, with a genuine high-density
term and a globally paid masked remainder. The unevaluated low count is explicit. -/
theorem actual_low_high_upper {δ ρ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ r : ℝ, r ≤ 1/3 →
      (U N r : ℝ) ≤ lowCount N δ r + highDensityMass N δ ρ r +
        ε * truncatedSixthMassScale N := by
  obtain ⟨TB, hTB4, hBV⟩ := masked_remainder_small hδ hε
  obtain ⟨TD, _, hD⟩ := high_prime_density hδ.le hδhi hρ
  refine ⟨max TB TD, hTB4.trans (le_max_left _ _), ?_⟩
  intro N hN he r hr
  have hNB : TB ≤ N := (le_max_left _ _).trans hN
  have hND : TD ≤ N := (le_max_right _ _).trans hN
  have hN4 := hTB4.trans hNB
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hmain : (∑ p ∈ highPrimes N δ r,
      (logarithmicIntegral N / (Nat.totient p : ℝ)) *
        ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p)
          ((N : ℝ)^truncatedSixthLowerAlpha)) ≤ highDensityMass N δ ρ r := by
    apply sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left
      (hD N hND he r hr p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
      (div_nonneg hli (Nat.cast_nonneg _))
  have hrem := hBV N hNB (highPrimes N δ r) (fun p hp =>
    ⟨(mem_primeWindow.mp (mem_filter.mp hp).1).1,
     (mem_primeWindow.mp (mem_filter.mp hp).1).2.1,
     (mem_primeWindow.mp (mem_filter.mp hp).1).2.2.1⟩)
  have hf := high_finite_upper (δ := δ) (r := r) (by omega : 2 ≤ N) hδhi hr
  rw [count_split N δ r]
  linarith [le_abs_self (∑ p ∈ highPrimes N δ r,
    ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p)
      ((N : ℝ)^truncatedSixthLowerAlpha))]

/-- One threshold for the original two summands; their overlap still occurs twice. -/
theorem both_low_high_upper {δ ρ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (U N (1/3) : ℝ) + (U N truncatedSixthLowerSigma : ℝ) ≤
        lowCount N δ (1/3) + lowCount N δ truncatedSixthLowerSigma +
        highDensityMass N δ ρ (1/3) + highDensityMass N δ ρ truncatedSixthLowerSigma +
        ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT4, hT⟩ := actual_low_high_upper hδ hδhi hρ (half_pos hε)
  refine ⟨T, hT4, ?_⟩
  intro N hN he
  have hσ : truncatedSixthLowerSigma ≤ (1/3 : ℝ) := by
    norm_num [truncatedSixthLowerSigma, truncatedSixthLowerAlpha]
  have h1 := hT N hN he (1/3) le_rfl
  have h2 := hT N hN he truncatedSixthLowerSigma hσ
  linarith

end Wu2008DoubleSieve.SingleUpperSplice
