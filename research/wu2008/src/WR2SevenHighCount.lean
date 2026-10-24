import WR2SevenIntegral

noncomputable section
namespace WuPaper.R2Seven
open Wu2008DoubleSieve WuSource.SrcSingle Real
open SingleUpperQuadrature SingleUpperHighQuadrature SingleUpperLowEndpoint
open scoped Interval BigOperators

theorem high_count_partition {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    highCount N δ (1/3) = highCount N δ (sevenBoundary 7)+
      ∑ j : Fin 7, psiCount j N := by
  rw [seven_actual_partition hN]
  unfold highCount
  rw [HighSix.highPrimes_window hN hh, HighSix.highPrimes_window hN hh]
  change primeBlock N ((1/2-δ)/2) (1/3) =
    primeBlock N ((1/2-δ)/2) (sevenBoundary 7)+
      primeBlock N (sevenBoundary 7) (1/3)
  symm
  apply prime_block_add hN
  · norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]
    linarith
  · norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]

theorem high_count_upper {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      highCount N δ (1/3) ≤
        (4*(∫ t in ((1/2-δ)/2)..(1/3 : ℝ), weight δ t/t)-psiSevenPaid+ε)*
          truncatedSixthMassScale N := by
  obtain ⟨TA,hTA,hA⟩ := actual_high_classical_upper hd hh (half_pos he)
  obtain ⟨TB,_,hB⟩ := actual_publication_gain (half_pos he)
  refine ⟨max TA TB,hTA.trans (le_max_left _ _),?_⟩
  intro N hN hn
  have hlo : (1/2-δ)/2 ≤ sevenBoundary 7 := by
    norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]; linarith
  have hhi : sevenBoundary 7 ≤ (1/3 : ℝ) := by
    norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]
  have ha := hA N (by omega) hn (sevenBoundary 7) hlo hhi
  have hb := hB N (by omega) hn
  have hm := mul_le_mul_of_nonneg_right (seven_classical_le_middle hd.le hh)
    (truncatedSixthClosure_scale_nonneg (show 4 ≤ N by omega))
  have hc : (1/15 : ℝ) ≤ (1/2-δ)/2 := by linarith
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (density_integrable hd.le hh hc hlo hhi)
    (density_integrable hd.le hh (hc.trans hlo) hhi le_rfl)
  rw [high_count_partition (by omega) hd.le hh, ← hs]
  nlinarith only [ha,hb,hm]

end WuPaper.R2Seven
#print axioms WuPaper.R2Seven.high_count_upper
