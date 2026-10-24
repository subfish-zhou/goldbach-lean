import WR2GammaHighLowerTripleSmall
import WR2GammaHighLowerTripleR1
import WR2GammaHighLowerTripleR2
import Wu08FourMotherRelative

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped HighBoxRecovery Real Finset
open scoped Classical

theorem small_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Fin 6,
      (sourceFamily j N δ k).small (sqrt ((N : ℝ)^(1/2-δ))) ≤ ε*truncatedSixthMassScale N := by
  have hK : 0 < (max 1 (1/highEta))^4 := by positivity
  have hg : 0 < 1-(1/2-δ)/2 := by linarith
  obtain ⟨T,hT,hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 0 he hK hg
  refine ⟨T,hT,fun N hN j k => ?_⟩
  have hs := HighUnitSieve.source_small_power (by omega : 2 ≤ N) hd (by linarith : δ < 1/2)
  exact (small_bound j k (by omega) hd hh (sqrt_nonneg _)).trans
    ((hs.2.2.2.2.2 _).trans_le (hp N hN))

theorem R1_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Fin 6, ∀ Z : ℝ,
      (sourceFamily j N δ k).R1 (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C,hC,T0,hT0,hc⟩ := R1_log_bound hd hh (by norm_num : (0 : ℝ)<3)
  obtain ⟨T1,_,hp⟩ := Wu08FourMother.raw_error_paid (div_pos he hC)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),fun N hN j k Z => ?_⟩
  have hb := hc N (by omega) j k Z
  norm_num at hb
  calc
    _ ≤ C*N/log (N : ℝ)^3 := hb
    _ = C*((N : ℝ)/log (N : ℝ)^3) := by ring
    _ ≤ C*((ε/C)*U8CanonicalMother.M N) := mul_le_mul_of_nonneg_left (hp N (by omega)) hC.le
    _ = ε*truncatedSixthMassScale N := by
      rw [← mul_assoc, mul_div_cancel₀ ε hC.ne']
      rfl

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.small_paid
#print axioms WuPaper.R2GammaHigh.LowerTriple.R1_paid
