import WR2GammaHighLowerTripleMainPaid
import WR2GammaHighNineGeometry
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve Real Finset
open scoped Classical

/-- Keep the varying singular series in the comparison with the original Theta. -/
theorem reciprocal_mass_theta {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    wuSingularSeries N/log N*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) ≤
      theta j N δ/2 := by
  have h := boxTheta_lower_singular_of_support (windows j N) hN
    (fun _ hm => boxConvolutionSupport_pos (fun _ _ hp => (mem_primeWindow.mp hp).1.pos) hm)
    (fun d hm => show 1 < (N:ℝ)^(1/2-δ)/d ∧ (N:ℝ)^(1/2-δ)/d ≤ N from by
      rw [support_eq] at hm
      have hg := prime_geometry j (by omega : 2 ≤ N) hd hh hm
      refine ⟨hg.2.2.2.2.2.2.2, ?_⟩
      have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hg.1.one_le
      exact (div_le_self (rpow_nonneg (Nat.cast_nonneg N) _) hd1).trans (by
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ N by omega)) (show 1/2-δ ≤ 1 by linarith)))
  change _ ≤ theta j N δ at h
  have heq : 2*(wuSingularSeries N/log N*((N:ℝ)/log N)*
      boxConvolutionReciprocalMass (windows j N)) =
      2*wuSingularSeries N*(N:ℝ)/log N^2*boxConvolutionReciprocalMass (windows j N) := by ring
  linarith only [h,heq]

/-- A coarse constant suffices for errors; both finite main terms remain unchanged. -/
theorem reciprocal_mass_scale {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      wuSingularSeries N/log N*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) ≤
        240*truncatedSixthMassScale N := by
  obtain ⟨T,hT,h⟩ := GammaNine.theta_total_mass hd hh
  refine ⟨T,hT,?_⟩
  intro N hN hn j
  have ha := reciprocal_mass_theta j (hT.trans hN) hd hh
  have hb := (h N hN hn j).2
  linarith only [ha,hb]

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.reciprocal_mass_scale
