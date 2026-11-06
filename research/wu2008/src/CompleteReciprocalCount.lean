import CompleteReciprocalGain
import KernelCurvatureWindowCount

namespace Wu2008DoubleSieve.Phase16
open Real HighSixPhase9 SingleUpperHIntegral
open Phase13 (rhoEndpoint rhoEndpoint_bounds)
noncomputable section


/-- The new unconditional raw-integral producer is actually supplied here. -/
theorem complete_reciprocal_actual_count :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g16)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) :=
  Phase10.same_mother_exact_payment g16 B16 B16_pos
    (fun _ hδ hδhi => gain16_linear_error hδ hδhi)


end
end Wu2008DoubleSieve.Phase16
