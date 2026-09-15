import CoupledFiniteAssembly
import GatedDensityFinite

namespace CoupledFullyFinite
open Real NodeExtension ActualNineFeedback Wu2008DoubleSieve
open CoupledFiniteAssembly GatedDensityPayment OriginalProfileSigmaPayment
noncomputable section

/-- No integral remains in this lower expression; every original term is paid once. -/
def lower (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  aCoefficient p*aFiniteLower z+remainder p z+densityFinite p z/5

theorem lower_le {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) : lower p z ≤ coupledFeedback p z := by
  have hd := div_le_div_of_nonneg_right (densityFinite_le hp.1 z hz) (by norm_num : (0:ℝ) ≤ 5)
  exact (add_le_add le_rfl hd).trans (finite_profile_lower hp hz)

/-- The original four H expressions, not a certificate that these reach the H targets. -/
theorem original_four (i : Fin 4) :
    lower (coupledRow i) NineFeedbackStrength.originalH ≤
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH :=
  lower_le (coupledRow_geometry i) CoupledIntegralRecovery.originalH_nonneg

end
end CoupledFullyFinite
