import FiniteEndpointJ
import OriginalSigmaFiniteConsumers

namespace CoupledFiniteAssembly
open Real NodeExtension ActualNineFeedback Wu2008DoubleSieve
open FiniteEndpointPayment CoupledIntegralRecovery OriginalProfileSigmaPayment
open scoped BigOperators
noncomputable section

/-- The finite E part after separating its genuine common profile. -/
def eRest (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*FirstFeedbackIntegrals.eCell S (left (S-2) 3 k) (right (S-2) 3 k)

/-- All original J tails and cells survive in this finite remainder. -/
def jRest (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  tail z (S-2)*log ((S-1)/(s-1))+
    ∑ k : Fin 9,z k*(jPrimitive S (jStart s S) (right (jStart s S-1) (S-2) k)-
      jPrimitive S (jStart s S) (left (jStart s S-1) (S-2) k))

def aCoefficient (p : SecondFunctionalParameters) : ℝ :=
  (4*log (4/(p.S-1))+log (4/(p.kappa1-1))+
    log ((p.S-1)/(p.s-1))+log ((p.S-1)/(p.kappa2-1))+
    log ((p.S-1)/(p.kappa3-1)))/5

def remainder (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  (4*eRest z p.S+eRest z p.kappa1+jRest z p.s p.S+
    jRest z p.kappa2 p.S+jRest z p.kappa3 p.S)/5

theorem aCoefficient_nonneg {p : SecondFunctionalParameters} (hp : CoupledGeometry p) :
    0 ≤ aCoefficient p := by
  have hg := coupled_geometry_bounds hp
  have he0 := log_nonneg ((one_le_div (by linarith [hp.1.three_le_S] : 0<p.S-1)).mpr
    (by linarith [hp.1.S_le_five] : p.S-1≤4))
  have he1 := log_nonneg ((one_le_div (by linarith [hp.2.1] : 0<p.kappa1-1)).mpr
    (by linarith [hg.2.2.2.2.2.2] : p.kappa1-1≤4))
  have hj0 := log_nonneg ((one_le_div (by linarith [hg.1] : 0<p.s-1)).mpr
    (by linarith [hg.2.1] : p.s-1≤p.S-1))
  have hj2 := log_nonneg ((one_le_div (by linarith [hg.2.2.1] : 0<p.kappa2-1)).mpr
    (by linarith [hg.2.2.2.1] : p.kappa2-1≤p.S-1))
  have hj3 := log_nonneg ((one_le_div (by linarith [hg.2.2.2.2.1] : 0<p.kappa3-1)).mpr
    (by linarith [hg.2.2.2.2.2.1] : p.kappa3-1≤p.S-1))
  unfold aCoefficient
  positivity

/-- Only the still-unpaid density remains an actual integral in the assembled row. -/
theorem analytic_lower {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) :
    aCoefficient p*aProfile (nineProfile z)+remainder p z+densityMoment p z/5 ≤
      coupledFeedback p z := by
  have hg := coupled_geometry_bounds hp
  have he0 := e_le z hz hp.1.three_le_S hp.1.S_le_five
  have he1 := e_le z hz hp.2.1 hg.2.2.2.2.2.2
  have hj0 := j_le z hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := j_le z hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := j_le z hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  have hraw : (4*e z p.S+e z p.kappa1+j z p.s p.S+j z p.kappa2 p.S+
      j z p.kappa3 p.S+densityMoment p z)/5 ≤ coupledFeedback p z := by
    unfold coupledFeedback
    linarith only [he0,he1,hj0,hj2,hj3]
  calc
    _ = (4*e z p.S+e z p.kappa1+j z p.s p.S+j z p.kappa2 p.S+
      j z p.kappa3 p.S+densityMoment p z)/5 := by
      unfold aCoefficient remainder eRest jRest FiniteEndpointPayment.e j
      ring
    _ ≤ _ := hraw

/-- The same complete row consumes the proved finite sigma normalization. -/
theorem finite_profile_lower {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) :
    aCoefficient p*aFiniteLower z+remainder p z+densityMoment p z/5 ≤ coupledFeedback p z := by
  have ha := mul_le_mul_of_nonneg_left (aFiniteLower_le_aProfile hz) (aCoefficient_nonneg hp)
  exact (add_le_add (add_le_add ha le_rfl) le_rfl).trans (analytic_lower hp hz)

/-- Original four rows; this is a paid lower expression, not the unproved H-table comparison. -/
theorem original_four (i : Fin 4) :
    aCoefficient (coupledRow i)*aFiniteLower NineFeedbackStrength.originalH+
      remainder (coupledRow i) NineFeedbackStrength.originalH+
      densityMoment (coupledRow i) NineFeedbackStrength.originalH/5 ≤
        coupledFeedback (coupledRow i) NineFeedbackStrength.originalH :=
  finite_profile_lower (coupledRow_geometry i) originalH_nonneg

end
end CoupledFiniteAssembly
