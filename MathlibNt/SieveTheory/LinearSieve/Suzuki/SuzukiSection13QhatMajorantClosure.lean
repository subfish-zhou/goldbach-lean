import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCutoffClaim146iiiSanitized
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiQuantitativeDerivatives

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

open BridgeAssembly CutoffCorrectedRatio
open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10CanonicalXi

namespace Section13QhatMajorantClosure


/-- The Section-13 source DDE, positivity and proved pairing identity give the
complete non-circular first-crossing apparatus for the single function `Qhat`. -/
noncomputable def section13QhatFirstCrossingData
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    FirstCrossingDDEApparatus (section13Qhat H) 3 where
  adjoint := section13AdjointPlus
  beta_ge_one := by norm_num
  continuous := (section13Qhat_continuousOn hH.toSection13HatContract).mono (by
    intro s hs
    norm_num at hs ⊢
    linarith)
  positive := by
    intro s hs
    exact section13Qhat_pos hH.toSection13HatContract (by linarith)
  original_dde := by
    intro s hs
    exact section13Qhat_dde hH.toSection13HatContract hs
  adjoint_positive := by
    intro s hs
    dsimp [section13AdjointPlus]
    nlinarith [sq_nonneg (s - 1)]
  adjoint_dde := by
    intro s _hs
    exact section13AdjointPlus_dde s
  pairing_zero := by
    intro s hs
    have hz := section13Qhat_pairing_zero hH hs
    have heq := sub_eq_zero.mp hz
    simpa [section10SignedPairing, section13AdjointPlus] using heq


end Section13QhatMajorantClosure
end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
