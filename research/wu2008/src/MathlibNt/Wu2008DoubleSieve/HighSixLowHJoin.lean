import MathlibNt.Wu2008DoubleSieve.HighSixFullU3
import MathlibNt.Wu2008DoubleSieve.TruncatedElevenHIntegralCount

/-! Fixed delta only. Reassemble two actual low counts and two actual high
counts before integrating; no subtraction of unrelated upper bounds. -/
namespace Wu2008DoubleSieve.HighSixLowHJoin
open Real SingleUpperCounts SingleUpperSplice SingleUpperLowPacking
open SingleUpperQuadrature SingleUpperHighQuadrature SingleUpperHAssembly
open SingleUpperClassicalLimit SingleUpperHPackingEndpoint SingleUpperHIntegral
open SingleUpperHFineCoarse
open scoped Classical

/-- Both copies of the overlapping low segment retain H; only high U3 gets Psi. -/
theorem actual_packed_pair_psi_upper {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hε : 0 < ε) (Q : Finset ℝ)
    (hanchor : truncatedSixthLowerAlpha/2 ∈ Q)
    (hQ : ∀ q ∈ Q, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      (U N (1/3) : ℝ) + (U N truncatedSixthLowerSigma : ℝ) ≤
        packed34 Q N δ η Δ +
          (-4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ+ε)*
            truncatedSixthMassScale N := by
  obtain ⟨TL,hTL,hL⟩ := SingleUpperHPacking.low_packing_upper hδ hδhi hη Q hanchor hQ
  obtain ⟨T3,_,h3⟩ := HighSix.U3_high_psi_integral_upper hδ hδhi (half_pos hε)
  obtain ⟨T4,_,h4⟩ := actual_high_classical_upper hδ hδhi (half_pos hε)
  refine ⟨max TL (max T3 T4),hTL.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hΔlo hΔhi
  have hl1 := hL N (by omega) he Δ hΔlo hΔhi (1/3)
  have hl2 := hL N (by omega) he Δ hΔlo hΔhi truncatedSixthLowerSigma
  have hh3 := h3 N (by omega) he
  have hb := SingleUpperClassicalAssembly.original_endpoint_bounds hδ.le
  have hh4 := h4 N (by omega) he truncatedSixthLowerSigma hb.2.1 hb.2.2
  rw [count_split (δ := δ),count_split (δ := δ)]
  change lowCount N δ (1/3) + highCount N δ (1/3) +
    (lowCount N δ truncatedSixthLowerSigma + highCount N δ truncatedSixthLowerSigma) ≤ _
  unfold packed34 highCoefficient
  nlinarith only [hl1,hl2,hh3,hh4]

/-- The same actual pair simultaneously carries the signed low H integral and
local high j6 Psi-delta saving, at the original window and fixed delta. -/
theorem actual_pair_integral_psi_upper {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (U N (1/3) : ℝ)+(U N truncatedSixthLowerSigma : ℝ) ≤
        (Gdelta δ (1/3)+Gdelta δ truncatedSixthLowerSigma-gainH34 δ-
          4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ+ε)*
            truncatedSixthMassScale N := by
  obtain ⟨n,η,hη,TP,hTP,hP⟩ :=
    TruncatedElevenHIntegralCount.packed_pair_integral_upper hδ hδhi (half_pos hε)
  obtain ⟨TU,_,hU⟩ := actual_packed_pair_psi_upper hδ hδhi hη (half_pos hε)
    (fullGrid δ n) (fullGrid_anchor δ n) (fullGrid_legal hδhi n)
  refine ⟨max TP TU,hTP.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hNP := (le_max_left TP TU).trans hN
  have hNU := (le_max_right TP TU).trans hN
  have hlog : 0 < log (N : ℝ) := log_pos (by
    exact_mod_cast (show 1 < N by have := hTP.trans hNP; omega))
  have hpΔ := rpow_pos_of_pos hlog (-4 : ℝ)
  have hp := hP N hNP (1+log (N : ℝ)^(-4 : ℝ)) le_rfl (by linarith)
  have hu := hU N hNU he (1+log (N : ℝ)^(-4 : ℝ)) le_rfl (by linarith)
  linarith only [hp,hu]

end Wu2008DoubleSieve.HighSixLowHJoin
