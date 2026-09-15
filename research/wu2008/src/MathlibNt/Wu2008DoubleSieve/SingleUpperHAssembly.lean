import MathlibNt.Wu2008DoubleSieve.SingleUpperHIntegral
import MathlibNt.Wu2008DoubleSieve.SingleUpperClassicalAssembly

namespace Wu2008DoubleSieve.SingleUpperHAssembly
open Real MeasureTheory SingleUpperCounts SingleUpperSplice SingleUpperLowPacking
open SingleUpperHSource SingleUpperQuadrature SingleUpperHighQuadrature
open scoped Classical Topology

noncomputable def highCoefficient (δ : ℝ) : ℝ :=
  4*(∫ t in ((1/2-δ)/2)..(1/3 : ℝ), weight δ t/t) +
  4*(∫ t in ((1/2-δ)/2)..truncatedSixthLowerSigma, weight δ t/t)

/-- Both overlapping low segments occur with their original multiplicity. -/
noncomputable def packed34 (Q : Finset ℝ) (N : ℕ) (δ η Δ : ℝ) : ℝ :=
  2*SingleUpperHPacking.packingMass Q N δ η Δ
    (packingStart N δ Δ) (packingSize N δ Δ) +
  highCoefficient δ * truncatedSixthMassScale N

/-- The high contribution is classical; no Psi improvement is asserted. -/
theorem actual_pair_upper {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hε : 0 < ε) (Q : Finset ℝ)
    (hanchor : truncatedSixthLowerAlpha/2 ∈ Q)
    (hQ : ∀ q ∈ Q, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      (U N (1/3) : ℝ) + (U N truncatedSixthLowerSigma : ℝ) ≤
        packed34 Q N δ η Δ + ε*truncatedSixthMassScale N := by
  obtain ⟨TL,hTL,hL⟩ := SingleUpperHPacking.low_packing_upper hδ hδhi hη Q hanchor hQ
  obtain ⟨TH,_,hH⟩ := actual_high_classical_upper hδ hδhi (half_pos hε)
  refine ⟨max TL TH,hTL.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hΔlo hΔhi
  have hb := SingleUpperClassicalAssembly.original_endpoint_bounds hδ.le
  have hl1 := hL N ((le_max_left _ _).trans hN) he Δ hΔlo hΔhi (1/3)
  have hl2 := hL N ((le_max_left _ _).trans hN) he Δ hΔlo hΔhi truncatedSixthLowerSigma
  have hh1 := hH N ((le_max_right _ _).trans hN) he (1/3) hb.1 le_rfl
  have hh2 := hH N ((le_max_right _ _).trans hN) he truncatedSixthLowerSigma hb.2.1 hb.2.2
  rw [count_split (δ := δ),count_split (δ := δ)]
  change lowCount N δ (1/3) + highCount N δ (1/3) +
    (lowCount N δ truncatedSixthLowerSigma + highCount N δ truncatedSixthLowerSigma) ≤ _
  unfold packed34 highCoefficient
  linarith only [hl1,hl2,hh1,hh2]

end Wu2008DoubleSieve.SingleUpperHAssembly
