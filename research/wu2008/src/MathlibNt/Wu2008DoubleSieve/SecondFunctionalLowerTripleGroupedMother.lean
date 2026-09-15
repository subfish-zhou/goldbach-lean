import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleGroupedActual
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9IntegralMother

namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighSourcePayload
open scoped Classical

/-- Split the literal remaining ledger, without removing cross-Gamma multiplicities. -/
theorem lowerTriple_remaining_ledger (F : ℕ → ℝ) :
    (∑ j ∈ (Icc 5 15).erase 9, F j) =
      (∑ j ∈ Icc 5 8, F j) + (F 10+F 11+F 12+F 13+F 14+F 15) := by
  have hs : (Icc 5 15 : Finset ℕ).erase 9 = Icc 5 8 ∪ Icc 10 15 := by
    ext j
    simp only [mem_erase, mem_Icc, mem_union]
    omega
  have hd : Disjoint (Icc 5 8 : Finset ℕ) (Icc 10 15) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [mem_Icc] at hj hk
    omega
  rw [hs, sum_union hd]
  congr 1
  norm_num [Finset.sum_Icc_succ_top]

/-- Six separate physical source envelopes enter the actual five-Phi bound.
No density is assumed and no additional epsilon is spent. -/
theorem secondFunctional_lower_triple_grouped_mother
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S +
            (2/(1-2*δ))*omega3XIntegralEnvelope p.kappa3 p.kappa1 + ε) *
              boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) +
          (∑ j ∈ Icc 5 8, secondFunctionalMotherGammaSum p N δ
            (convolutionWuWindows N Δ V) j) +
          (∑ j : Fin 6, (LowerTripleGrouped.sourceFamily N δ Δ V p j).primeMass) +
          (2/(1-2*δ))*secondFunctionalCombinedTheta N δ Δ V p := by
  obtain ⟨T,hT,hbase⟩ := secondFunctional_gamma9_integral_mother p hp hs hs3 hS hS5
    k hk hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN he i Δ V hb
  have h := hbase N hN he i Δ V hb
  have hN4 : 4 ≤ N := hT.trans hN
  have hd : δ < 1/2 := by linarith
  have h10 := LowerTripleGrouped.gamma10_source_upper hN4 he hδ hd hb p hp
  have h11 := LowerTripleGrouped.gamma11_source_upper hN4 he hδ hd hb p hp
  have h12 := LowerTripleGrouped.gamma12_source_upper hN4 he hδ hd hb p hp
  have h13 := LowerTripleGrouped.gamma13_source_upper hN4 he hδ hd hb p hp
  have h14 := LowerTripleGrouped.gamma14_source_upper hN4 he hδ hd hb p hp
  have h15 := LowerTripleGrouped.gamma15_source_upper hN4 he hδ hd hb p hp
  rw [lowerTriple_remaining_ledger] at h
  have hf (F : Fin 6 → ℝ) : (∑ j, F j) =
      F 0 + (F 1 + (F 2 + (F 3 + (F 4 + F 5)))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  rw [hf]
  linarith only [h, h10, h11, h12, h13, h14, h15]

end Wu2008DoubleSieve
