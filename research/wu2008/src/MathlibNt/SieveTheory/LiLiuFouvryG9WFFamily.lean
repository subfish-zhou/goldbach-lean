import MathlibNt.SieveTheory.LiLiuFouvryG9WFLevel

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- A genuine common external family at each original G9 level, with all
coefficients supplied by the accepted normalized sieve producer. -/
theorem g9WF_external_family_at_level {δ η : ℝ}
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N T : ℝ, N₀ ≤ N → 1 ≤ T → T ≤ N^(1/10 : ℝ) →
      ∀ (upper : Bool) (P : Finset ℕ) (z : ℝ),
      let Q := N^(5/9-δ)/T^(5/9 : ℝ)
      let D := externalInternalLevel Q η
      ((externalTags upper P D η z).card : ℝ) < Real.exp (8*(η⁻¹)^3) ∧
      ∀ t ∈ externalTags upper P D η z,
        SignedWellFactorable 1 Q (fun n => externalTerm upper P D η z t n) := by
  obtain ⟨N₀,hgate⟩ := g9WF_exists_internal_level_gate hδ hδu hη 1
  refine ⟨N₀, ?_⟩
  intro N T hN hT hTup upper P z
  obtain ⟨_,hQ,_,hD,_⟩ := hgate N T hN hT hTup
  refine ⟨(externalTags_card_and_wellFactorable upper P z hD hη hηu).1, ?_⟩
  intro t ht
  exact externalTerm_signedWellFactorable upper P z t (by linarith) hD hη hηu ht

end MathlibNt.SieveTheory.LiLiuPrereqWF
