import MathlibNt.SieveTheory.LiLiuPrereqWFExternalFamily
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFactorConvolution

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The order-one bound includes the zero coefficient. -/
theorem boundedOne_fouvryTau {f : ArithmeticFunction ℝ} (hf : BoundedOne f) :
    ∀ n, |f n| ≤ (fouvryTau 1 n : ℝ) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [fouvryTau]
  · simpa [fouvryTau, ArithmeticFunction.zeta_apply, hn] using hf n

/-- No squarefree mask, coefficient rescaling, or change of real level. -/
theorem wellFactorable_to_signed {f : ArithmeticFunction ℝ} {Q : ℝ}
    (hf : WellFactorable f Q) : SignedWellFactorable 1 Q (fun n => f n) := by
  refine ⟨boundedOne_fouvryTau hf.2.1, ?_⟩
  intro R S hR hS hRS
  obtain ⟨a,b,ha,haR,hb,hbS,hab⟩ := hf.2.2.2 R S hR hS hRS
  refine ⟨(fun n => a n), (fun n => b n), ?_, ?_,
    boundedOne_fouvryTau ha, boundedOne_fouvryTau hb, ?_⟩
  · intro n hn
    exact ⟨Nat.pos_of_ne_zero (by intro hz; subst n; simp at hn), haR n hn⟩
  · intro n hn
    exact ⟨Nat.pos_of_ne_zero (by intro hz; subst n; simp at hn), hbS n hn⟩
  · funext n
    rw [hab, ArithmeticFunction.mul_apply]
    rfl

/-- Actual normalized external family members at the original external level. -/
theorem externalTerm_signedWellFactorable (upper : Bool) (P : Finset ℕ)
    {Q η : ℝ} (z : ℝ) (t : List ℕ) (hQ : 0 ≤ Q)
    (hD : 2 ≤ externalInternalLevel Q η) (hη : 0 < η) (hηsmall : η < 1/8)
    (ht : t ∈ externalTags upper P (externalInternalLevel Q η) η z) :
    SignedWellFactorable 1 Q
      (fun n => externalTerm upper P (externalInternalLevel Q η) η z t n) := by
  have h := (externalTags_card_and_wellFactorable upper P z hD hη hηsmall).2 t ht
  rw [externalInternalLevel_level hQ hη hηsmall] at h
  exact wellFactorable_to_signed h

end MathlibNt.SieveTheory.LiLiuPrereqWF
