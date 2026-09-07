import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetLogSaving
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGateSaving

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace G12FlexibleWF

/-- Literal transport of the physical residual, without a new coefficient. -/
theorem residue_linked (N : ℕ) (A : Finset (ℕ × ℕ)) (d : ℕ) :
    G12OutsideBudget.residue N (A.image G12RectangleWF.linkedEmbed) d = residue N A d := by
  unfold G12OutsideBudget.residue G12OutsideBudget.divisibility G12OutsideBudget.mass residue mass
  rw [sum_image, sum_image]
  · rfl
  · exact fun _ _ _ _ h => G12RectangleWF.linkedEmbed_injective h
  · exact fun _ _ _ _ h => G12RectangleWF.linkedEmbed_injective h

theorem outside_linked (N : ℕ) (A : Finset (ℕ × ℕ)) (Z Q : ℝ) (c : ℕ → ℝ) :
    G12OutsideBudget.outside N (A.image G12RectangleWF.linkedEmbed) Z Q c =
      outsidePrimorial N A Z Q c := by
  unfold G12OutsideBudget.outside outsidePrimorial
  simp_rw [residue_linked]

def correctionBudget (N : ℕ) (Q η : ℝ) : ℝ :=
  (800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2 +
    (20*N)*(4/(externalInternalLevel Q η)^(η^2))*(1+Real.log ⌊Q⌋₊)^2

/-- Both actual corrections are paid on the very same full external family. -/
theorem signed_corrections_paid {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (A : Finset (ℕ × ℕ)) (hA : A.image G12RectangleWF.linkedEmbed ⊆ goldbachG12LinkedAtoms N ε)
    (Z Q η : ℝ) (hQ : Q ≤ N) (hD : 2 ≤ externalInternalLevel Q η)
    (hη : 0 < η) (hηu : η < 1/8)
    (hf : ∀ t ∈ externalTags true (goldbachB10SiftingPrimes N Z)
      (externalInternalLevel Q η) η Z,
      WellFactorable (externalTerm true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z t) Q) :
    let S := externalTags true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z
    let c := fun t => externalTerm true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z t
    (∑ t ∈ S, (G12FlexibleRectangle.discrepancy N A (Ioc 0 ⌊Q⌋₊) (c t) -
      G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) (c t) - outsidePrimorial N A Z Q (c t))) ≤
      (∑ t ∈ S, |G12FlexibleRectangle.discrepancy N A (Ioc 0 ⌊Q⌋₊) (c t)|) +
        (S.card : ℝ)*correctionBudget N Q η := by
  dsimp only
  let S := externalTags true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z
  let c := fun t => externalTerm true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z t
  have hg : (∑ t ∈ S, |G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) (c t)|) ≤
      (S.card : ℝ)*((800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2) := by
    calc
      _ ≤ ∑ _t ∈ S, ((800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2) :=
        sum_le_sum fun t ht => G12RectangleGate.gate_wellFactorable hN hQ hA (hf t ht)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have ho := G12OutsideBudget.family_budget hN ε (A.image G12RectangleWF.linkedEmbed)
    hA Z Q η hD hη hηu
  simp_rw [outside_linked] at ho
  have hp : (∑ t ∈ S, (G12FlexibleRectangle.discrepancy N A (Ioc 0 ⌊Q⌋₊) (c t) -
      G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) (c t) - outsidePrimorial N A Z Q (c t))) ≤
      (∑ t ∈ S, |G12FlexibleRectangle.discrepancy N A (Ioc 0 ⌊Q⌋₊) (c t)|) +
      (∑ t ∈ S, |G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) (c t)|) +
      (∑ t ∈ S, |outsidePrimorial N A Z Q (c t)|) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro t _
    linarith only [le_abs_self (G12FlexibleRectangle.discrepancy N A (Ioc 0 ⌊Q⌋₊) (c t)),
      neg_le_abs (G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) (c t)),
      neg_le_abs (outsidePrimorial N A Z Q (c t))]
  unfold correctionBudget
  dsimp only [S,c] at hg hp
  linarith only [hp,hg,ho]

end G12FlexibleWF
