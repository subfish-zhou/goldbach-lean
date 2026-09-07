import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudget

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12OutsideBudget

/-- Original full weights on precisely the reduced non-primorial carrier. -/
def outside (N : ℕ) (A : Finset GoldbachG12LinkedAtom) (Z Q : ℝ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ (reducedModuli (Ioc 0 ⌊Q⌋₊) (N : ℤ)).filter
    (fun d => ¬ d ∣ goldbachB10ProdPrimes N Z), c d * residue N A d

/-- Only the remainder, not the well-factorable coefficient, absorbs coprimality. -/
theorem outside_eq (N : ℕ) (A : Finset GoldbachG12LinkedAtom) (Z Q : ℝ) (c : ℕ → ℝ) :
    outside N A Z Q c =
      ∑ d ∈ (Icc 1 ⌊Q⌋₊).filter (fun d => ¬ d ∣ (goldbachB10SiftingPrimes N Z).prod id),
        c d * (if Int.gcd (N : ℤ) d = 1 then residue N A d else 0) := by
  have hI : Icc 1 ⌊Q⌋₊ = Ioc 0 ⌊Q⌋₊ := by ext d; simp; omega
  rw [hI]
  unfold outside reducedModuli goldbachB10ProdPrimes
  simp only [sum_filter]
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp_all only [mul_zero]

theorem masked_majorant {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (A : Finset GoldbachG12LinkedAtom) (hA : A ⊆ goldbachG12LinkedAtoms N ε)
    (T : ℕ) : ∀ d ∈ Icc 1 T,
      |if Int.gcd (N : ℤ) d = 1 then residue N A d else 0| ≤ (20 * N) / d.totient := by
  intro d hd
  split_ifs
  · exact residue_majorant hN ε A hA (mem_Icc.mp hd).1
  · simp only [abs_zero]
    positivity

/-- Explicit transport payment for any genuine submother; no majorant premise. -/
theorem family_budget {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (A : Finset GoldbachG12LinkedAtom) (hA : A ⊆ goldbachG12LinkedAtoms N ε)
    (Z Q η : ℝ) (hD : 2 ≤ externalInternalLevel Q η)
    (hη : 0 < η) (hηsmall : η < 1/8) :
    (∑ t ∈ externalTags true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z,
      |outside N A Z Q
        (externalTerm true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z t)|) ≤
      ((externalTags true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z).card : ℝ) *
        (20 * N) * (4 / (externalInternalLevel Q η) ^ (η^2)) * (1 + Real.log ⌊Q⌋₊)^2 := by
  simp_rw [outside_eq]
  exact externalUpperFamily_exceptional_remainder_budget (goldbachB10SiftingPrimes N Z)
    Z hD hη hηsmall ⌊Q⌋₊
    (fun d => if Int.gcd (N : ℤ) d = 1 then residue N A d else 0)
    (20 * N) (by positivity) (masked_majorant hN ε A hA _)

/-- Pair cells retain their original coefficient after the canonical embedding. -/
theorem rectangle_residue (N : ℕ) (ε : ℝ) (M T d : ℕ) :
    residue N ((G12LowRectangle.rectangle N ε M T).image G12RectangleWF.linkedEmbed) d =
      G12RectangleWF.residue N ε M T d := by
  unfold residue divisibility mass G12RectangleWF.residue G12RectangleWF.mass
  rw [sum_image, sum_image]
  · rfl
  · exact fun _ _ _ _ h => G12RectangleWF.linkedEmbed_injective h
  · exact fun _ _ _ _ h => G12RectangleWF.linkedEmbed_injective h

theorem rectangle_outside (N : ℕ) (ε Z Q : ℝ) (M T : ℕ) (c : ℕ → ℝ) :
    outside N ((G12LowRectangle.rectangle N ε M T).image G12RectangleWF.linkedEmbed) Z Q c =
      G12RectangleWF.outsidePrimorial N ε Z Q M T c := by
  unfold outside G12RectangleWF.outsidePrimorial
  simp_rw [rectangle_residue]

/-- The literal third term in the accepted dyadic G12 decomposition is paid. -/
theorem rectangle_family_budget {N : ℕ} (hN : 2 ≤ N) (ε Z Q η : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ))
    (hD : 2 ≤ externalInternalLevel Q η) (hη : 0 < η) (hηsmall : η < 1/8) :
    (∑ t ∈ externalTags true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z,
      |G12RectangleWF.outsidePrimorial N ε Z Q M T
        (externalTerm true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z t)|) ≤
      ((externalTags true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z).card : ℝ) *
        (20 * N) * (4 / (externalInternalLevel Q η) ^ (η^2)) * (1 + Real.log ⌊Q⌋₊)^2 := by
  have h := family_budget hN ε _
    (G12RectangleWF.rectangle_image_subset N ε M T hlow hhigh) Z Q η hD hη hηsmall
  simpa only [rectangle_outside] using h

end G12OutsideBudget
