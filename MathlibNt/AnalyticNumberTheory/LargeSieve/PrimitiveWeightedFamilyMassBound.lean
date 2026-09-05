import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanHyperbolicPrimitiveL1

namespace AnalyticNumberTheory.LargeSieve

open Finset

/-- The number of primitive characters modulo a positive `q` is at most Euler's
 totient.  This is the cardinality bound coming directly from the subtype definition. -/
private theorem primitiveCharacter_card_le_totient_mass (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    Fintype.card (PrimitiveCharacter q) ≤
        Fintype.card (DirichletCharacter ℂ q) := Fintype.card_subtype_le _
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

private theorem sum_Icc_one_cast (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ)) = (Q : ℝ) * ((Q : ℝ) + 1) / 2 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ Q + 1), ih]
      push_cast
      ring

/-- A primitive family supported on conductors in `[1,Q]` has weighted mass at
most the triangular number `Q(Q+1)/2`. -/
theorem weightedPrimitiveFamilyMass_le_triangular
    (Q : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 Q) :
    weightedPrimitiveFamilyMass S ≤ (Q : ℝ) * ((Q : ℝ) + 1) / 2 := by
  have hterm : ∀ q ∈ S,
      ((q : ℝ) / (q.totient : ℝ)) * Fintype.card (PrimitiveCharacter q) ≤ (q : ℝ) := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp (hS hq)).1
    have hq0 : 0 < q := by omega
    have htot : 0 < (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ htot).2
    have hcard : (Fintype.card (PrimitiveCharacter q) : ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast primitiveCharacter_card_le_totient_mass q hq0
    nlinarith
  unfold weightedPrimitiveFamilyMass
  calc
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) * Fintype.card (PrimitiveCharacter q)) ≤
        ∑ q ∈ S, (q : ℝ) := by
          exact sum_le_sum fun q hq => hterm q hq
    _ ≤ ∑ q ∈ Icc 1 Q, (q : ℝ) := by
      exact sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.cast_nonneg _)
    _ = (Q : ℝ) * ((Q : ℝ) + 1) / 2 := sum_Icc_one_cast Q

/-- The full conductor interval version of `weightedPrimitiveFamilyMass_le_triangular`. -/
theorem weightedPrimitiveFamilyMass_Icc_le_triangular (Q : ℕ) :
    weightedPrimitiveFamilyMass (Icc 1 Q) ≤
      (Q : ℝ) * ((Q : ℝ) + 1) / 2 := by
  exact weightedPrimitiveFamilyMass_le_triangular Q (Icc 1 Q) (by rfl)

end AnalyticNumberTheory.LargeSieve
