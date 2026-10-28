

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIDyadicLedger

/-!
 # Primitive-character bilinear large sieve for Vaughan Type II rectangles

The inner `e,m` packet is first collected by the product `t=e*m`.  Its
coefficient is independent of the character, so the weighted primitive
Bombieri--Davenport inequality can be applied for each outer `d`.  Cauchy is
used only in `d`; no coefficient is ever repackaged and squared by `n=d*e*m`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- The character-free tensor coefficient obtained by collecting all pairs
`(e,m)` in the inner packet with product `t=e*m`. -/
def vaughanBilinearTensorCoeff
    (β : ℕ → ℂ) (c : ℕ → ℂ) (y d : ℕ) (ES : Finset ℕ) (t : ℤ) : ℂ :=
  ∑ e ∈ ES, ∑ m ∈ Finset.Icc 1 (y / (d * e)),
    if ((e * m : ℕ) : ℤ) = t then β e * c (d * t.toNat) else 0


/-- A bilinear rectangle over arbitrary positive finite `d` and `e` supports. -/
def vaughanBilinearBlockOn
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ DS, (α d * χ.1 (d : ZMod q)) *
    ∑ e ∈ ES, (β e * χ.1 (e : ZMod q)) *
      ∑ m ∈ Finset.Icc 1 (y / (d * e)),
        c (d * e * m) * χ.1 (m : ZMod q)

/-- Exact second rearrangement of the inner packet.  The right-hand
coefficients contain no occurrence of `χ`. -/
theorem vaughanBilinearInner_eq_tensor
    (β : ℕ → ℂ) (c : ℕ → ℂ) (y d : ℕ) (ES : Finset ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q) (hd : 0 < d)
    (hES : ∀ e ∈ ES, 0 < e) :
    (∑ e ∈ ES, (β e * χ.1 (e : ZMod q)) *
        ∑ m ∈ Finset.Icc 1 (y / (d * e)),
          c (d * e * m) * χ.1 (m : ZMod q)) =
      ∑ t ∈ Finset.Icc (1 : ℤ) y,
        vaughanBilinearTensorCoeff β c y d ES t * χ.1 (t : ZMod q) := by
  unfold vaughanBilinearTensorCoeff
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hepos : 0 < e := hES e he
  have hde : 0 < d * e := Nat.mul_pos hd hepos
  have hmI := Finset.mem_Icc.mp hm
  have hem_le : e * m ≤ y := by
    have hdem : d * e * m ≤ y := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (Nat.le_div_iff_mul_le hde).mp hmI.2
    exact (Nat.le_mul_of_pos_left (e * m) hd).trans
      (by simpa [mul_assoc] using hdem)
  have hem_pos : 0 < e * m := Nat.mul_pos hepos hmI.1
  have hsingle :
      (∑ t ∈ Finset.Icc (1 : ℤ) y,
        (if ((e * m : ℕ) : ℤ) = t then β e * c (d * t.toNat) else 0) *
          χ.1 (t : ZMod q)) =
        (β e * c (d * (e * m))) * χ.1 ((e * m : ℕ) : ZMod q) := by
    have hem_mem : ((e * m : ℕ) : ℤ) ∈ Finset.Icc (1 : ℤ) y :=
      Finset.mem_Icc.mpr
        ⟨by exact_mod_cast hem_pos, by exact_mod_cast hem_le⟩
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos hem_mem]
    simp only [Int.toNat_natCast, Int.cast_natCast]
  rw [hsingle]
  rw [show ((e * m : ℕ) : ZMod q) =
    (e : ZMod q) * (m : ZMod q) by simp only [Nat.cast_mul], map_mul]
  ring_nf

/-- Whole-block tensor form, obtained before any analytic estimate. -/
theorem vaughanBilinearBlockOn_eq_tensor
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q)
    (hDS : ∀ d ∈ DS, 0 < d) (hES : ∀ e ∈ ES, 0 < e) :
    vaughanBilinearBlockOn α β c y DS ES q χ =
      ∑ d ∈ DS, (α d * χ.1 (d : ZMod q)) *
        ∑ t ∈ Finset.Icc (1 : ℤ) y,
          vaughanBilinearTensorCoeff β c y d ES t * χ.1 (t : ZMod q) := by
  unfold vaughanBilinearBlockOn
  apply Finset.sum_congr rfl
  intro d hd
  rw [vaughanBilinearInner_eq_tensor β c y d ES q χ (hDS d hd) hES]

/-- The primitive-character large-sieve constant at physical packet length
`y` and conductor cap `Q`. -/
def vaughanBilinearLargeSieveConstant (y Q : ℕ) : ℝ :=
  largeSieveBound y (1 / (Q : ℝ) ^ 2)

/-- Expanded physical constant inherited from the reduced-Farey large sieve. -/
theorem vaughanBilinearLargeSieveConstant_eq_explicit
    (y Q : ℕ) (hQ : 0 < Q) :
    vaughanBilinearLargeSieveConstant y Q =
      (y : ℝ) +
        (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2 := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hOneDiv : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by
    field_simp [hQr]
  have hDivide (x : ℝ) : x / (1 / (Q : ℝ) ^ 2) = x * (Q : ℝ) ^ 2 := by
    field_simp [hQr]
  unfold vaughanBilinearLargeSieveConstant largeSieveBound
  rw [hOneDiv, hDivide]


end

end AnalyticNumberTheory.LargeSieve
