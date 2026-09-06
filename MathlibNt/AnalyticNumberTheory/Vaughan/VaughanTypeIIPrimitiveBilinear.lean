

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIDyadicLedger
import MathlibNt.AnalyticNumberTheory.LargeSieve.BombieriDavenport

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

/-- Raw coefficient energy in the outer variable. -/
def vaughanBilinearCoeffEnergy (α : ℕ → ℂ) (DS : Finset ℕ) : ℝ :=
  ∑ d ∈ DS, ‖α d‖ ^ 2

/-- The consumable tensor energy after the second (`e,m → t`) rearrangement. -/
def vaughanBilinearTensorEnergy
    (β : ℕ → ℂ) (c : ℕ → ℂ) (y : ℕ)
    (DS ES : Finset ℕ) : ℝ :=
  ∑ d ∈ DS, ∑ t ∈ Finset.Icc (1 : ℤ) y,
    ‖vaughanBilinearTensorCoeff β c y d ES t‖ ^ 2

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

/-- Cauchy only in the outer variable, after the packet has become a genuine
one-variable character sum. -/
theorem vaughanBilinearBlockOn_norm_sq_le
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q)
    (hDS : ∀ d ∈ DS, 0 < d) (hES : ∀ e ∈ ES, 0 < e) :
    ‖vaughanBilinearBlockOn α β c y DS ES q χ‖ ^ 2 ≤
      vaughanBilinearCoeffEnergy α DS *
        ∑ d ∈ DS, ‖∑ t ∈ Finset.Icc (1 : ℤ) y,
          vaughanBilinearTensorCoeff β c y d ES t * χ.1 (t : ZMod q)‖ ^ 2 := by
  rw [vaughanBilinearBlockOn_eq_tensor α β c y DS ES q χ hDS hES]
  unfold vaughanBilinearCoeffEnergy
  let I : ℕ → ℂ := fun d => ∑ t ∈ Finset.Icc (1 : ℤ) y,
    vaughanBilinearTensorCoeff β c y d ES t * χ.1 (t : ZMod q)
  have hnorm := norm_sum_le DS (fun d => (α d * χ.1 (d : ZMod q)) * I d)
  have hsq : ‖∑ d ∈ DS, (α d * χ.1 (d : ZMod q)) * I d‖ ^ 2 ≤
      (∑ d ∈ DS, ‖α d * χ.1 (d : ZMod q)‖ * ‖I d‖) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa [norm_mul] using hnorm
  refine hsq.trans ((Finset.sum_mul_sq_le_sq_mul_sq DS
    (fun d => ‖α d * χ.1 (d : ZMod q)‖) (fun d => ‖I d‖)).trans ?_)
  apply mul_le_mul_of_nonneg_right
  · apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, mul_pow]
    have hχ := DirichletCharacter.norm_le_one χ.1 (d : ZMod q)
    have hχsq : ‖χ.1 (d : ZMod q)‖ ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg _) hχ 2
    simpa using mul_le_mul_of_nonneg_left hχsq (sq_nonneg ‖α d‖)
  · positivity

/-- Weighted primitive-character bilinear large sieve over a finite positive
rectangle.  The two energies are kept separate: the raw `d`-coefficient
energy and the character-free `(d,t)` tensor energy. -/
theorem weighted_primitive_vaughanBilinearBlockOn
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y Q : ℕ) (DS ES : Finset ℕ)
    (hQ : 0 < Q) (hDS : ∀ d ∈ DS, 0 < d) (hES : ∀ e ∈ ES, 0 < e) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖vaughanBilinearBlockOn α β c y DS ES q χ‖ ^ 2) ≤
      vaughanBilinearCoeffEnergy α DS *
        vaughanBilinearLargeSieveConstant y Q *
          vaughanBilinearTensorEnergy β c y DS ES := by
  let A : ℝ := vaughanBilinearCoeffEnergy α DS
  let T : ℕ → ℤ → ℂ := fun d t => vaughanBilinearTensorCoeff β c y d ES t
  let S : ℕ → (q : ℕ) → PrimitiveCharacter q → ℝ := fun d q χ =>
    ‖∑ t ∈ Finset.Icc (1 : ℤ) y, T d t * χ.1 (t : ZMod q)‖ ^ 2
  have hA : 0 ≤ A := by
    dsimp [A, vaughanBilinearCoeffEnergy]
    positivity
  have hqBound : ∀ q ∈ Finset.Icc 1 Q,
      (∑ χ : PrimitiveCharacter q,
        ‖vaughanBilinearBlockOn α β c y DS ES q χ‖ ^ 2) ≤
        A * ∑ d ∈ DS, ∑ χ : PrimitiveCharacter q, S d q χ := by
    intro q hq
    calc
      (∑ χ : PrimitiveCharacter q,
          ‖vaughanBilinearBlockOn α β c y DS ES q χ‖ ^ 2) ≤
          ∑ χ : PrimitiveCharacter q, A * ∑ d ∈ DS, S d q χ := by
        apply Finset.sum_le_sum
        intro χ hχ
        simpa [A, T, S] using
          vaughanBilinearBlockOn_norm_sq_le α β c y DS ES q χ hDS hES
      _ = A * ∑ d ∈ DS, ∑ χ : PrimitiveCharacter q, S d q χ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
  have hCauchy :
      (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖vaughanBilinearBlockOn α β c y DS ES q χ‖ ^ 2) ≤
        A * ∑ d ∈ DS, ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q, S d q χ := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            (A * ∑ d ∈ DS, ∑ χ : PrimitiveCharacter q, S d q χ) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left (hqBound q hq)
        positivity
      _ = A * ∑ d ∈ DS, ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q, S d q χ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro χ hχ
        exact mul_left_comm _ _ _
  refine hCauchy.trans ?_
  have hLS : ∀ d ∈ DS,
      (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, S d q χ) ≤
        vaughanBilinearLargeSieveConstant y Q *
          ∑ t ∈ Finset.Icc (1 : ℤ) y, ‖T d t‖ ^ 2 := by
    intro d hd
    simpa [S, T, vaughanBilinearLargeSieveConstant] using
      weighted_primitive_bombieri_davenport (T d) 0 y Q hQ
  calc
    A * ∑ d ∈ DS, ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, S d q χ ≤
      A * ∑ d ∈ DS, vaughanBilinearLargeSieveConstant y Q *
        ∑ t ∈ Finset.Icc (1 : ℤ) y, ‖T d t‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Finset.sum_le_sum fun d hd => hLS d hd
    _ = vaughanBilinearCoeffEnergy α DS *
        vaughanBilinearLargeSieveConstant y Q *
          vaughanBilinearTensorEnergy β c y DS ES := by
      dsimp [A, T]
      unfold vaughanBilinearTensorEnergy
      rw [← Finset.mul_sum]
      ring_nf

/-- Dyadic specialization.  The parameters `D,E,y,Q` remain literal and the
coefficient energies are not replaced by pointwise cardinality bounds. -/
theorem weighted_primitive_vaughanBilinearDyadic
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E Q : ℕ)
    (hQ : 0 < Q) (hD : 0 < D) (hE : 0 < E) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖vaughanBilinearBlockOn α β c y
            (vaughanDyadicBlock D) (vaughanDyadicBlock E) q χ‖ ^ 2) ≤
      vaughanBilinearCoeffEnergy α (vaughanDyadicBlock D) *
        vaughanBilinearLargeSieveConstant y Q *
          vaughanBilinearTensorEnergy β c y
            (vaughanDyadicBlock D) (vaughanDyadicBlock E) := by
  apply weighted_primitive_vaughanBilinearBlockOn α β c y Q
    (vaughanDyadicBlock D) (vaughanDyadicBlock E) hQ
  · intro d hd
    exact hD.trans_le (mem_vaughanDyadicBlock.mp hd).1.le
  · intro e he
    exact hE.trans_le (mem_vaughanDyadicBlock.mp he).1.le

/-- Fully expanded dyadic form: all four physical parameters `D,E,y,Q` and
both coefficient energies remain visible. -/
theorem weighted_primitive_vaughanBilinearDyadic_explicit
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E Q : ℕ)
    (hQ : 0 < Q) (hD : 0 < D) (hE : 0 < E) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖vaughanBilinearBlockOn α β c y
            (vaughanDyadicBlock D) (vaughanDyadicBlock E) q χ‖ ^ 2) ≤
      vaughanBilinearCoeffEnergy α (vaughanDyadicBlock D) *
        ((y : ℝ) +
          (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
            (Q : ℝ) ^ 2) *
          vaughanBilinearTensorEnergy β c y
            (vaughanDyadicBlock D) (vaughanDyadicBlock E) := by
  rw [← vaughanBilinearLargeSieveConstant_eq_explicit y Q hQ]
  exact weighted_primitive_vaughanBilinearDyadic α β c y D E Q hQ hD hE

/-- Canonical-rectangle specialization used by the full Type-II ledger. -/
theorem weighted_primitive_vaughanCanonicalBilinear
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ‖ ^ 2) ≤
      vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
        vaughanBilinearLargeSieveConstant y Q *
          vaughanBilinearTensorEnergy vaughanMangoldtCoeff b y
            (vaughanCanonicalDyadicBlock N u k)
            (vaughanCanonicalDyadicBlock N v l) := by
  change (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖vaughanBilinearBlockOn vaughanMoebiusCoeff vaughanMangoldtCoeff b y
            (vaughanCanonicalDyadicBlock N u k)
            (vaughanCanonicalDyadicBlock N v l) q χ‖ ^ 2) ≤ _
  apply weighted_primitive_vaughanBilinearBlockOn
    vaughanMoebiusCoeff vaughanMangoldtCoeff b y Q
    (vaughanCanonicalDyadicBlock N u k)
    (vaughanCanonicalDyadicBlock N v l) hQ
  · intro d hd
    exact (mem_vaughanCanonicalDyadicBlock.mp hd).1
  · intro e he
    exact (mem_vaughanCanonicalDyadicBlock.mp he).1

end

end AnalyticNumberTheory.LargeSieve
