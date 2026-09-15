import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainJointMean
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryZeroModeBound

/-!
# Uniform subpower payment of the joint gcd mean

The constant is chosen before all three signed coefficients and the scale.
Zero numerators are excluded by the support, not charged as ordinary rows.
There is no coprimality hypothesis on either original summation variable.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The divisor-weighted joint mean, with a constant depending only on
the positive exponent. This includes empty supports and the zero scale. -/
theorem mainJoint_mean_subpower {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a U V : ℤ) (S : ℕ) (P : Finset (ℕ × ℕ)),
      a ≠ 0 → U ≠ 0 → V ≠ 0 →
      (∀ p ∈ P, (0 < p.1 ∧ p.1 ≤ S) ∧ (0 < p.2 ∧ p.2 ≤ S) ∧
        mainJointNumerator a U V p.1 p.2 ≠ 0) →
      (∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ) *
        fouvryTau 2 (mainJointNumerator a U V p.1 p.2).natAbs) ≤
        C * (S : ℝ) ^ 2 * (1 + Real.log S) *
          ((a.natAbs * (U.natAbs + V.natAbs) * S : ℕ) : ℝ) ^ δ := by
  obtain ⟨C₀, hC₀, hτ⟩ := fouvryTau_le_const_rpow (k := 2) (by omega)
    (show 0 < δ / 4 by positivity)
  refine ⟨2 * C₀ ^ 4, by positivity, fun a U V S P ha hU hV hP => ?_⟩
  obtain rfl | hS := eq_or_ne S 0
  · have hPe : P = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have := (hP p hp).1
      omega
    simp [hPe]
  have hSpos : 0 < S := Nat.pos_of_ne_zero hS
  let L := a.natAbs * (U.natAbs + V.natAbs) * S
  let T := C₀ * (L : ℝ) ^ (δ / 4)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have henv (n : ℕ) (hn : 0 < n) (hnL : n ≤ L) :
      (fouvryTau 2 n : ℝ) ≤ T := by
    exact (hτ n hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnL)
        (by positivity : 0 ≤ δ / 4)) hC₀.le)
  have hAU : (a * U).natAbs ≤ L := by
    rw [Int.natAbs_mul]
    exact (Nat.mul_le_mul_left a.natAbs (Nat.le_add_right U.natAbs V.natAbs)).trans
      (Nat.le_mul_of_pos_right _ hSpos)
  have hAV : (a * V).natAbs ≤ L := by
    rw [Int.natAbs_mul]
    exact (Nat.mul_le_mul_left a.natAbs (Nat.le_add_left V.natAbs U.natAbs)).trans
      (Nat.le_mul_of_pos_right _ hSpos)
  have hτAU := henv (a * U).natAbs
    (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (mul_ne_zero ha hU))) hAU
  have hτAV := henv (a * V).natAbs
    (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (mul_ne_zero ha hV))) hAV
  have hlog : 0 ≤ 1 + Real.log (S : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hSpos : (1 : ℝ) ≤ S)
    linarith
  have hpower : ((L : ℝ) ^ (δ / 4)) ^ 4 = (L : ℝ) ^ δ := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg L)]
    congr 1
    norm_num
  calc
    _ ≤ 2 * (S : ℝ) ^ 2 * (fouvryTau 2 (a * U).natAbs : ℝ) *
        fouvryTau 2 (a * V).natAbs * T ^ 2 * (1 + Real.log S) :=
      mainJoint_mean_envelope ha hU hV hSpos hT henv P hP
    _ ≤ 2 * (S : ℝ) ^ 2 * T * T * T ^ 2 * (1 + Real.log S) := by gcongr
    _ = 2 * (S : ℝ) ^ 2 * T ^ 4 * (1 + Real.log S) := by ring
    _ = _ := by
      dsimp only [T]
      rw [mul_pow, hpower]
      ring

private theorem joint_unweighted_le (a U V : ℤ) (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, mainJointNumerator a U V p.1 p.2 ≠ 0) :
    (∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ)) ≤
      ∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ) *
        fouvryTau 2 (mainJointNumerator a U V p.1 p.2).natAbs := by
  apply sum_le_sum
  intro p hp
  apply le_mul_of_one_le_right (by positivity)
  exact_mod_cast one_le_fouvryTau_succ 1 (Int.natAbs_ne_zero.mpr (hP p hp))

/-- The same joint mean without the optional divisor weight. -/
theorem mainJoint_mean_unweighted_subpower {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a U V : ℤ) (S : ℕ) (P : Finset (ℕ × ℕ)),
      a ≠ 0 → U ≠ 0 → V ≠ 0 →
      (∀ p ∈ P, (0 < p.1 ∧ p.1 ≤ S) ∧ (0 < p.2 ∧ p.2 ≤ S) ∧
        mainJointNumerator a U V p.1 p.2 ≠ 0) →
      (∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ)) ≤
        C * (S : ℝ) ^ 2 * (1 + Real.log S) *
          ((a.natAbs * (U.natAbs + V.natAbs) * S : ℕ) : ℝ) ^ δ := by
  obtain ⟨C, hC, hbound⟩ := mainJoint_mean_subpower hδ
  refine ⟨C, hC, fun a U V S P ha hU hV hP => ?_⟩
  exact (joint_unweighted_le a U V P (fun p hp => (hP p hp).2.2)).trans
    (hbound a U V S P ha hU hV hP)

/-- The full positive rectangle, with only its zero numerators removed.
Both the weighted and unweighted estimates use the same uniform constant. -/
theorem mainJoint_rectangular_subpower {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a U V : ℤ) (S : ℕ),
      a ≠ 0 → U ≠ 0 → V ≠ 0 →
      let P := ((Ioc 0 S) ×ˢ (Ioc 0 S)).filter
        (fun p : ℕ × ℕ => mainJointNumerator a U V p.1 p.2 ≠ 0)
      let B := C * (S : ℝ) ^ 2 * (1 + Real.log S) *
        ((a.natAbs * (U.natAbs + V.natAbs) * S : ℕ) : ℝ) ^ δ
      (∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ) *
        fouvryTau 2 (mainJointNumerator a U V p.1 p.2).natAbs) ≤ B ∧
      (∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ)) ≤ B := by
  obtain ⟨C, hC, hbound⟩ := mainJoint_mean_subpower hδ
  refine ⟨C, hC, fun a U V S ha hU hV => ?_⟩
  dsimp only
  let P := ((Ioc 0 S) ×ˢ (Ioc 0 S)).filter
    (fun p : ℕ × ℕ => mainJointNumerator a U V p.1 p.2 ≠ 0)
  have hP (p : ℕ × ℕ) (hp : p ∈ P) :
      (0 < p.1 ∧ p.1 ≤ S) ∧ (0 < p.2 ∧ p.2 ≤ S) ∧
        mainJointNumerator a U V p.1 p.2 ≠ 0 := by
    obtain ⟨hpbox, hn⟩ := mem_filter.mp hp
    obtain ⟨hs, ht⟩ := mem_product.mp hpbox
    exact ⟨mem_Ioc.mp hs, mem_Ioc.mp ht, hn⟩
  have hb := hbound a U V S P ha hU hV hP
  exact ⟨hb, (joint_unweighted_le a U V P (fun p hp => (hP p hp).2.2)).trans hb⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
