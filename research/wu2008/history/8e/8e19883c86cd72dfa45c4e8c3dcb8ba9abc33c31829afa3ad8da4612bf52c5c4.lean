import W17AcceptedBudget

noncomputable section
namespace WuTarget.E02JointCredit
open ActualNineFeedback NodeExtension
open scoped BigOperators

def difference (i : Fin 9) : ℝ :=
  W17Accepted.enhanced i - W04Accepted.enhanced i

def addedMatrix (i k : Fin 9) : ℝ :=
  W17Joint.jointMatrix i k - W04.augmentedMatrix i k

theorem increment_nonneg (i : Fin 9) : 0 ≤ W09.increment i := by
  fin_cases i <;> norm_num [W09.increment]

theorem augmented_le_joint (i k : Fin 9) :
    W04.augmentedMatrix i k ≤ W17Joint.jointMatrix i k := by
  have hm := (W04.oldMatrix_le_elementary i k).trans
    (W08.elementaryMatrix_le_paidMatrix i k)
  have hs := W17Joint.rationalSigmaMatrix_nonneg i k
  have hj := W05.jTable_nonneg i k
  have hd := W07.paidMatrix_nonneg i k
  unfold W04.augmentedMatrix W17Joint.jointMatrix W17Joint.remainderMatrix
  linarith only [hm, hs, hj, hd]

theorem addedMatrix_nonneg (i k : Fin 9) : 0 ≤ addedMatrix i k :=
  sub_nonneg.mpr (augmented_le_joint i k)

theorem frozen_subsolution (i : Fin 9) :
    Wu04Bypass.v8 i ≤ Wu04Bypass.v0 i +
      matrixApply W04.augmentedMatrix Wu04Bypass.v8 i := by
  have hr : Wu04Bypass.v8 i ≤ Wu04Bypass.v0 i +
      matrixApply Wu04Bypass.M Wu04Bypass.v8 i := Wu04Bypass.round7 i
  exact hr.trans (add_le_add_left
    (Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_right (W04.oldMatrix_le_augmentedMatrix i k)
        (Wu04Bypass.v8_nonneg k))) _)

theorem previous_eq_update (i : Fin 9) :
    W04Accepted.enhanced i = Wu04Bypass.v0 i +
      matrixApply W04.augmentedMatrix Wu04Bypass.v8 i :=
  max_eq_right (frozen_subsolution i)

theorem seed_eq_old_add_increment (i : Fin 9) :
    W09.seed i = Wu04Bypass.v0 i + W09.increment i := by
  rw [Wu04Bypass.v0_eq_publication]
  exact W09.seed_eq_publication_add_increment i

theorem increment_paid (i : Fin 9) :
    W04Accepted.enhanced i + W09.increment i ≤
      W09.seed i + matrixApply W17Joint.jointMatrix W04Accepted.enhanced i := by
  have ha := matrixApply_mono W17Joint.jointMatrix_nonneg
    W04Accepted.old_le_enhanced i
  have hj : matrixApply W04.augmentedMatrix Wu04Bypass.v8 i ≤
      matrixApply W17Joint.jointMatrix Wu04Bypass.v8 i :=
    Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_right (augmented_le_joint i k)
        (Wu04Bypass.v8_nonneg k))
  rw [previous_eq_update i, seed_eq_old_add_increment i]
  linarith only [ha, hj]

theorem enhanced_eq_update (i : Fin 9) :
    W17Accepted.enhanced i =
      W09.seed i + matrixApply W17Joint.jointMatrix W04Accepted.enhanced i :=
  max_eq_right ((le_add_of_nonneg_right (increment_nonneg i)).trans
    (increment_paid i))

theorem increment_le_difference (i : Fin 9) :
    W09.increment i ≤ difference i := by
  have h := increment_paid i
  rw [← enhanced_eq_update i] at h
  exact le_sub_iff_add_le.mpr (by linarith only [h])

theorem difference_nonneg (i : Fin 9) : 0 ≤ difference i :=
  (increment_nonneg i).trans (increment_le_difference i)

theorem difference_eq (i : Fin 9) :
    difference i = W09.increment i +
      matrixApply W17Joint.jointMatrix
        (fun k => W04Accepted.enhanced k - Wu04Bypass.v8 k) i +
      matrixApply addedMatrix Wu04Bypass.v8 i := by
  unfold difference
  rw [enhanced_eq_update i, seed_eq_old_add_increment i]
  simp only [matrixApply, addedMatrix, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hx := previous_eq_update i
  unfold matrixApply at hx
  linarith only [hx]

theorem difference_remainders_nonneg (i : Fin 9) :
    0 ≤ matrixApply W17Joint.jointMatrix
        (fun k => W04Accepted.enhanced k - Wu04Bypass.v8 k) i ∧
    0 ≤ matrixApply addedMatrix Wu04Bypass.v8 i :=
  ⟨matrixApply_nonneg W17Joint.jointMatrix_nonneg
      (fun k => sub_nonneg.mpr (W04Accepted.old_le_enhanced k)) i,
    matrixApply_nonneg addedMatrix_nonneg Wu04Bypass.v8_nonneg i⟩

end WuTarget.E02JointCredit
