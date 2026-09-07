import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainJointSubpower
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainNonzeroReindex

/-! # Arithmetic on the difference-preserving main carrier

The common index remains part of the carrier. In particular its two forbidden
diagonals are never reintroduced when either arithmetic mean is applied.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def mainRestrictedU (d n m m' : ℕ) (h : ℤ) : ℤ :=
  h * m' * ((d : ℤ) * n - m)

def mainRestrictedMax (a : ℤ) (d N M H S : ℕ) : ℕ :=
  2 * a.natAbs * H * M * (d * N + M) * S

theorem mainRestricted_numerator (d n m m' s s' : ℕ) (a h h' : ℤ) :
    iv3CorrelationNumerator d n m m' s s' a h h' =
      mainJointNumerator a (mainRestrictedU d n m m' h)
        (mainRestrictedU d n m' m h') s s' := by
  unfold iv3CorrelationNumerator mainJointNumerator mainRestrictedU
  ring

theorem mainRestrictedU_ne_zero {d n m m' : ℕ} {h : ℤ}
    (hh : h ≠ 0) (hm' : 0 < m') (hd : (d : ℤ) * n - m ≠ 0) :
    mainRestrictedU d n m m' h ≠ 0 :=
  mul_ne_zero (mul_ne_zero hh (by exact_mod_cast hm'.ne')) hd

theorem mainRestrictedU_abs_le {d n m m' N M H : ℕ} {h : ℤ}
    (hn : n ≤ N) (hm : m ≤ M) (hm' : m' ≤ M) (hh : h.natAbs ≤ H) :
    (mainRestrictedU d n m m' h).natAbs ≤ H * M * (d * N + M) := by
  have hd : ((d : ℤ) * n - m).natAbs ≤ d * N + M := by
    calc
      _ ≤ ((d : ℤ) * n).natAbs + (m : ℤ).natAbs := Int.natAbs_sub_le _ _
      _ = d * n + m := by simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left d hn) hm
  simpa only [mainRestrictedU, Int.natAbs_mul, Int.natAbs_natCast] using
    Nat.mul_le_mul (Nat.mul_le_mul hh hm') hd

theorem mainRestricted_joint_scale_le {d n m m' N M H S : ℕ} {a h h' : ℤ}
    (hn : n ≤ N) (hm : m ≤ M) (hm' : m' ≤ M)
    (hh : h.natAbs ≤ H) (hh' : h'.natAbs ≤ H) :
    a.natAbs * ((mainRestrictedU d n m m' h).natAbs +
      (mainRestrictedU d n m' m h').natAbs) * S ≤ mainRestrictedMax a d N M H S := by
  calc
    _ ≤ a.natAbs * (H * M * (d * N + M) + H * M * (d * N + M)) * S :=
      Nat.mul_le_mul_right S (Nat.mul_le_mul_left _ (Nat.add_le_add
        (mainRestrictedU_abs_le hn hm hm' hh) (mainRestrictedU_abs_le hn hm' hm hh')))
    _ = _ := by unfold mainRestrictedMax; ring

theorem mainRestricted_constant_le {d m m' s s' N M H S : ℕ} {a h h' : ℤ}
    (hm : m ≤ M) (hm' : m' ≤ M) (hs : s ≤ S) (hs' : s' ≤ S)
    (hh : h.natAbs ≤ H) (hh' : h'.natAbs ≤ H) :
    (iv3MainConstant m m' s s' a h h').natAbs ≤ mainRestrictedMax a d N M H S := by
  have hd : (h' * s - h * s').natAbs ≤ H * S + H * S :=
    (Int.natAbs_sub_le _ _).trans (by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
        Nat.add_le_add (Nat.mul_le_mul hh' hs) (Nat.mul_le_mul hh hs'))
  calc
    _ ≤ a.natAbs * M * M * (H * S + H * S) := by
      simpa only [iv3MainConstant, Int.natAbs_mul, Int.natAbs_natCast] using
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hm) hm') hd
    _ = 2 * a.natAbs * H * M * M * S := by ring
    _ ≤ _ := Nat.mul_le_mul_right S
      (Nat.mul_le_mul_left _ (Nat.le_add_left M (d * N)))

/-- The arithmetic assumptions on an arbitrary finite seven-coordinate
carrier. Actual Gram membership will supply every conjunct. -/
def mainRestrictedData (d : ℕ) (a : ℤ) (N M S : ℕ) (H : Finset ℤ)
    (v : WGramSecondaryBase) : Prop :=
  v.1 ∈ Ioc 0 N ∧
  v.2.1.1 ∈ Ioc 0 M ∧ v.2.2.1 ∈ Ioc 0 M ∧
  v.2.1.2.1 ∈ Ioc 0 S ∧ v.2.2.2.1 ∈ Ioc 0 S ∧
  v.2.1.2.2 ∈ H ∧ v.2.2.2.2 ∈ H ∧
  (d : ℤ) * v.1 - v.2.1.1 ≠ 0 ∧ (d : ℤ) * v.1 - v.2.2.1 ≠ 0 ∧
  v.2.2.2.2 * v.2.1.2.1 ≠ v.2.1.2.2 * v.2.2.2.1 ∧
  iv3CorrelationNumerator d v.1 v.2.1.1 v.2.2.1 v.2.1.2.1 v.2.2.2.1
    a v.2.1.2.2 v.2.2.2.2 ≠ 0

/-- Summation over an image fiber keeps all ordered coordinates. -/
theorem mainRestricted_sum_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : Finset α) (π : α → β) (f : α → ℝ) :
    ∑ v ∈ G, f v = ∑ b ∈ G.image π, ∑ v ∈ G.filter (fun v => π v = b), f v :=
  (sum_fiberwise_of_maps_to (fun v hv => mem_image.mpr ⟨v, hv, rfl⟩) f).symm

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
