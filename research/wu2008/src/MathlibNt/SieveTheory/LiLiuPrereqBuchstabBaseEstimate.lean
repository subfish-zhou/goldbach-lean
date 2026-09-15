import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBase
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction

/-!
# A uniform quantitative base band for actual rough counts

The extra boundary term is essential when `x` is near `y`. The unit and
possible prime square are retained in the exact formula before estimation.
-/

set_option autoImplicit false

namespace LiLiuPrereqBuchstab

theorem primeCutoff_le_primeCounting {x y : ℝ} (hx : 0 ≤ x) (hyx : y ≤ x) :
    Nat.primeCounting' ⌈y⌉₊ ≤ Nat.primeCounting ⌊x⌋₊ := by
  rw [Nat.primeCounting_eq_primeCounting'_succ,
    ← Nat.primesBelow_card_eq_primeCounting', ← Nat.primesBelow_card_eq_primeCounting']
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpy, hp⟩ := Nat.mem_primesBelow.mp hp
  exact Nat.mem_primesBelow.mpr
    ⟨Nat.lt_succ_iff.mpr ((Nat.le_floor_iff hx).mpr ((Nat.lt_ceil.mp hpy).le.trans hyx)), hp⟩

theorem squareCorrection_le_one (x y : ℝ) : squareCorrection x y ≤ 1 := by
  classical
  unfold squareCorrection
  split_ifs <;> omega

theorem roughCount_le_sq_real {x y : ℝ} (hy : 0 ≤ y) (hx1 : 1 ≤ x)
    (hyx : y ≤ x) (hxy : x ≤ y ^ 2) :
    (roughCount x y : ℝ) =
      1 + primePi x - (Nat.primeCounting' ⌈y⌉₊ : ℝ) + squareCorrection x y := by
  rw [roughCount_le_sq_primeCounting hy hx1 hyx hxy]
  push_cast [Nat.cast_sub (primeCutoff_le_primeCounting (by linarith) hyx)]
  unfold primePi
  ring

theorem roughCount_base_error {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ 2) :
    |(roughCount x y : ℝ) - x / Real.log x| ≤
      primeErrorEnvelope y * (x / Real.log x) + 4 * (y / Real.log y) := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx1 : 1 < x := hy1.trans_le hyx
  have hy0 : 0 < y := by linarith
  have hyl := Real.log_pos hy1
  have he := roughCount_le_sq_real hy0.le hx1.le hyx hxy
  have hcut : (Nat.primeCounting' ⌈y⌉₊ : ℝ) ≤ primePi y := by
    unfold primePi
    exact_mod_cast primeCutoff_le_primeCounting hy0.le le_rfl
  have hc := hcut.trans (primePi_le_two_mul hy)
  have hs : (squareCorrection x y : ℝ) ≤ 1 := by
    exact_mod_cast squareCorrection_le_one x y
  have hc0 : (0 : ℝ) ≤ Nat.primeCounting' ⌈y⌉₊ := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ squareCorrection x y := Nat.cast_nonneg _
  have hym : 1 ≤ y / Real.log y := by
    apply (le_div_iff₀ hyl).2
    linarith [Real.log_le_sub_one_of_pos hy0]
  have hdiff : |(roughCount x y : ℝ) - primePi x| ≤ 4 * (y / Real.log y) := by
    apply abs_le.2
    constructor <;> linarith
  calc
    _ ≤ |(roughCount x y : ℝ) - primePi x| + |primePi x - x / Real.log x| :=
      abs_sub_le _ _ _
    _ ≤ 4 * (y / Real.log y) + primeErrorEnvelope y * (x / Real.log x) :=
      add_le_add hdiff (primePi_error_le hy hyx)
    _ = _ := add_comm _ _

theorem base_log_ratio_mem {x y : ℝ} (hy : 1 < y)
    (hyx : y ≤ x) (hxy : x ≤ y ^ 2) :
    1 ≤ Real.log x / Real.log y ∧ Real.log x / Real.log y ≤ 2 := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := hy0.trans_le hyx
  have hyl := Real.log_pos hy
  constructor
  · apply (le_div_iff₀ hyl).2
    simpa using Real.log_le_log hy0 hyx
  · apply (div_le_iff₀ hyl).2
    have h := Real.log_le_log hx0 hxy
    simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem base_buchstab_main_eq {x y : ℝ} (hy : 1 < y)
    (hyx : y ≤ x) (hxy : x ≤ y ^ 2) :
    x * buchstab (Real.log x / Real.log y) / Real.log y = x / Real.log x := by
  obtain ⟨hu1, hu2⟩ := base_log_ratio_mem hy hyx hxy
  rw [buchstab_eq_one_div hu1 hu2]
  have hlx := (Real.log_pos (hy.trans_le hyx)).ne'
  have hly := (Real.log_pos hy).ne'
  field_simp

/-- The `K=2` induction estimate, with a constant independent of `x` and `y`. -/
theorem roughCount_base_buchstab_error {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ 2) :
    |(roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
      primeErrorEnvelope y * (x / Real.log y) + 4 * (y / Real.log y) := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  rw [base_buchstab_main_eq hy1 hyx hxy]
  apply (roughCount_base_error hy hyx hxy).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (primeErrorEnvelope_nonneg y)
  exact div_le_div_of_nonneg_left (by linarith) (Real.log_pos hy1)
    (Real.log_le_log (by linarith) hyx)

end LiLiuPrereqBuchstab