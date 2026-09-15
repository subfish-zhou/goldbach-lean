import U8OptimalCRTJoint

/-! Bounds on the unchanged pair and interval carriers, retaining closed cuts. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct

/-- The square constraint saves a half power in the second coordinate. -/
theorem pair_second_le_sqrt {N : ℕ} {e : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (he : e ≤ 1) : (t.2 : ℝ) ≤ Real.sqrt N := by
  have hd := pairs_data ht
  have h1 : (1 : ℝ) ≤ t.1 := by exact_mod_cast hd.1.one_lt.le
  have hsq : (t.2 : ℝ)^2 ≤ (N : ℝ) := by
    have hcut := hd.2.2.2.2.2.2.2
    push_cast at hcut
    have heN := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)
    nlinarith [sq_nonneg (t.2 : ℝ)]
  exact (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hsq

theorem pairs_card_le_sharp_box (N : ℕ) {e : ℝ} (he : e ≤ 1) :
    ((pairs N e).card : ℝ) ≤ ((N : ℝ)^(1/10 : ℝ)+1)*(Real.sqrt N+1) := by
  have hs : pairs N e ⊆ range (⌊(N : ℝ)^(1/10 : ℝ)⌋₊+1) ×ˢ
      range (⌊Real.sqrt N⌋₊+1) := by
    intro t ht
    have h1 := Nat.le_floor (pairs_data ht).2.2.2.2.1.le
    have h2 := Nat.le_floor (pair_second_le_sqrt ht he)
    exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
  have hc := card_le_card hs
  rw [card_product, card_range, card_range] at hc
  have hcr : ((pairs N e).card : ℝ) ≤
      ((⌊(N : ℝ)^(1/10 : ℝ)⌋₊ : ℝ)+1)*((⌊Real.sqrt N⌋₊ : ℝ)+1) := by exact_mod_cast hc
  apply hcr.trans
  exact mul_le_mul (add_le_add (Nat.floor_le (by positivity)) le_rfl)
    (add_le_add (Nat.floor_le (Real.sqrt_nonneg _)) le_rfl) (by positivity) (by positivity)

/-- A universal payable pair count, rather than the old quadratic box. -/
theorem pairs_card_le_three_fifths {N : ℕ} {e : ℝ} (hN : 1 ≤ N) (he : e ≤ 1) :
    ((pairs N e).card : ℝ) ≤ 4*(N : ℝ)^(3/5 : ℝ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 1 ≤ (N : ℝ)^(1/10 : ℝ) := Real.one_le_rpow hN' (by norm_num)
  have hb : 1 ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.one_le_rpow hN' (by norm_num)
  have heq : (N : ℝ)^(1/10 : ℝ)*Real.sqrt N = (N : ℝ)^(3/5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
    norm_num
  calc
    _ ≤ ((N : ℝ)^(1/10 : ℝ)+1)*(Real.sqrt N+1) := pairs_card_le_sharp_box N he
    _ ≤ (2*(N : ℝ)^(1/10 : ℝ))*(2*Real.sqrt N) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = _ := by nlinarith [heq]

/-- The lower endpoint is positive, so a closed upper endpoint costs no extra one. -/
theorem interval_card_le_cutoff {N : ℕ} {e : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (he : 0 ≤ e) :
    ((interval N e t).card : ℝ) ≤ e*(N : ℝ)/((t.1 : ℝ)*t.2) := by
  classical
  have hd := pairs_data ht
  have hp : (0 : ℝ) < (t.1 : ℝ)*t.2 := by
    exact mul_pos (by exact_mod_cast hd.1.pos) (by exact_mod_cast hd.2.1.pos)
  let X := e*(N : ℝ)/((t.1 : ℝ)*t.2)
  have hs : interval N e t ⊆ Icc 1 ⌊X⌋₊ := by
    intro r hr
    obtain ⟨_,hbr,_,hcut⟩ := mem_filter.mp hr
    have hrX : (r : ℝ) ≤ X := by
      apply (le_div_iff₀ hp).mpr
      push_cast at hcut
      nlinarith
    exact mem_Icc.mpr ⟨hd.2.1.one_lt.le.trans hbr, Nat.le_floor hrX⟩
  have hc : (interval N e t).card ≤ ⌊X⌋₊ := by
    have := card_le_card hs
    simpa using this
  exact (show ((interval N e t).card : ℝ) ≤ ⌊X⌋₊ by exact_mod_cast hc).trans
    (Nat.floor_le (div_nonneg (mul_nonneg he (Nat.cast_nonneg N)) hp.le))

/-- Pair counting is paid for the actual optimized signed CRT remainder. -/
theorem sum_optimal_remainder_bound {N : ℕ} (hNe : Even N) {e R : ℝ}
    (hN : 1 ≤ N) (he : e ≤ 1) (hR : 1 ≤ R) (Z : ℝ) :
    |∑ t ∈ pairs N e, quadraticRemainder N e t (TwoDimensional.carrier Z R)
      (TwoDimensional.optimalWeight N hNe Z R)| ≤
      8*(N : ℝ)^(3/5 : ℝ)*(R+1)^2*R^4 := by
  calc
    _ ≤ ∑ t ∈ pairs N e, |quadraticRemainder N e t (TwoDimensional.carrier Z R)
      (TwoDimensional.optimalWeight N hNe Z R)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ pairs N e, 2*(R+1)^2*R^4 :=
      sum_le_sum fun t _ => optimal_remainder_bound N hNe e Z R t hR
    _ = (pairs N e).card * (2*(R+1)^2*R^4) := by simp
    _ ≤ (4*(N : ℝ)^(3/5 : ℝ)) * (2*(R+1)^2*R^4) :=
      mul_le_mul_of_nonneg_right (pairs_card_le_three_fifths hN he) (by positivity)
    _ = _ := by ring

end U8Literal.SmallProduct
