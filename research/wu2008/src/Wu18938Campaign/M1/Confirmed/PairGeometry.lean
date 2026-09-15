import Wu18938Campaign.M1.Confirmed.ClassicalInputs
import MathlibNt.Wu2008DoubleSieve.MotherPairClassicalUpper

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

structure Geometry (η S U : ℝ) (N : ℕ) (δ : ℝ) (x : Gamma5ClassicalLabel) : Prop where
  product_pos : 0 < gamma5ClassicalProduct x
  product_le : (gamma5ClassicalProduct x : ℝ) ≤ N
  level_gt_one : 1 < gamma5ClassicalLevel N δ x
  cutoff_gt_one : 1 < classicalCutoff S N δ x
  cutoff_le_level : classicalCutoff S N δ x ≤ gamma5ClassicalLevel N δ x
  cutoff_lower : (N : ℝ) ^ (η * min (1 / S) ((1 - 2 * U) / 2)) ≤ classicalCutoff S N δ x
  prime_lower : (N : ℝ) ^ (η / 10) ≤ (x.2.1 : ℝ)
  ratio_lower : 2 ≤ log (gamma5ClassicalLevel N δ x) / log (classicalCutoff S N δ x)
  ratio_upper : log (gamma5ClassicalLevel N δ x) / log (classicalCutoff S N δ x) ≤ 3

theorem geometry {m i N : ℕ} {η δ Δ S U : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hcap : CapAdmissible S U) {x : Gamma5ClassicalLabel}
    (hx : x ∈ capLabels S U N δ (convolutionWuWindows N Δ V)) :
    Geometry η S U N δ x := by
  have hS : 0 < S := by linarith [hcap.three_le_S]
  have hU : 0 < 1 - 2 * U := by linarith [hcap.cap_lt_half]
  obtain ⟨hxambient,hp,hq,_,_,hzp,hpq,hqu⟩ := mem_filter.mp hx
  have hd := (mem_product.mp hxambient).1
  have hg := hb.support_geometry hN hη hδ hd
  let R : ℝ := (N : ℝ) ^ (1 / 2 - δ) / x.1
  let L : ℝ := gamma5ClassicalLevel N δ x
  let z : ℝ := wuLocalCutoff N δ x.1 S
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hR : 1 < R := hg.2.2.1
  have hR0 : 0 < R := by linarith
  have hp0 : (0 : ℝ) < x.2.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < x.2.2 := by exact_mod_cast hq.pos
  have hLdef : L = R / ((x.2.1 : ℝ) * x.2.2) := by
    dsimp [L,R,gamma5ClassicalLevel,gamma5ClassicalProduct]
    push_cast
    ring
  have hpair := classical_pair_geometry hcap hR hp0 hq0 hzp
    (by exact_mod_cast hpq.le) hqu.le
  rw [← hLdef] at hpair
  have hL : 1 < L := (one_lt_rpow hR hU).trans_le hpair.1
  have hz : 1 < z := one_lt_rpow hR (by positivity)
  have hbridge := classical_ratio2_cutoff_bridge hL hz (hpair.2.2.trans (by linarith [hcap.S_le_five]))
  have hM : 0 < gamma5ClassicalProduct x := Nat.mul_pos (Nat.mul_pos hg.1 hp.pos) hq.pos
  have hM0 : (0 : ℝ) < gamma5ClassicalProduct x := by exact_mod_cast hM
  have hMN : (gamma5ClassicalProduct x : ℝ) ≤ N := by
    have hMQ : (gamma5ClassicalProduct x : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) := by
      have hh := (lt_div_iff₀ hM0).mp hL
      linarith
    exact hMQ.trans (by
      simpa only [rpow_one] using
        rpow_le_rpow_of_exponent_le hN1.le (show 1 / 2 - δ ≤ 1 by linarith))
  have hpow (e : ℝ) (he : 0 ≤ e) : (N : ℝ) ^ (η * e) ≤ R ^ e := by
    rw [rpow_mul hN0.le]
    exact rpow_le_rpow (rpow_nonneg hN0.le _) (hb.remaining _ hd) he
  have hcut : (N : ℝ) ^ (η * min (1 / S) ((1 - 2 * U) / 2)) ≤ min z (sqrt L) := by
    apply le_min
    · exact (rpow_le_rpow_of_exponent_le hN1.le
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hη.le)).trans (hpow _ (by positivity))
    · calc
        _ ≤ (N : ℝ) ^ (η * ((1 - 2 * U) / 2)) :=
          rpow_le_rpow_of_exponent_le hN1.le
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hη.le)
        _ ≤ R ^ ((1 - 2 * U) / 2) := hpow _ (by positivity)
        _ = sqrt (R ^ (1 - 2 * U)) := by
          rw [sqrt_eq_rpow,← rpow_mul hR0.le]
          congr 1
          ring
        _ ≤ sqrt L := sqrt_le_sqrt hpair.1
  exact ⟨hM,hMN,hL,hbridge.1,hbridge.2.1,hcut,
    (roughBox_cutoff_lower hb hN hη hδ hd (by linarith [hcap.three_le_S])
      (by linarith [hcap.S_le_five])).trans hzp,hbridge.2.2.2.1,hbridge.2.2.2.2⟩

theorem polynomial_envelope {m i N : ℕ} {η δ Δ S U : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hcap : CapAdmissible S U) {x : Gamma5ClassicalLabel}
    (hx : x ∈ capLabels S U N δ (convolutionWuWindows N Δ V)) :
    ((gamma5ClassicalProduct x * N : ℕ) : ℝ) ≤
      classicalCutoff S N δ x ^ (2 / (η * min (1 / S) ((1 - 2 * U) / 2))) := by
  have hg := geometry hb hN hη hδ hcap hx
  have hζ : 0 < η * min (1 / S) ((1 - 2 * U) / 2) := by
    have hS : 0 < S := by linarith [hcap.three_le_S]
    have hU : 0 < (1 - 2 * U) / 2 := by linarith [hcap.cap_lt_half]
    positivity
  calc
    _ ≤ (N : ℝ) ^ (2 : ℝ) := by
      rw [Nat.cast_mul,rpow_two]
      nlinarith [mul_le_mul_of_nonneg_right hg.product_le (Nat.cast_nonneg N)]
    _ = ((N : ℝ) ^ (η * min (1 / S) ((1 - 2 * U) / 2))) ^
        (2 / (η * min (1 / S) ((1 - 2 * U) / 2))) := by
      have hm : min (1 / S) ((1 - 2 * U) / 2) ≠ 0 := by
        intro hz
        rw [hz,mul_zero] at hζ
        exact lt_irrefl _ hζ
      rw [← rpow_mul (Nat.cast_nonneg N)]
      congr 1
      field_simp [hm]
    _ ≤ _ := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg N) _) hg.cutoff_lower (by positivity)

end Wu18938Campaign.M1.Confirmed.Pair
