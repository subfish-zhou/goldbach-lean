import Wu18938Campaign.M1.ResidualClassification

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

theorem FourFactorShape.complement_lt_product {N p a b c d : ℕ}
    {z w u v V : ℝ} (h : FourFactorShape N p a b c d z w u v V) :
    ((N - p : ℕ) : ℝ) < w ^ 3 * u := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast h.primeA.pos
  have hb0 : (0 : ℝ) < b := by exact_mod_cast h.primeB.pos
  have hc0 : (0 : ℝ) < c := by exact_mod_cast h.primeC.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast h.primeD.pos
  have hab : (a : ℝ) < b := by exact_mod_cast h.ab
  have hbc : (b : ℝ) < c := by exact_mod_cast h.bc
  have hw0 : 0 < w := hc0.trans h.cw
  have haw : (a : ℝ) < w := hab.trans (hbc.trans h.cw)
  have hbw : (b : ℝ) < w := hbc.trans h.cw
  calc
    ((N - p : ℕ) : ℝ) = (a : ℝ) * b * c * d := by
      rw [h.complement]
      push_cast
      rfl
    _ < w * w * w * u := by
      gcongr
      exact h.cw
      exact h.du
    _ = w ^ 3 * u := by ring

theorem fourFactor_card_le_ceiling (N : ℕ) (z w u v V : ℝ) :
    (fourFactorIndices N z w u v V).card ≤ ⌈w ^ 3 * u⌉₊ := by
  have hsub : fourFactorIndices N z w u v V ⊆
      (primeIndices N).filter (fun p => N - p ∈ range ⌈w ^ 3 * u⌉₊) := by
    intro p hp
    obtain ⟨a, b, c, d, h⟩ := (mem_filter.mp hp).2
    exact mem_filter.mpr ⟨mem_primeIndices.mpr ⟨h.indexBound, h.primeIndex⟩,
      mem_range.mpr (Nat.lt_ceil.mpr h.complement_lt_product)⟩
  exact (card_le_card hsub).trans
    ((primeComplement_filter_card_le N (range ⌈w ^ 3 * u⌉₊)).trans_eq (card_range _))

theorem fourFactor_residual_lt_product (N : ℕ) (z v V : ℝ)
    {w u : ℝ} (hw : 0 ≤ w) (hu : 0 ≤ u) :
    ((∑ p ∈ fourFactorIndices N z w u v V,
      (pointExcess N p z w u V - pointGains N p z w u v) : ℤ) : ℝ) <
      w ^ 3 * u + 1 := by
  rw [fourFactor_residual_sum, Int.cast_natCast]
  exact (Nat.cast_le.mpr (fourFactor_card_le_ceiling N z w u v V)).trans_lt
    (Nat.ceil_lt_add_one (mul_nonneg (pow_nonneg hw _) hu))

theorem source_fourFactor_residual_lt {N : ℕ} (hN : 0 < N) (κ₁ κ₂ : ℝ) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    ((∑ p ∈ fourFactorIndices N z w u v V,
      (pointExcess N p z w u V - pointGains N p z w u v) : ℤ) : ℝ) <
      (N : ℝ) ^ (1 / 2 - 3 * κ₁ + 3 * κ₂) + 1 := by
  dsimp only
  have h := fourFactor_residual_lt_product N ((N : ℝ) ^ κ₁)
    ((N : ℝ) ^ (1 / 3 : ℝ)) ((N : ℝ) ^ (1 / 2 - 2 * κ₁))
    (Real.rpow_nonneg (Nat.cast_nonneg N) κ₂)
    (Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 2 - 3 * κ₁))
  have he : ((N : ℝ) ^ κ₂) ^ (3 : ℕ) *
      (N : ℝ) ^ (1 / 2 - 3 * κ₁) =
      (N : ℝ) ^ (1 / 2 - 3 * κ₁ + 3 * κ₂) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N),
      ← Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N)]
    congr 1
    norm_num
    ring
  rwa [he] at h

theorem source_fourFactor_residual_paid {N : ℕ} (hN : 1 ≤ N)
    {κ₁ κ₂ : ℝ} (hκ₁ : κ₁ ≤ 1) (hsize : 3 * κ₂ - 2 * κ₁ ≤ 1 / 2) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    ((∑ p ∈ fourFactorIndices N z w u v V,
      (pointExcess N p z w u V - pointGains N p z w u v) : ℤ) : ℝ) ≤
      2 * (N : ℝ) ^ (1 - κ₁) := by
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : 1 / 2 - 3 * κ₁ + 3 * κ₂ ≤ 1 - κ₁ := by linarith
  have he := Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hone : 1 ≤ (N : ℝ) ^ (1 - κ₁) :=
    Real.one_le_rpow hbase (sub_nonneg.mpr hκ₁)
  have h := source_fourFactor_residual_lt (by omega : 0 < N) κ₁ κ₂
  dsimp only at h ⊢
  linarith

theorem source_residual_fourFactor_paid {N : ℕ} (hN : 1 ≤ N)
    {κ₁ κ₂ : ℝ} (hκ₁ : κ₁ ≤ 1) (hsize : 3 * κ₂ - 2 * κ₁ ≤ 1 / 2) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (quotientExcess N z w u V : ℝ) - quotientAssemblyGains N z w u v ≤
      2 * (N : ℝ) ^ (1 - κ₁) +
      ((∑ p ∈ range (N + 1) \ fourFactorIndices N z w u v V,
        (pointExcess N p z w u V - pointGains N p z w u v) : ℤ) : ℝ) -
      (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) -
      (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) := by
  have h := source_fourFactor_residual_paid hN hκ₁ hsize
  dsimp only at h ⊢
  rw [fourFactor_residual_sum, Int.cast_natCast] at h
  rw [full_residual_classified]
  linarith

theorem original_parameters_do_not_force_size_condition :
    let κ₁ : ℝ := 1 / 18
    let κ₂ : ℝ := 1 / 4
    1 / 18 ≤ κ₁ ∧ κ₁ < κ₂ ∧
      3 * κ₁ + κ₂ < 1 / 2 ∧ 3 * κ₁ - κ₂ < 1 / 6 ∧
      ¬(3 * κ₂ - 2 * κ₁ ≤ 1 / 2) := by
  norm_num

end Wu18938Campaign.M1
