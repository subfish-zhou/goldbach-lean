import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridRectangle

open scoped BigOperators
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- The rectangular long labels. There is deliberately no short variable, curved
cutoff, or coprimality condition on the second prime. -/
def fouvryG9LongLabels (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)) ×ˢ (range (N + 1))).filter fun z =>
    z.1.Prime ∧ z.2.Prime ∧ z.1.Coprime N ∧
    (N : ℝ) ^ (1/3 : ℝ) ≤ z.1 ∧
    ρ ^ k.2.1 ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) < ρ ^ (k.2.1 + 1) ∧
    ρ ^ k.2.2 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) < ρ ^ (k.2.2 + 1)

/-- Distinct products; multiplicities remain in `fouvryG9LongAlpha`. -/
def fouvryG9LongProducts (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : Finset ℕ :=
  (fouvryG9LongLabels N ρ k).image fun z => z.1 * z.2

/-- A rectangular coefficient independent of the short coordinate. -/
def fouvryG9LongAlpha (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (m : ℕ) : ℝ :=
  (((fouvryG9LongLabels N ρ k).filter fun z => z.1 * z.2 = m).card : ℝ)

theorem fouvryG9LongAlpha_nonneg (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (m : ℕ) :
    0 ≤ fouvryG9LongAlpha N ρ k m := by
  unfold fouvryG9LongAlpha
  positivity

theorem fouvryG9LongAlpha_le_divisors (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (m : ℕ) :
    fouvryG9LongAlpha N ρ k m ≤ (m.divisors.card : ℝ) := by
  classical
  unfold fouvryG9LongAlpha
  apply Nat.cast_le.mpr
  apply card_le_card_of_injOn (fun z => z.1)
  · intro z hz
    obtain ⟨hz, he⟩ := mem_filter.mp hz
    have hp := (mem_filter.mp hz).2
    apply Nat.mem_divisors.mpr
    refine ⟨he ▸ dvd_mul_right z.1 z.2, ?_⟩
    exact he ▸ Nat.ne_of_gt (Nat.mul_pos hp.1.pos hp.2.1.pos)
  · intro x hx y hy he
    obtain ⟨hx, hxm⟩ := mem_filter.mp hx
    obtain ⟨_, hym⟩ := mem_filter.mp hy
    have hs := (mem_filter.mp hx).2.1.pos
    apply Prod.ext he
    apply Nat.eq_of_mul_eq_mul_left hs
    change x.1 = y.1 at he
    calc
      x.1 * x.2 = m := hxm
      _ = y.1 * y.2 := hym.symm
      _ = x.1 * y.2 := by rw [he]

/-- Neither the short label nor even its grid index enters the long coefficient. -/
theorem fouvryG9LongAlpha_firstIndex_eq (N : ℕ) (ρ : ℝ) (i i' j l m : ℕ) :
    fouvryG9LongAlpha N ρ (i, j, l) m = fouvryG9LongAlpha N ρ (i', j, l) m := rfl

/-- The full divisor-bound contract, including the ordered-divisor normalization. -/
theorem fouvryG9LongAlpha_bounds (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (m : ℕ) :
    0 ≤ fouvryG9LongAlpha N ρ k m ∧
    fouvryG9LongAlpha N ρ k m ≤ (m.divisors.card : ℝ) ∧
    (m.divisors.card : ℝ) = (fouvryTau 2 m : ℝ) := by
  exact ⟨fouvryG9LongAlpha_nonneg N ρ k m,
    fouvryG9LongAlpha_le_divisors N ρ k m, by rw [fouvryTau_two]⟩

/-- Regrouping preserves every ordered prime label, for arbitrary signed kernels. -/
theorem fouvryG9Long_sum (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
    (F : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ z ∈ fouvryG9LongLabels N ρ k, F n (z.1 * z.2)) =
      ∑ m ∈ fouvryG9LongProducts N ρ k, fouvryG9LongAlpha N ρ k m * F n m := by
  classical
  have h := sum_fiberwise_of_maps_to
    (s := fouvryG9LongLabels N ρ k) (t := fouvryG9LongProducts N ρ k)
    (g := fun z : ℕ × ℕ => z.1 * z.2)
    (fun z hz => mem_image_of_mem (fun z : ℕ × ℕ => z.1 * z.2) hz)
    (fun z => F n (z.1 * z.2))
  rw [← h]
  apply sum_congr rfl
  intro m hm
  calc
    _ = ∑ _z ∈ (fouvryG9LongLabels N ρ k).filter (fun z => z.1 * z.2 = m), F n m := by
      apply sum_congr rfl
      intro z hz
      rw [(mem_filter.mp hz).2]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, fouvryG9LongAlpha]

/-- The support is a genuine rectangular long interval. -/
theorem fouvryG9LongProducts_bounds {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    {k : ℕ × ℕ × ℕ} {m : ℕ} (hm : m ∈ fouvryG9LongProducts N ρ k) :
    ρ ^ (k.2.1 + k.2.2) ≤ (m : ℝ) ∧
      (m : ℝ) < ρ ^ 2 * ρ ^ (k.2.1 + k.2.2) := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hm
  obtain ⟨_, hs, ht, _, _, hslo, hshi, htlo, hthi⟩ := mem_filter.mp hz
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  rw [Nat.cast_mul, pow_add]
  constructor
  · exact mul_le_mul hslo htlo (pow_nonneg hr.le _) (Nat.cast_nonneg _)
  · have hh := mul_lt_mul hshi hthi.le
      (show (0 : ℝ) < z.2 by exact_mod_cast ht.pos)
      (pow_nonneg hr.le (k.2.1 + 1))
    rw [pow_succ, pow_succ] at hh
    nlinarith only [hh]

theorem fouvryG9LongProducts_le_two {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5 / 4) {k : ℕ × ℕ × ℕ} {m : ℕ}
    (hm : m ∈ fouvryG9LongProducts N ρ k) :
    (m : ℝ) ≤ 2 * ρ ^ (k.2.1 + k.2.2) := by
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  have hs : ρ ^ 2 ≤ 2 := by nlinarith
  exact (fouvryG9LongProducts_bounds hρ hm).2.le.trans
    (mul_le_mul_of_nonneg_right hs (pow_nonneg hr.le _))

/-- Actual cell labels enter the positive rectangular cover. The second prime
is not required to be coprime to `N`. -/
theorem fouvryG9LongLabels_of_cell {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ)
    {k y : ℕ × ℕ × ℕ} (hy : y ∈ fouvryG9GridCell N eps ρ k) :
    (y.2.1, y.1 / y.2.1) ∈ fouvryG9LongLabels N ρ k := by
  obtain ⟨hy, he⟩ := fouvryG9GridCell_mem_iff.mp hy
  obtain ⟨_, hsN, htN⟩ := fouvryG9Grid_label_bounds hy
  obtain ⟨hs, _, _, ht, hcop, _, _, hslo, _⟩ := fouvryG9Carrier_geometry hy
  have hj := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) he
  have hk := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) he
  change fouvryG9GridIndex ρ (y.2.1 : ℝ) = k.2.1 at hj
  change fouvryG9GridIndex ρ ((y.1 / y.2.1 : ℕ) : ℝ) = k.2.2 at hk
  have hsb := fouvryG9GridIndex_bounds hρ
    (show (1 : ℝ) ≤ y.2.1 by exact_mod_cast hs.one_le)
  have htb := fouvryG9GridIndex_bounds hρ
    (show (1 : ℝ) ≤ (y.1 / y.2.1 : ℕ) by exact_mod_cast ht.one_le)
  rw [hj] at hsb
  rw [hk] at htb
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩,
    hs, ht, ?_, hslo, hsb.1, hsb.2, htb.1, htb.2⟩
  exact (Nat.coprime_mul_iff_left.mp hcop).2

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
