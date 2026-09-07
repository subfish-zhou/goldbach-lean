import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridCarrier

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- A cell is the exact fibre inside the actual carrier, not an enlarged prefix. -/
def fouvryG9GridCell (N : ℕ) (eps ρ : ℝ) (k : ℕ × ℕ × ℕ) :
    Finset (ℕ × ℕ × ℕ) :=
  (fouvryG9Carrier N eps).filter (fun y => fouvryG9GridKey ρ y = k)

theorem fouvryG9GridCell_mem_iff {N : ℕ} {eps ρ : ℝ} {k y : ℕ × ℕ × ℕ} :
    y ∈ fouvryG9GridCell N eps ρ k ↔
      y ∈ fouvryG9Carrier N eps ∧ fouvryG9GridKey ρ y = k := by
  simp only [fouvryG9GridCell, mem_filter]

theorem fouvryG9GridCell_nonempty_iff {N : ℕ} {eps ρ : ℝ} {k : ℕ × ℕ × ℕ} :
    (fouvryG9GridCell N eps ρ k).Nonempty ↔ k ∈ fouvryG9GridUsed N eps ρ := by
  simp only [fouvryG9GridUsed, mem_image, Finset.Nonempty, fouvryG9GridCell_mem_iff]

/-- Rectangular geometry uses both separate long-coordinate prime labels. -/
theorem fouvryG9GridCell_rectangle {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ)
    {k y : ℕ × ℕ × ℕ} (hy : y ∈ fouvryG9GridCell N eps ρ k) :
    ρ ^ k.1 ≤ (y.2.2 : ℝ) ∧ (y.2.2 : ℝ) < ρ * ρ ^ k.1 ∧
    ρ ^ (k.2.1 + k.2.2) ≤ (y.1 : ℝ) ∧
      (y.1 : ℝ) < ρ ^ 2 * ρ ^ (k.2.1 + k.2.2) := by
  obtain ⟨hy, he⟩ := fouvryG9GridCell_mem_iff.mp hy
  obtain ⟨hn, hs, hq⟩ := fouvryG9Grid_label_bounds hy
  have hi := congrArg Prod.fst he
  have hj := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) he
  have hk := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) he
  change fouvryG9GridIndex ρ (y.2.2 : ℝ) = k.1 at hi
  change fouvryG9GridIndex ρ (y.2.1 : ℝ) = k.2.1 at hj
  change fouvryG9GridIndex ρ ((y.1 / y.2.1 : ℕ) : ℝ) = k.2.2 at hk
  have bound : ∀ a : ℕ, 2 ≤ a →
      ρ ^ fouvryG9GridIndex ρ a ≤ (a : ℝ) ∧
      (a : ℝ) < ρ * ρ ^ fouvryG9GridIndex ρ a := by
    intro a ha
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    simpa only [pow_succ, mul_comm] using fouvryG9GridIndex_bounds hρ ha1
  have hnb := bound _ hn.1
  have hsb := bound _ hs.1
  have hqb := bound _ hq.1
  rw [hi] at hnb
  rw [hj] at hsb
  rw [hk] at hqb
  have hm : (y.2.1 : ℝ) * ((y.1 / y.2.1 : ℕ) : ℝ) = y.1 := by
    exact_mod_cast (Nat.mul_div_cancel' (fouvryG9Carrier_geometry hy).2.2.1)
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  refine ⟨hnb.1, hnb.2, ?_, ?_⟩
  · rw [pow_add, ← hm]
    exact mul_le_mul hsb.1 hqb.1 (pow_nonneg hr.le _) (Nat.cast_nonneg _)
  · rw [pow_add, ← hm]
    have hh := mul_lt_mul hsb.2 hqb.2.le
      (show (0 : ℝ) < (y.1 / y.2.1 : ℕ) by exact_mod_cast (show 0 < y.1 / y.2.1 by omega))
      (mul_nonneg hr.le (pow_nonneg hr.le k.2.1))
    nlinarith only [hh]

/-- With the small mesh, the long-coordinate interval lies in `[M,2M]`. -/
theorem fouvryG9GridCell_long_le_two {N : ℕ} {eps ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5 / 4) {k y : ℕ × ℕ × ℕ}
    (hy : y ∈ fouvryG9GridCell N eps ρ k) :
    (y.1 : ℝ) ≤ 2 * ρ ^ (k.2.1 + k.2.2) := by
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  have hs : ρ ^ 2 ≤ 2 := by nlinarith
  exact (fouvryG9GridCell_rectangle hρ hy).2.2.2.le.trans
    (mul_le_mul_of_nonneg_right hs (pow_nonneg hr.le _))

/-- A genuine occupied-cell witness supplies the scale window; no error estimate is claimed. -/
theorem fouvryG9GridCell_scale_window {N : ℕ} {eps ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5 / 4) {k : ℕ × ℕ × ℕ}
    (hne : (fouvryG9GridCell N eps ρ k).Nonempty) :
    eps * (N : ℝ) < 4 * ρ ^ (k.2.1 + k.2.2) * ρ ^ k.1 ∧
      4 * ρ ^ (k.2.1 + k.2.2) * ρ ^ k.1 ≤ 4 * (N : ℝ) := by
  obtain ⟨y, hy⟩ := hne
  have hg := fouvryG9Carrier_geometry (fouvryG9GridCell_mem_iff.mp hy).1
  obtain ⟨hnlo, hnhi, hmlo, hmhi⟩ := fouvryG9GridCell_rectangle hρ hy
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  have hT : 0 < ρ ^ k.1 := pow_pos hr _
  have hM : 0 < ρ ^ (k.2.1 + k.2.2) := pow_pos hr _
  have hn : 0 < (y.2.2 : ℝ) := lt_of_lt_of_le hT hnlo
  have hm : 0 < (y.1 : ℝ) := lt_of_lt_of_le hM hmlo
  have hupper : (y.2.2 : ℝ) * y.1 < (N : ℝ) := by exact_mod_cast hg.2.2.2.2.2.2.2.2.2.2
  have hlower : eps * (N : ℝ) < (y.2.2 : ℝ) * y.1 := by
    exact_mod_cast hg.2.2.2.2.2.2.2.2.2.1
  have hlo := mul_le_mul hnlo hmlo hM.le hn.le
  have hhi := mul_lt_mul hnhi hmhi.le hm (mul_nonneg hr.le hT.le)
  have hs : ρ ^ 2 ≤ 2 := by nlinarith
  have hc : ρ * ρ ^ 2 ≤ 4 := by nlinarith
  have hbudget := mul_le_mul_of_nonneg_right hc (mul_nonneg hM.le hT.le)
  constructor <;> nlinarith

/-- Exact partition of the carrier sum into its occupied grid cells. -/
theorem fouvryG9GridCell_sum (N : ℕ) (eps ρ : ℝ) (F : (ℕ × ℕ × ℕ) → ℝ) :
    (∑ k ∈ fouvryG9GridUsed N eps ρ, ∑ y ∈ fouvryG9GridCell N eps ρ k, F y) =
      ∑ y ∈ fouvryG9Carrier N eps, F y := by
  apply sum_fiberwise_of_maps_to
  intro y hy
  exact mem_image_of_mem (fouvryG9GridKey ρ) hy

/-- Exact positive counting partition; no carrier point is lost or merged. -/
theorem fouvryG9GridCell_card_sum (N : ℕ) (eps ρ : ℝ) :
    (∑ k ∈ fouvryG9GridUsed N eps ρ, (fouvryG9GridCell N eps ρ k).card) =
      (fouvryG9Carrier N eps).card := by
  have h := sum_fiberwise_of_maps_to
    (s := fouvryG9Carrier N eps) (t := fouvryG9GridUsed N eps ρ)
    (g := fouvryG9GridKey ρ)
    (fun y hy => mem_image_of_mem (fouvryG9GridKey ρ) hy) (fun _ => (1 : ℕ))
  simpa only [sum_const, smul_eq_mul, mul_one, fouvryG9GridCell] using h

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
