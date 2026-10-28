import MathlibNt.SieveTheory.LiLiuGoldbachS4CarrierGeometry

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


noncomputable def goldbachC9Pairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (goldbachS4Pairs N ((N : ℝ) ^ ((4 : ℝ) / 53))).filter fun rs =>
    (rs.1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) ∧
      (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (rs.2 : ℝ)

theorem mem_goldbachC9Pairs_iff {N : ℕ} {rs : ℕ × ℕ} :
    rs ∈ goldbachC9Pairs N ↔
      rs.1.Prime ∧ rs.2.Prime ∧ Nat.Coprime (rs.1 * rs.2) N ∧
        (N : ℝ) ^ ((4 : ℝ) / 53) ≤ (rs.1 : ℝ) ∧
          rs.1 ≤ rs.2 ∧ rs.1 * rs.2 ^ 2 ≤ N ∧
            (rs.1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) ∧
              (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (rs.2 : ℝ) := by
  simp only [goldbachC9Pairs, Finset.mem_filter, mem_goldbachS4Pairs_iff]
  tauto

theorem goldbachC9Pairs_subset_S4Pairs (N : ℕ) :
    goldbachC9Pairs N ⊆ goldbachS4Pairs N ((N : ℝ) ^ ((4 : ℝ) / 53)) :=
  Finset.filter_subset _ _

def goldbachC9Prod (rs : ℕ × ℕ) : ℕ := goldbachC8Prod rs

theorem goldbachC9Prod_pos {N : ℕ} {rs : ℕ × ℕ} (hrs : rs ∈ goldbachC9Pairs N) :
    0 < goldbachC9Prod rs :=
  goldbachC8Prod_pos (goldbachC9Pairs_subset_S4Pairs N hrs)


theorem goldbachC9Prod_support_bounds {N : ℕ} {rs : ℕ × ℕ}
    (hN : 2 ≤ N) (hrs : rs ∈ goldbachC9Pairs N) :
    (N : ℝ) ^ ((65 : ℝ) / 159) ≤ (goldbachC9Prod rs : ℝ) ∧
      (goldbachC9Prod rs : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
  have h := mem_goldbachC9Pairs_iff.mp hrs
  refine ⟨?_, goldbachC8Prod_le_two_thirds hN (goldbachC9Pairs_subset_S4Pairs N hrs)⟩
  calc
    (N : ℝ) ^ ((65 : ℝ) / 159) =
        (N : ℝ) ^ ((4 : ℝ) / 53) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      norm_num
    _ ≤ (rs.1 : ℝ) * (rs.2 : ℝ) :=
      mul_le_mul h.2.2.2.1 h.2.2.2.2.2.2.2 (by positivity) (by positivity)
    _ = (goldbachC9Prod rs : ℝ) := by simp [goldbachC9Prod, goldbachC8Prod]

noncomputable def goldbachC9ProductSupport (N : ℕ) : Finset ℕ :=
  (goldbachC9Pairs N).image goldbachC9Prod


theorem goldbachC9ProductSupport_bounds {N m : ℕ}
    (hN : 2 ≤ N) (hm : m ∈ goldbachC9ProductSupport N) :
    (N : ℝ) ^ ((65 : ℝ) / 159) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp hm
  exact goldbachC9Prod_support_bounds hN hrs


theorem goldbachC9Pair_dvdFiber_card_le_fourHundred {N n : ℕ}
    (hn1 : 1 ≤ n) (hnN : n < N) :
    ((goldbachC9Pairs N).filter fun rs => goldbachC9Prod rs ∣ n).card ≤ 400 := by
  have hcap := largePrimeDivisors_card_le_twenty hn1 hnN
    (by norm_num : (1 : ℝ) / 21 < 4 / 53)
  have hsub : ((goldbachC9Pairs N).filter fun rs => goldbachC9Prod rs ∣ n) ⊆
      (largePrimeDivisors n ((N : ℝ) ^ ((4 : ℝ) / 53))).product
        (largePrimeDivisors n ((N : ℝ) ^ ((4 : ℝ) / 53))) := by
    intro rs hrs
    obtain ⟨hrs, hd⟩ := Finset.mem_filter.mp hrs
    exact goldbachS4Pair_mem_largePrimeDivisors (by omega)
      (goldbachC9Pairs_subset_S4Pairs N hrs) hd
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ = _ := Finset.card_product _ _
    _ ≤ 20 * 20 := Nat.mul_le_mul hcap hcap
    _ = 400 := by norm_num

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig