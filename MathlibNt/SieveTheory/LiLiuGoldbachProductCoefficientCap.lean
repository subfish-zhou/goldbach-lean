import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductCoefficient

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The product-fibre cap does not depend on the upper cutoff. -/
theorem goldbachG11ProductCoefficient_le_four_hundred_of_cutoff
    (N m : ℕ) (c : ℝ) :
    goldbachG11ProductCoefficient N ((N : ℝ) ^ ((4 : ℝ) / 53)) c m ≤ 400 := by
  classical
  let z : ℝ := (N : ℝ) ^ ((4 : ℝ) / 53)
  change (goldbachG11ProductFiber N z c m).card ≤ 400
  by_cases hne : (goldbachG11ProductFiber N z c m).Nonempty
  · have hm := goldbachG11ProductSupport_data
      (goldbachG11ProductFiber_nonempty_iff.mp hne)
    have hn1 : 1 ≤ m := hm.1
    have hnN : m < N := hm.2.1
    let L := largePrimeDivisors m z
    have hcap : L.card ≤ 20 := largePrimeDivisors_card_le_twenty hn1 hnN
      (by norm_num : (1 : ℝ) / 21 < 4 / 53)
    have hcard : (goldbachG11ProductFiber N z c m).card ≤ (L.product L).card :=
      Finset.card_le_card_of_injOn goldbachG11ProductCoordinates
        (fun _ hu => goldbachG11ProductCoordinates_mem_largePrimeDivisors hu)
        (goldbachG11ProductCoordinates_injOn N m z c)
    calc
      (goldbachG11ProductFiber N z c m).card ≤ (L.product L).card := hcard
      _ = L.card * L.card := Finset.card_product _ _
      _ = L.card ^ 2 := (pow_two _).symm
      _ ≤ 20 ^ 2 := Nat.pow_le_pow_left hcap 2
      _ = 400 := by norm_num
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    norm_num

/-- Any subset of good bodies retains the cap, without identifying equal products. -/
theorem goldbachG11GoodBodySubset_product_fiber_card_le_four_hundred
    (N m : ℕ) (c : ℝ) (B : Finset GoldbachG11SwitchedBody)
    (hB : B ⊆ goldbachG11GoodSwitchedBodies N ((N : ℝ) ^ ((4 : ℝ) / 53)) c) :
    (B.filter fun u => goldbachG11SwitchedBodyProd u = m).card ≤ 400 := by
  classical
  apply le_trans (Finset.card_le_card (show
    (B.filter fun u => goldbachG11SwitchedBodyProd u = m) ⊆
      goldbachG11ProductFiber N ((N : ℝ) ^ ((4 : ℝ) / 53)) c m from ?_))
    (goldbachG11ProductCoefficient_le_four_hundred_of_cutoff N m c)
  intro u hu
  obtain ⟨hu, hm⟩ := Finset.mem_filter.mp hu
  exact mem_goldbachG11ProductFiber_iff.mpr ⟨hB hu, hm⟩

/-- Filter actual bodies first, then count every body representation in the product fibre. -/
noncomputable def goldbachG11FilteredProductCoefficient
    (N : ℕ) (z c : ℝ) (C : GoldbachG11SwitchedBody → Prop) (m : ℕ) : ℕ := by
  classical
  exact (((goldbachG11GoodSwitchedBodies N z c).filter C).filter fun u =>
    goldbachG11SwitchedBodyProd u = m).card

theorem goldbachG11FilteredProductCoefficient_le
    (N m : ℕ) (z c : ℝ) (C : GoldbachG11SwitchedBody → Prop) :
    goldbachG11FilteredProductCoefficient N z c C m ≤
      goldbachG11ProductCoefficient N z c m := by
  classical
  unfold goldbachG11FilteredProductCoefficient goldbachG11ProductCoefficient
  apply Finset.card_le_card
  intro u hu
  obtain ⟨hu, hm⟩ := Finset.mem_filter.mp hu
  exact mem_goldbachG11ProductFiber_iff.mpr ⟨(Finset.mem_filter.mp hu).1, hm⟩

theorem goldbachG11FilteredProductCoefficient_le_four_hundred
    (N m : ℕ) (c : ℝ) (C : GoldbachG11SwitchedBody → Prop) :
    goldbachG11FilteredProductCoefficient N ((N : ℝ) ^ ((4 : ℝ) / 53)) c C m ≤ 400 :=
  (goldbachG11FilteredProductCoefficient_le N m _ c C).trans
    (goldbachG11ProductCoefficient_le_four_hundred_of_cutoff N m c)

noncomputable def goldbachG11NormalizedFilteredProductCoefficient
    (N : ℕ) (z c : ℝ) (C : GoldbachG11SwitchedBody → Prop) (m : ℕ) : ℝ :=
  (goldbachG11FilteredProductCoefficient N z c C m : ℝ) / 400

theorem goldbachG11NormalizedFilteredProductCoefficient_mem_Icc
    (N m : ℕ) (c : ℝ) (C : GoldbachG11SwitchedBody → Prop) :
    goldbachG11NormalizedFilteredProductCoefficient
      N ((N : ℝ) ^ ((4 : ℝ) / 53)) c C m ∈ Set.Icc (0 : ℝ) 1 := by
  have h : (goldbachG11FilteredProductCoefficient
      N ((N : ℝ) ^ ((4 : ℝ) / 53)) c C m : ℝ) ≤ 400 := by
    exact_mod_cast goldbachG11FilteredProductCoefficient_le_four_hundred N m c C
  unfold goldbachG11NormalizedFilteredProductCoefficient
  constructor
  · positivity
  · linarith

theorem goldbachG11NormalizedProductCoefficient_mem_Icc_of_cutoff
    (N m : ℕ) (c : ℝ) :
    goldbachG11NormalizedProductCoefficient
      N ((N : ℝ) ^ ((4 : ℝ) / 53)) c m ∈ Set.Icc (0 : ℝ) 1 := by
  have h : (goldbachG11ProductCoefficient
      N ((N : ℝ) ^ ((4 : ℝ) / 53)) c m : ℝ) ≤ 400 := by
    exact_mod_cast goldbachG11ProductCoefficient_le_four_hundred_of_cutoff N m c
  constructor
  · exact goldbachG11NormalizedProductCoefficient_nonneg N m _ c
  · unfold goldbachG11NormalizedProductCoefficient
    linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
