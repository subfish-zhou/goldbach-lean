import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossSwitch
import MathlibNt.SieveTheory.LiLiuGoldbachProductCoefficientCap
import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductGrouping

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG12GoodCrossBodies (N : ℕ) (z b c : ℝ) :
    Finset GoldbachG11SwitchedBody := by
  classical
  exact (goldbachG12CrossSwitchedBodies N z b c).filter
    (fun u => Nat.Coprime (goldbachG11SwitchedBodyProd u) N)

noncomputable def goldbachG12GoodCrossTotal (N : ℕ) (ε z b c : ℝ) : ℤ :=
  ∑ u ∈ goldbachG12GoodCrossBodies N z b c,
    ((goldbachG11FirstPrimeFiber N ε z u).card : ℤ)

noncomputable def goldbachG12BadCrossTotal (N : ℕ) (ε z b c : ℝ) : ℤ := by
  classical
  exact ∑ u ∈ (goldbachG12CrossSwitchedBodies N z b c).filter
    (fun u => ¬Nat.Coprime (goldbachG11SwitchedBodyProd u) N),
    ((goldbachG11FirstPrimeFiber N ε z u).card : ℤ)

noncomputable def goldbachG12ProductSupport (N : ℕ) (z b c : ℝ) : Finset ℕ :=
  (goldbachG12GoodCrossBodies N z b c).image goldbachG11SwitchedBodyProd

noncomputable def goldbachG12ProductCoefficient (N : ℕ) (z b c : ℝ) (m : ℕ) : ℕ :=
  goldbachG11FilteredProductCoefficient N z c
    (fun u => (u.2.1 : ℝ) ≤ b ∧ b ≤ (u.1 : ℝ)) m

open Classical in
theorem goldbachG12GoodCrossBodies_eq_filter (N : ℕ) (z b c : ℝ) :
    goldbachG12GoodCrossBodies N z b c =
      (goldbachG11GoodSwitchedBodies N z c).filter
        (fun u => (u.2.1 : ℝ) ≤ b ∧ b ≤ (u.1 : ℝ)) := by
  ext u
  simp [goldbachG12GoodCrossBodies, goldbachG12CrossSwitchedBodies,
    goldbachG11GoodSwitchedBodies, and_assoc, and_left_comm, and_comm]

theorem goldbachG12GoodCrossBodies_subset (N : ℕ) (z b c : ℝ) :
    goldbachG12GoodCrossBodies N z b c ⊆ goldbachG11GoodSwitchedBodies N z c := by
  classical
  rw [goldbachG12GoodCrossBodies_eq_filter]
  exact Finset.filter_subset _ _

open Classical in
theorem goldbachG12ProductCoefficient_eq_card (N : ℕ) (z b c : ℝ) (m : ℕ) :
    goldbachG12ProductCoefficient N z b c m =
      ((goldbachG12GoodCrossBodies N z b c).filter
        (fun u => goldbachG11SwitchedBodyProd u = m)).card := by
  rw [goldbachG12GoodCrossBodies_eq_filter]
  unfold goldbachG12ProductCoefficient goldbachG11FilteredProductCoefficient
  apply congrArg Finset.card
  ext u
  simp only [Finset.mem_filter]

theorem goldbachG12ProductCoefficient_le_four_hundred (N m : ℕ) (b c : ℝ) :
    goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ)) b c m ≤ 400 :=
  goldbachG11FilteredProductCoefficient_le_four_hundred N m c _

theorem goldbachG12ProductSupport_data {N m : ℕ} {z b c : ℝ}
    (hm : m ∈ goldbachG12ProductSupport N z b c) :
    0 < m ∧ m < N ∧ Nat.Coprime m N ∧ z ≤ (m.minFac : ℝ) := by
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hm
  exact goldbachG11ProductSupport_data
    (mem_goldbachG11ProductSupport_iff.mpr
      ⟨u,goldbachG12GoodCrossBodies_subset N z b c hu,rfl⟩)

/-- The cross is split before any bound; no main-family enlargement occurs. -/
theorem goldbachG12RoughSum_eq_good_add_bad (N : ℕ) (ε z b c : ℝ) :
    (∑ v ∈ goldbachG12Labels N z b c, goldbachG11RoughCount N ε v) =
      goldbachG12GoodCrossTotal N ε z b c + goldbachG12BadCrossTotal N ε z b c := by
  classical
  rw [goldbachG12RoughSum_eq_crossSwitchedBodies]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- Only the exceptional bad part is bounded by the broad exception family. -/
theorem goldbachG12BadCrossTotal_le_NCount_sum (N : ℕ) (ε z b c : ℝ) (hε : 0 ≤ ε) :
    goldbachG12BadCrossTotal N ε z b c ≤
      ∑ v ∈ goldbachG11Labels N z c,
        goldbachG11NCount (goldbachDifferenceCarrier N ε) N v := by
  classical
  apply le_trans (show goldbachG12BadCrossTotal N ε z b c ≤
    goldbachG11BadSwitchedTotal N ε z c from ?_)
    (goldbachG11BadSwitchedTotal_le_NCount_sum N ε z c hε)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    obtain ⟨hu,hbad⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,hbad⟩
  · intro u _ _
    exact Int.natCast_nonneg _

/-- Product grouping counts every body in its fibre; product injectivity is not assumed. -/
theorem goldbachG12GoodCross_sum_product (N : ℕ) (z b c : ℝ) (f : ℕ → ℤ) :
    (∑ u ∈ goldbachG12GoodCrossBodies N z b c, f (goldbachG11SwitchedBodyProd u)) =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℤ)*f m := by
  classical
  have hh : (goldbachG12GoodCrossBodies N z b c).filter
      (fun u => goldbachG11SwitchedBodyProd u ∈ goldbachG12ProductSupport N z b c) =
      goldbachG12GoodCrossBodies N z b c := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
  have hf := Finset.sum_fiberwise_eq_sum_filter (goldbachG12GoodCrossBodies N z b c)
    (goldbachG12ProductSupport N z b c) goldbachG11SwitchedBodyProd
    (fun u => f (goldbachG11SwitchedBodyProd u))
  rw [hh] at hf
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m _
  rw [goldbachG12ProductCoefficient_eq_card]
  calc
    _ = ∑ _u ∈ (goldbachG12GoodCrossBodies N z b c).filter
        (fun u => goldbachG11SwitchedBodyProd u = m), f m := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [(Finset.mem_filter.mp hu).2]
    _ = _ := by simp

theorem goldbachG12GoodCrossTotal_eq_product_sum (N : ℕ) (ε z b c : ℝ) :
    goldbachG12GoodCrossTotal N ε z b c =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℤ)*
          (goldbachG11ProductFirstPrimeFiber N ε z m).card := by
  unfold goldbachG12GoodCrossTotal
  calc
    _ = ∑ u ∈ goldbachG12GoodCrossBodies N z b c,
        ((goldbachG11ProductFirstPrimeFiber N ε z (goldbachG11SwitchedBodyProd u)).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [goldbachG11FirstPrimeFiber_eq_product
        (mem_goldbachG11GoodSwitchedBodies_iff.mp
          (goldbachG12GoodCrossBodies_subset N z b c hu)).1]
    _ = _ := goldbachG12GoodCross_sum_product N z b c
      (fun m => (goldbachG11ProductFirstPrimeFiber N ε z m).card)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
