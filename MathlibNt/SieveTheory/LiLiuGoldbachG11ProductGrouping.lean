import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductCoefficient

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG11ProductFirstPrimeFiber (N : ℕ) (eps z : ℝ) (m : ℕ) :
    Finset ℕ := by
  classical
  exact (goldbachClosedPrimes N z m.minFac).filter fun r =>
    eps * N < (r * m : ℕ) ∧ r * m < N ∧ (N - r * m).Prime

theorem mem_goldbachG11ProductFirstPrimeFiber_iff {N m r : ℕ} {eps z : ℝ} :
    r ∈ goldbachG11ProductFirstPrimeFiber N eps z m ↔
      r.Prime ∧ ¬r ∣ N ∧ z ≤ (r : ℝ) ∧ r ≤ m.minFac ∧
        eps * N < (r * m : ℕ) ∧ r * m < N ∧ (N - r * m).Prime := by
  classical
  simp only [goldbachG11ProductFirstPrimeFiber, Finset.mem_filter,
    mem_goldbachClosedPrimes_iff, Nat.cast_le]
  tauto

theorem goldbachG11FirstPrimeFiber_eq_product {N : ℕ} {eps z b : ℝ}
    {u : GoldbachG11SwitchedBody} (hu : u ∈ goldbachG11SwitchedBodies N z b) :
    goldbachG11FirstPrimeFiber N eps z u =
      goldbachG11ProductFirstPrimeFiber N eps z (goldbachG11SwitchedBodyProd u) := by
  classical
  unfold goldbachG11FirstPrimeFiber goldbachG11ProductFirstPrimeFiber
  rw [goldbachG11SwitchedBodyProd_minFac hu]

theorem goldbachG11FirstPrimeFiber_eq_product_of_mem {N m : ℕ} {eps z b : ℝ}
    {u : GoldbachG11SwitchedBody} (hu : u ∈ goldbachG11ProductFiber N z b m) :
    goldbachG11FirstPrimeFiber N eps z u =
      goldbachG11ProductFirstPrimeFiber N eps z m := by
  obtain ⟨hu, heq⟩ := mem_goldbachG11ProductFiber_iff.mp hu
  rw [goldbachG11FirstPrimeFiber_eq_product
    (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1, heq]

-- No injectivity of the product map is used: each filtered fiber contributes its card.
theorem goldbachG11GoodSwitchedBodies_sum_product (N : ℕ) (z b : ℝ) (f : ℕ → ℤ) :
    (∑ u ∈ goldbachG11GoodSwitchedBodies N z b, f (goldbachG11SwitchedBodyProd u)) =
      ∑ m ∈ goldbachG11ProductSupport N z b,
        (goldbachG11ProductCoefficient N z b m : ℤ) * f m := by
  classical
  have hfilter : (goldbachG11GoodSwitchedBodies N z b).filter
      (fun u => goldbachG11SwitchedBodyProd u ∈ goldbachG11ProductSupport N z b) =
        goldbachG11GoodSwitchedBodies N z b := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact mem_goldbachG11ProductSupport_iff.mpr ⟨u, hu, rfl⟩
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (goldbachG11GoodSwitchedBodies N z b) (goldbachG11ProductSupport N z b)
    goldbachG11SwitchedBodyProd (fun u => f (goldbachG11SwitchedBodyProd u))
  rw [hfilter] at hfiber
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro m _
  calc
    (∑ u ∈ (goldbachG11GoodSwitchedBodies N z b).filter
        (fun u => goldbachG11SwitchedBodyProd u = m), f (goldbachG11SwitchedBodyProd u)) =
        ∑ _u ∈ goldbachG11ProductFiber N z b m, f m := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [(mem_goldbachG11ProductFiber_iff.mp hu).2]
    _ = (goldbachG11ProductCoefficient N z b m : ℤ) * f m := by
      simp [goldbachG11ProductCoefficient]

theorem goldbachG11GoodSwitchedTotal_eq_product_sum (N : ℕ) (eps z b : ℝ) :
    goldbachG11GoodSwitchedTotal N eps z b =
      ∑ m ∈ goldbachG11ProductSupport N z b,
        (goldbachG11ProductCoefficient N z b m : ℤ) *
          (goldbachG11ProductFirstPrimeFiber N eps z m).card := by
  unfold goldbachG11GoodSwitchedTotal
  calc
    (∑ u ∈ goldbachG11GoodSwitchedBodies N z b,
        ((goldbachG11FirstPrimeFiber N eps z u).card : ℤ)) =
        ∑ u ∈ goldbachG11GoodSwitchedBodies N z b,
          ((goldbachG11ProductFirstPrimeFiber N eps z
            (goldbachG11SwitchedBodyProd u)).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [goldbachG11FirstPrimeFiber_eq_product
        (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1]
    _ = _ := goldbachG11GoodSwitchedBodies_sum_product N z b
      (fun m => (goldbachG11ProductFirstPrimeFiber N eps z m).card)

theorem goldbachG11GoodSwitchedTotal_eq_canonical_product_sum (N : ℕ) (eps : ℝ) :
    goldbachG11GoodSwitchedTotal N eps ((N : ℝ) ^ ((4 : ℝ) / 53))
      ((N : ℝ) ^ ((4 : ℝ) / 33)) =
      ∑ m ∈ goldbachG11ProductSupport N ((N : ℝ) ^ ((4 : ℝ) / 53))
          ((N : ℝ) ^ ((4 : ℝ) / 33)),
        (goldbachG11ProductCoefficient N ((N : ℝ) ^ ((4 : ℝ) / 53))
          ((N : ℝ) ^ ((4 : ℝ) / 33)) m : ℤ) *
            (goldbachG11ProductFirstPrimeFiber N eps ((N : ℝ) ^ ((4 : ℝ) / 53)) m).card :=
  goldbachG11GoodSwitchedTotal_eq_product_sum N eps _ _

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig