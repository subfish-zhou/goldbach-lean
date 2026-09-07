import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductGrouping
import MathlibNt.SieveTheory.LiLiuGoldbachG11ActiveProductGeometry

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11_product_active_bounds {N m r : ℕ} {ε : ℝ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)))
    (hr : r ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) m) :
    ε * (N : ℝ)^(29 / 33 : ℝ) < (m : ℝ) ∧ (m : ℝ) < (N : ℝ)^(49 / 53 : ℝ) := by
  obtain ⟨u, hu, heq⟩ := mem_goldbachG11ProductSupport_iff.mp hm
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1
  have hr' : r ∈ goldbachG11FirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) u := by
    rwa [goldbachG11FirstPrimeFiber_eq_product huB, heq]
  simpa only [heq] using goldbachG11_active_product_bounds hN huB hr'

/-- A purely geometric envelope; no output-prime condition is inserted into coefficients. -/
noncomputable def goldbachG11EffectiveProductSupport (N : ℕ) (ε : ℝ) : Finset ℕ := by
  classical
  exact (goldbachG11ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ))).filter
    fun m => ε * (N : ℝ)^(29 / 33 : ℝ) < (m : ℝ) ∧ (m : ℝ) < (N : ℝ)^(49 / 53 : ℝ)

theorem goldbachG11ProductFirstPrimeFiber_eq_empty_of_inactive {N m : ℕ} {ε : ℝ}
    (hN : 2 ≤ N)
    (hm : m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)))
    (hi : ¬(ε * (N : ℝ)^(29 / 33 : ℝ) < (m : ℝ) ∧ (m : ℝ) < (N : ℝ)^(49 / 53 : ℝ))) :
    goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) m = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  exact hi (goldbachG11_product_active_bounds hN hm hr)

theorem goldbachG11GoodSwitchedTotal_eq_effective_product_sum {N : ℕ} (ε : ℝ)
    (hN : 2 ≤ N) :
    goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) =
      ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
        (goldbachG11ProductCoefficient N ((N : ℝ)^(4 / 53 : ℝ))
          ((N : ℝ)^(4 / 33 : ℝ)) m : ℤ) *
        (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) m).card := by
  classical
  rw [goldbachG11GoodSwitchedTotal_eq_canonical_product_sum,
    goldbachG11EffectiveProductSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hi : ε * (N : ℝ)^(29 / 33 : ℝ) < (m : ℝ) ∧ (m : ℝ) < (N : ℝ)^(49 / 53 : ℝ)
  · rw [if_pos hi]
  · rw [if_neg hi, goldbachG11ProductFirstPrimeFiber_eq_empty_of_inactive hN hm hi,
      Finset.card_empty, Nat.cast_zero, mul_zero]

noncomputable def goldbachG11EffectiveProductCoefficient (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ := by
  classical
  exact if m ∈ goldbachG11EffectiveProductSupport N ε then
    goldbachG11NormalizedProductCoefficient N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) m
    else 0

theorem goldbachG11EffectiveProductCoefficient_bounds (N m : ℕ) (ε : ℝ) :
    0 ≤ goldbachG11EffectiveProductCoefficient N ε m ∧
      goldbachG11EffectiveProductCoefficient N ε m ≤ 1 := by
  classical
  unfold goldbachG11EffectiveProductCoefficient
  split
  · exact ⟨goldbachG11NormalizedProductCoefficient_nonneg N m _ _,
      goldbachG11NormalizedProductCoefficient_le_one N m⟩
  · norm_num

theorem goldbachG11EffectiveProductCoefficient_support {N m : ℕ} {ε : ℝ}
    (ha : goldbachG11EffectiveProductCoefficient N ε m ≠ 0) :
    m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) ∧
      ε * (N : ℝ)^(29 / 33 : ℝ) < (m : ℝ) ∧ (m : ℝ) < (N : ℝ)^(49 / 53 : ℝ) := by
  classical
  have hm : m ∈ goldbachG11EffectiveProductSupport N ε := by
    by_contra hn
    simp only [goldbachG11EffectiveProductCoefficient, if_neg hn, ne_eq, not_true_eq_false] at ha
  exact Finset.mem_filter.mp hm

theorem goldbachG11GoodSwitchedTotal_eq_effective_normalized_sum {N : ℕ} (ε : ℝ)
    (hN : 2 ≤ N) :
    (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)) : ℝ) =
      400 * ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
        goldbachG11EffectiveProductCoefficient N ε m *
          (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) m).card := by
  classical
  rw [goldbachG11GoodSwitchedTotal_eq_effective_product_sum ε hN]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [goldbachG11EffectiveProductCoefficient, if_pos hm, ← mul_assoc,
    goldbachG11NormalizedProductCoefficient_mul_four_hundred]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig