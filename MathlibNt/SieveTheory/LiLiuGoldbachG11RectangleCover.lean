import MathlibNt.SieveTheory.LiLiuGoldbachG11RectangleCount

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11RectangleWeight_of_firstPrimeFiber {N m p : ℕ} {ε : ℝ}
    (hp : p ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m) :
    goldbachG11RectangleWeight N (m,p) =
      (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ) := by
  obtain ⟨hp, hpN, _⟩ := mem_goldbachG11ProductFirstPrimeFiber_iff.mp hp
  have hc := hp.coprime_iff_not_dvd.mpr hpN
  simp [goldbachG11RectangleWeight,
    MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeSWBeta, hp, hc]

/-- Actual first-prime/product pairs; the coefficient continues to carry the body fibres. -/
def goldbachG11PrimeProductAtoms (N : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  ((goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ))) ×ˢ range N).filter fun v =>
      v.2 ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) v.1

/-- Literal equality with the accepted good switched count, including all multiplicities. -/
theorem goldbachG11GoodSwitchedTotal_eq_weighted_atoms (N : ℕ) (ε : ℝ) :
    (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) : ℝ) =
      ∑ v ∈ goldbachG11PrimeProductAtoms N ε, goldbachG11RectangleWeight N v := by
  rw [goldbachG11GoodSwitchedTotal_eq_canonical_product_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  unfold goldbachG11PrimeProductAtoms
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro m hm
  let F := goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m
  have hFrange : F ⊆ range N := by
    intro p hp
    obtain ⟨_, _, _, _, _, hprod, _⟩ := mem_goldbachG11ProductFirstPrimeFiber_iff.mp hp
    have hm0 := (goldbachG11ProductSupport_data hm).1
    have hpm : p ≤ p*m := by simpa using Nat.mul_le_mul_left p hm0
    exact mem_range.mpr (hpm.trans_lt hprod)
  have hfilter : (range N).filter (fun p => p ∈ F) = F := by
    ext p
    exact ⟨fun h => (mem_filter.mp h).2,
      fun h => mem_filter.mpr ⟨hFrange h, h⟩⟩
  rw [← sum_filter, hfilter]
  symm
  calc
    _ = ∑ _p ∈ F, (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ) := by
      apply sum_congr rfl
      intro p hp
      exact goldbachG11RectangleWeight_of_firstPrimeFiber hp
    _ = _ := by simp [F, mul_comm]

/-- A positive cover may overlap; no output or body-product injectivity is asserted. -/
theorem goldbachG11_finite_positive_cover {ι κ : Type*} (S : Finset ι) (K : Finset κ)
    (R : κ → Finset ι) (f : ι → ℝ) (hf : ∀ v, 0 ≤ f v)
    (hc : ∀ v ∈ S, ∃ k ∈ K, v ∈ R k) :
    ∑ v ∈ S, f v ≤ ∑ k ∈ K, ∑ v ∈ R k, f v := by
  calc
    _ ≤ ∑ v ∈ S, ∑ k ∈ K, if v ∈ R k then f v else 0 := by
      apply sum_le_sum
      intro v hv
      obtain ⟨k, hk, hvk⟩ := hc v hv
      have h := single_le_sum (s := K) (a := k)
        (f := fun j => if v ∈ R j then f v else 0)
        (fun j _ => by split_ifs; exact hf v; exact le_rfl) hk
      simpa only [if_pos hvk] using h
    _ = ∑ k ∈ K, ∑ v ∈ S.filter (fun v => v ∈ R k), f v := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ _ := sum_le_sum (fun k _ => sum_le_sum_of_subset_of_nonneg
      (fun v hv => (mem_filter.mp hv).2) (fun v _ _ => hf v))

/-- The true G11 good count is bounded by the positive rectangular prime masses
once the actual finite prime/product atoms are covered. No geometric cover is assumed proved. -/
theorem goldbachG11GoodSwitchedTotal_le_rectanglePrimeMass_cover {κ : Type*}
    (N : ℕ) (ε : ℝ) (K : Finset κ) (U V : κ → Finset ℕ)
    (hc : ∀ m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)),
      ∀ p ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m,
        ∃ k ∈ K, m ∈ U k ∧ p ∈ V k) :
    (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      ∑ k ∈ K, goldbachG11RectanglePrimeMass N (U k) (V k) := by
  let f := fun v : ℕ × ℕ => goldbachG11RectangleWeight N v *
    (if ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs.Prime then 1 else 0)
  have hf : ∀ v, 0 ≤ f v := by
    intro v
    apply mul_nonneg (goldbachG11RectangleWeight_nonneg N v)
    split_ifs <;> norm_num
  rw [goldbachG11GoodSwitchedTotal_eq_weighted_atoms]
  have he : (∑ v ∈ goldbachG11PrimeProductAtoms N ε, goldbachG11RectangleWeight N v) =
      ∑ v ∈ goldbachG11PrimeProductAtoms N ε, f v := by
    apply sum_congr rfl
    rintro ⟨m,p⟩ hv
    obtain ⟨_, _, _, _, _, hprod, hout⟩ :=
      mem_goldbachG11ProductFirstPrimeFiber_iff.mp (mem_filter.mp hv).2
    have hp : ((N : ℤ)-(m : ℤ)*p).natAbs.Prime := by
      rw [MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.g9IntegerFibre_original
        N m p (by simpa [Nat.mul_comm] using hprod.le)]
      simpa [Nat.mul_comm] using hout
    simp only [f, if_pos hp, mul_one]
  rw [he]
  apply goldbachG11_finite_positive_cover _ K (fun k => U k ×ˢ V k) f hf
  rintro ⟨m,p⟩ hv
  obtain ⟨hm, hp⟩ := mem_filter.mp hv
  obtain ⟨k, hk, hmk, hpk⟩ := hc m (mem_product.mp hm).1 p hp
  exact ⟨k, hk, mem_product.mpr ⟨hmk,hpk⟩⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig