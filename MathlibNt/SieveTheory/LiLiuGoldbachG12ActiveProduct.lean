import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossProductPaid

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual cross support retains the upper bound on its least prime factor. -/
theorem goldbachG12ProductSupport_minFac_le {N m : ℕ} {z b c : ℝ}
    (hm : m ∈ goldbachG12ProductSupport N z b c) : (m.minFac : ℝ) ≤ b := by
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hm
  have hcross := (Finset.mem_filter.mp hu).1
  have hbody := (Finset.mem_filter.mp hcross).1
  rw [goldbachG11SwitchedBodyProd_minFac hbody]
  rcases u with ⟨t,s,q,k⟩
  obtain ⟨_,_,_,_,_,hqs,hsb,_⟩ := mem_goldbachG12CrossSwitchedBodies_iff.mp hcross
  exact (show (q : ℝ) ≤ s by exact_mod_cast hqs).trans hsb

/-- Any nonempty physical first-prime fibre already lies in the balanced range. -/
theorem goldbachG12_nonempty_productFiber_upper {N m : ℕ} {ε : ℝ}
    (hN : 2 ≤ N)
    (hf : (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).Nonempty) :
    (m : ℝ) < (N : ℝ)^(49/53 : ℝ) := by
  obtain ⟨r,hr⟩ := hf
  obtain ⟨_,_,hz,_,_,hrm,_⟩ := mem_goldbachG11ProductFirstPrimeFiber_iff.mp hr
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprod : (r : ℝ)*(m : ℝ) < N := by exact_mod_cast hrm
  have hzpos := Real.rpow_pos_of_pos hNp (4/53 : ℝ)
  apply (mul_lt_mul_iff_right₀ hzpos).mp
  calc
    (N : ℝ)^(4/53 : ℝ)*(m : ℝ) ≤ (r : ℝ)*m :=
      mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg _)
    _ < N := hprod
    _ = (N : ℝ)^(4/53 : ℝ)*(N : ℝ)^(49/53 : ℝ) := by
      rw [← Real.rpow_add hNp]
      norm_num

/-- Independent of epsilon and of the output sieve modulus. -/
noncomputable def goldbachG12ActiveProductSupport (N : ℕ) : Finset ℕ := by
  classical
  exact (goldbachG12ProductSupport N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))).filter
    (fun m => (m : ℝ) ≤ (N : ℝ)^(49/53 : ℝ))

noncomputable def goldbachG12NormalizedCoefficient (N m : ℕ) : ℝ :=
  (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ)/400

theorem goldbachG12NormalizedCoefficient_bounds (N m : ℕ) :
    goldbachG12NormalizedCoefficient N m ∈ Set.Icc (0 : ℝ) 1 := by
  have h : (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) ≤ 400 := by
    exact_mod_cast goldbachG12ProductCoefficient_le_four_hundred N m _ _
  constructor
  · unfold goldbachG12NormalizedCoefficient; positivity
  · unfold goldbachG12NormalizedCoefficient; linarith

/-- Exact support facts for the existing balanced prime-centered distribution theorem. -/
theorem goldbachG12ActiveProductSupport_data {N m : ℕ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    0 < m ∧ m < N ∧ Nat.Coprime m N ∧
      (N : ℝ)^(4/53 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (N : ℝ)^(49/53 : ℝ) ∧
      (N : ℝ)^(4/53 : ℝ) ≤ (m.minFac : ℝ) ∧
        (m.minFac : ℝ) ≤ (N : ℝ)^(4/33 : ℝ) := by
  obtain ⟨hm,hu⟩ := Finset.mem_filter.mp hm
  have hd := goldbachG12ProductSupport_data hm
  have hmin : m.minFac ≤ m := Nat.le_of_dvd hd.1 (Nat.minFac_dvd m)
  exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.trans (by exact_mod_cast hmin),hu,
    hd.2.2.2,goldbachG12ProductSupport_minFac_le hm⟩

/-- Restricting to the balanced support deletes only empty first-prime fibres.
The factor 400 restores the literal integer coefficient, including every representation. -/
theorem goldbachG12ProductPrimeTotal_eq_active (N : ℕ) (ε : ℝ) (hN : 2 ≤ N) :
    (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) =
      400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
        goldbachG12NormalizedCoefficient N m *
          ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ) := by
  classical
  have heq : (∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℤ)*
        (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card) =
      goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hm hnot
    have hu : ¬ (m : ℝ) ≤ (N : ℝ)^(49/53 : ℝ) := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hm,h⟩)
    have hf : goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro h
      exact hu (goldbachG12_nonempty_productFiber_upper hN h).le
    rw [hf, Finset.card_empty, Nat.cast_zero, mul_zero]
  rw [← heq, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  push_cast
  unfold goldbachG12NormalizedCoefficient
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
