import MathlibNt.SieveTheory.LiLiuGoldbachG11GridDisjointEnvelope

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The finite product-fibre identity for genuinely real weights, not an
invalid cast of the integer-valued grouping theorem. -/
theorem goldbachG11GoodSwitchedBodies_sum_product_real (N : ℕ) (z b : ℝ) (f : ℕ → ℝ) :
    (∑ u ∈ goldbachG11GoodSwitchedBodies N z b,f (goldbachG11SwitchedBodyProd u)) =
      ∑ m ∈ goldbachG11ProductSupport N z b,(goldbachG11ProductCoefficient N z b m : ℝ)*f m := by
  have hs : (goldbachG11GoodSwitchedBodies N z b).filter
      (fun u => goldbachG11SwitchedBodyProd u ∈ goldbachG11ProductSupport N z b) =
      goldbachG11GoodSwitchedBodies N z b := by
    apply filter_eq_self.mpr
    intro u hu
    exact mem_goldbachG11ProductSupport_iff.mpr ⟨u,hu,rfl⟩
  have hf := sum_fiberwise_eq_sum_filter (goldbachG11GoodSwitchedBodies N z b)
    (goldbachG11ProductSupport N z b) goldbachG11SwitchedBodyProd (fun u => f (goldbachG11SwitchedBodyProd u))
  rw [hs] at hf
  rw [← hf]
  apply sum_congr rfl
  intro m _
  calc
    _ = ∑ _u ∈ goldbachG11ProductFiber N z b m,f m := by
      apply sum_congr rfl
      intro u hu
      rw [(mem_goldbachG11ProductFiber_iff.mp hu).2]
    _ = _ := by simp [goldbachG11ProductCoefficient]

def goldbachG11ExpandedPrimeWindow (N : ℕ) (ρ : ℝ) (m : ℕ) : Finset ℕ :=
  (range (2*N+1)).filter fun p => p.Prime ∧ (N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ) ∧
    (p : ℝ) < ρ*m.minFac ∧ (m : ℝ)*p < ρ^2*N

def goldbachG11ExpandedMotherMass (N : ℕ) (ρ : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∑ u ∈ goldbachG11GoodSwitchedBodies N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),
    ∑ p ∈ goldbachG11ExpandedPrimeWindow N ρ (goldbachG11SwitchedBodyProd u),
      h (Real.log (p : ℝ)/Real.log (N : ℝ))

/-- Reconstruct every retained body label from the raw coefficient, without
any injectivity assumption on the product map. The product and ordering
extensions, and the absent p-coprimality filter, remain explicit in the window. -/
theorem goldbachG11WeightedGridMass_le_expandedMother {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    (h : ℝ → ℝ) (hh : ∀ r : ℝ, 0 ≤ h r) :
    goldbachG11WeightedGridMass N ε ρ h ≤ goldbachG11ExpandedMotherMass N ρ h := by
  let S := (goldbachG11ExpandedGridPairs N ε ρ).filter fun v => v.2.Prime
  let T := (goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))).sigma
    (goldbachG11ExpandedPrimeWindow N ρ)
  let f : (ℕ × ℕ) → (Σ _m : ℕ,ℕ) := fun v => ⟨v.1,v.2⟩
  let g : (Σ _m : ℕ,ℕ) → ℝ := fun v =>
    (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) v.1 : ℝ)*
      h (Real.log (v.2 : ℝ)/Real.log (N : ℝ))
  have hsrc : goldbachG11WeightedGridMass N ε ρ h = ∑ v ∈ S,g (f v) := by
    rw [goldbachG11WeightedGridMass_eq_union hρ hρu hbig h]
    dsimp [S,g,f]
    rw [sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases hp : v.2.Prime <;>
      simp only [goldbachG11AllPrimeWeight,primeSWBeta,hp,ite_true,ite_false,mul_one,mul_zero,zero_mul]
  have hmap : ∀ v ∈ S, f v ∈ T := by
    intro v hv
    obtain ⟨hv,hp⟩ := mem_filter.mp hv
    obtain ⟨hm,hz,hmin,hprod⟩ := goldbachG11ExpandedGridPairs_data hρ hρu hbig hv
    have hmS := (mem_filter.mp hm).1
    have hm1 : (1 : ℝ) ≤ v.1 := by exact_mod_cast (goldbachG11ProductSupport_data hmS).1
    have hρ2 : ρ^2 ≤ (2 : ℝ) := by nlinarith
    have hhN := mul_le_mul_of_nonneg_right hρ2 (Nat.cast_nonneg N)
    have hpN : v.2 ≤ 2*N := by
      have hpNN : (v.2 : ℝ) ≤ 2*N := by nlinarith [show (0 : ℝ) ≤ v.2 from Nat.cast_nonneg _]
      exact_mod_cast hpNN
    exact mem_sigma.mpr ⟨hmS,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hpN),hp,hz,hmin,hprod⟩⟩
  have hinj : Function.Injective f := by
    intro v w he
    exact congrArg (fun x : (Σ _m : ℕ,ℕ) => (x.1,x.2)) he
  have hsub : S.image f ⊆ T := by
    intro t ht
    obtain ⟨v,hv,rfl⟩ := mem_image.mp ht
    exact hmap v hv
  have htgt : (∑ v ∈ T,g v) = goldbachG11ExpandedMotherMass N ρ h := by
    unfold goldbachG11ExpandedMotherMass
    rw [goldbachG11GoodSwitchedBodies_sum_product_real N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
      (fun m => ∑ p ∈ goldbachG11ExpandedPrimeWindow N ρ m,h (Real.log (p : ℝ)/Real.log (N : ℝ)))]
    simp only [T,g,sum_sigma,mul_sum]
  calc
    _ = ∑ v ∈ S,g (f v) := hsrc
    _ = ∑ v ∈ S.image f,g v := (sum_image (fun _ _ _ _ he => hinj he)).symm
    _ ≤ ∑ v ∈ T,g v := sum_le_sum_of_subset_of_nonneg hsub (by intro v _ _; exact mul_nonneg (Nat.cast_nonneg _) (hh _))
    _ = _ := htgt

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig