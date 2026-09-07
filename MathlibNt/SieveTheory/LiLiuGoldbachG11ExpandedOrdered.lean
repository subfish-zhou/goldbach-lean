import MathlibNt.SieveTheory.LiLiuGoldbachG11ExpandedMother

open Finset LiLiuPrereqBuchstab
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11ExpandedMotherSlice (N : ℕ) (ρ : ℝ) (h : ℝ → ℝ) (a : ℕ → ℕ → Prop) : ℝ :=
  ∑ u ∈ goldbachG11GoodSwitchedBodies N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),
    ∑ p ∈ (goldbachG11ExpandedPrimeWindow N ρ (goldbachG11SwitchedBodyProd u)).filter
      (a (goldbachG11SwitchedBodyProd u)), h (Real.log (p : ℝ)/Real.log (N : ℝ))

def goldbachG11ExpandedRoughMass (N : ℕ) (ρ : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),
    h (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ))*
      (roughCount (ρ^2*N/goldbachG11LabelProd v) v.2.2.2 : ℝ)

theorem goldbachG11ExpandedMother_split (N : ℕ) (ρ : ℝ) (h : ℝ → ℝ) (hh : ∀ r, 0 ≤ h r) :
    goldbachG11ExpandedMotherMass N ρ h ≤
      goldbachG11ExpandedMotherSlice N ρ h (fun m p => p ≤ m.minFac ∧ ¬p ∣ N)+
      goldbachG11ExpandedMotherSlice N ρ h (fun _ p => p ∣ N)+
      goldbachG11ExpandedMotherSlice N ρ h (fun m p => m.minFac < p) := by
  unfold goldbachG11ExpandedMotherMass goldbachG11ExpandedMotherSlice
  rw [← sum_add_distrib,← sum_add_distrib]
  apply sum_le_sum
  intro u _
  simp only [sum_filter,← sum_add_distrib]
  apply sum_le_sum
  intro p _
  split_ifs <;> first | omega | linarith [hh (Real.log (p : ℝ)/Real.log (N : ℝ))]

/-- The original five coordinates survive the enlarged upper endpoint. -/
theorem goldbachG11Expanded_ordered_pair_mem {N p : ℕ} {ρ : ℝ} {u : GoldbachG11SwitchedBody}
    (hu : u ∈ goldbachG11GoodSwitchedBodies N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)))
    (hp : p ∈ goldbachG11ExpandedPrimeWindow N ρ (goldbachG11SwitchedBodyProd u))
    (hpq : p ≤ (goldbachG11SwitchedBodyProd u).minFac) (hpN : ¬p ∣ N) :
    (⟨u.1,u.2.1,p,u.2.2.1⟩ : GoldbachG11Label) ∈
      goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
    u.2.2.2 ∈ roughNumbers (ρ^2*N/goldbachG11LabelProd ⟨u.1,u.2.1,p,u.2.2.1⟩) u.2.2.1 := by
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1
  obtain ⟨_,hpp,hzp,_hmin,hprod⟩ := mem_filter.mp hp
  rw [goldbachG11SwitchedBodyProd_minFac huB] at hpq
  rcases u with ⟨t,s,q,k⟩
  obtain ⟨hq,hs,ht,hcop,_hzq,hqs,hst,htb,hk,_,hrough,_⟩ := mem_goldbachG11SwitchedBodies_iff.mp huB
  have hv : (⟨t,s,p,q⟩ : GoldbachG11Label) ∈
      goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) :=
    mem_goldbachG11Labels_iff.mpr ⟨hpp,hq,hs,ht,by
      simpa only [Nat.mul_assoc] using (hpp.coprime_iff_not_dvd.mpr hpN).mul_left hcop,
      hzp,hpq,hqs,hst,htb⟩
  refine ⟨hv,mem_roughNumbers.mpr ⟨hk,?_,(goldbachG11_rough_iff_survives _ _).mpr hrough⟩⟩
  apply (le_div_iff₀ (show (0 : ℝ) < goldbachG11LabelProd ⟨t,s,p,q⟩ by
    exact_mod_cast goldbachG11LabelProd_pos hv)).2
  have he : (k : ℝ)*(goldbachG11LabelProd ⟨t,s,p,q⟩ : ℝ) =
      (goldbachG11SwitchedBodyProd ⟨t,s,q,k⟩ : ℝ)*p := by
    simp only [goldbachG11LabelProd,goldbachG11SwitchedBodyProd,Nat.cast_mul]
    ring
  rw [he]
  exact hprod.le

theorem goldbachG11Expanded_ordered_le_rough (N : ℕ) (ρ : ℝ) (h : ℝ → ℝ) (hh : ∀ r, 0 ≤ h r) :
    goldbachG11ExpandedMotherSlice N ρ h (fun m p => p ≤ m.minFac ∧ ¬p ∣ N) ≤
      goldbachG11ExpandedRoughMass N ρ h := by
  let S := (goldbachG11GoodSwitchedBodies N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))).sigma
    (fun u => (goldbachG11ExpandedPrimeWindow N ρ (goldbachG11SwitchedBodyProd u)).filter
      (fun p => p ≤ (goldbachG11SwitchedBodyProd u).minFac ∧ ¬p ∣ N))
  let T := (goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))).sigma
    (fun v => roughNumbers (ρ^2*N/goldbachG11LabelProd v) v.2.2.2)
  let f : (Σ _u : GoldbachG11SwitchedBody,ℕ) → (Σ _v : GoldbachG11Label,ℕ) :=
    fun a => ⟨⟨a.1.1,a.1.2.1,a.2,a.1.2.2.1⟩,a.1.2.2.2⟩
  let g : (Σ _v : GoldbachG11Label,ℕ) → ℝ := fun a => h (Real.log (a.1.2.2.1 : ℝ)/Real.log (N : ℝ))
  have hmap : ∀ a ∈ S, f a ∈ T := by
    rintro ⟨u,p⟩ ha
    obtain ⟨hu,hp⟩ := mem_sigma.mp ha
    obtain ⟨hp,hpq,hpN⟩ := mem_filter.mp hp
    exact mem_sigma.mpr (goldbachG11Expanded_ordered_pair_mem hu hp hpq hpN)
  have hinj : Function.Injective f := by
    rintro ⟨⟨t,s,q,k⟩,p⟩ ⟨⟨t',s',q',k'⟩,p'⟩ he
    have ht := congrArg (fun a => a.1.1) he
    have hs := congrArg (fun a => a.1.2.1) he
    have hp := congrArg (fun a => a.1.2.2.1) he
    have hq := congrArg (fun a => a.1.2.2.2) he
    have hk := congrArg (fun a => a.2) he
    dsimp [f] at ht hs hp hq hk
    subst t'; subst s'; subst p'; subst q'; subst k'
    rfl
  have hsub : S.image f ⊆ T := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := mem_image.mp ha
    exact hmap v hv
  calc
    _ = ∑ a ∈ S,g (f a) := by simp only [S,g,f,sum_sigma,goldbachG11ExpandedMotherSlice]
    _ = ∑ a ∈ S.image f,g a := (sum_image (fun _ _ _ _ he => hinj he)).symm
    _ ≤ ∑ a ∈ T,g a := sum_le_sum_of_subset_of_nonneg hsub (by intro a _ _; exact hh _)
    _ = _ := by simp only [T,g,sum_sigma,sum_const,nsmul_eq_mul,roughCount,goldbachG11ExpandedRoughMass,mul_comm]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig