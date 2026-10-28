import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughElementary

noncomputable section
open Classical Finset LiLiuPrereqBuchstab
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12FineGrid

namespace G12RoughBoundary

def nearWindow (N : ℕ) (ε a : ℝ) (m : ℕ) : Finset ℕ :=
  (goldbachG11LinkedPrimeWindow N ε m).filter fun r =>
    ¬r ∣ N ∧ (m.minFac : ℝ) ≤ a*r

def nearWindowMass (N : ℕ) (ε a : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N,
    goldbachG12NormalizedCoefficient N m * ((nearWindow N ε a m).card : ℝ)

/-- All body multiplicities, not merely one minFac witness, are injected. -/
theorem nearWindowMass_le_nearMass {N : ℕ} (ε a : ℝ) :
    400 * nearWindowMass N ε a ≤ nearMass N a := by
  let z : ℝ := (N : ℝ)^(4/53 : ℝ)
  let b : ℝ := (N : ℝ)^(4/33 : ℝ)
  let c : ℝ := (N : ℝ)^(3/11 : ℝ)
  let W : ℕ → Finset ℕ := fun m =>
    if m ∈ goldbachG12ActiveProductSupport N then nearWindow N ε a m else ∅
  have hgroup : (∑ v ∈ goldbachG12GoodCrossBodies N z b c,
      ((W (goldbachG11SwitchedBodyProd v)).card : ℝ)) =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
    exact_mod_cast goldbachG12GoodCross_sum_product N z b c
      (fun m => ((W m).card : ℤ))
  have hmass : 400 * nearWindowMass N ε a =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
    unfold nearWindowMass
    rw [mul_sum]
    calc
      _ = ∑ m ∈ goldbachG12ActiveProductSupport N,
          (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
        apply sum_congr rfl
        intro m hm
        simp only [W,if_pos hm,← mul_assoc,
          goldbachG12NormalizedCoefficient_mul_four_hundred,z,b,c]
      _ = _ := sum_subset (filter_subset _ _) (by
        intro m _ hm
        simp only [W,if_neg hm,card_empty,Nat.cast_zero,mul_zero])
  let S := (goldbachG12GoodCrossBodies N z b c).sigma
    (fun v => W (goldbachG11SwitchedBodyProd v))
  let T := (nearLabels N a).sigma (fun v => roughNumbers ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2)
  let f : (Σ _v : GoldbachG11SwitchedBody, ℕ) → (Σ _v : GoldbachG11Label, ℕ) :=
    fun a => ⟨⟨a.1.1,a.1.2.1,a.2,a.1.2.2.1⟩,a.1.2.2.2⟩
  have hmap : ∀ a ∈ S, f a ∈ T := by
    rintro ⟨v,r⟩ ha
    obtain ⟨hv,hr⟩ := mem_sigma.mp ha
    have hm : goldbachG11SwitchedBodyProd v ∈ goldbachG12ActiveProductSupport N := by
      by_contra hn
      simp only [W,if_neg hn,notMem_empty] at hr
    have hr' : r ∈ nearWindow N ε a (goldbachG11SwitchedBodyProd v) := by
      simpa only [W,if_pos hm] using hr
    obtain ⟨hrW,hrN,hnear⟩ := mem_filter.mp hr'
    obtain ⟨hl,hk⟩ := goldbachG12MainMass_good_pair_mem hv hm hrW hrN
    have hmin := goldbachG11SwitchedBodyProd_minFac
      (mem_goldbachG11GoodSwitchedBodies_iff.mp (goldbachG12GoodCrossBodies_subset _ _ _ _ hv)).1
    rw [hmin] at hnear
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨hl,hnear⟩,hk⟩
  have hinj : Set.InjOn f S := by
    rintro ⟨⟨t,s,q,k⟩,r⟩ _ ⟨⟨t',s',q',k'⟩,r'⟩ _ he
    have ht := congrArg (fun a => a.1.1) he
    have hs := congrArg (fun a => a.1.2.1) he
    have hr := congrArg (fun a => a.1.2.2.1) he
    have hq := congrArg (fun a => a.1.2.2.2) he
    have hk := congrArg (fun a => a.2) he
    dsimp [f] at ht hs hr hq hk
    subst t'; subst s'; subst r'; subst q'; subst k'
    rfl
  have hc : S.card ≤ T.card := card_le_card_of_injOn f hmap hinj
  have hS : (S.card : ℝ) = ∑ v ∈ goldbachG12GoodCrossBodies N z b c,
      ((W (goldbachG11SwitchedBodyProd v)).card : ℝ) := by
    simp only [S,card_sigma,Nat.cast_sum]
  have hT : (T.card : ℝ) = nearMass N a := by
    simp only [T,card_sigma,Nat.cast_sum,nearMass,roughCount]
  rw [hmass,← hgroup,← hS,← hT]
  exact_mod_cast hc


end G12RoughBoundary
