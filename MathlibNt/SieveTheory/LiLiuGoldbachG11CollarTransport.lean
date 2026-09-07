import MathlibNt.SieveTheory.LiLiuGoldbachG11ExpandedOrdered

open Finset LiLiuPrereqBuchstab
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Unordered q,s,t are deliberately an upper carrier. Its fourth coordinate
is the short integer p in q<p<=rho*q, not a rough cofactor. -/
def goldbachG11CollarBoxes (N : ℕ) (ρ : ℝ) : Finset GoldbachG11SwitchedBody :=
  let P := goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
  P.sigma fun _t => P.sigma fun _s => P.sigma fun q => Ioc q ⌊ρ*(q : ℝ)⌋₊

def goldbachG11CollarRoughMass (N : ℕ) (ρ : ℝ) : ℝ :=
  ∑ v ∈ goldbachG11CollarBoxes N ρ,
    (roughCount (ρ^2*N/goldbachG11SwitchedBodyProd v) v.2.2.1 : ℝ)

theorem goldbachG11Expanded_collar_pair_mem {N p : ℕ} {ρ : ℝ} {u : GoldbachG11SwitchedBody}
    (hu : u ∈ goldbachG11GoodSwitchedBodies N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)))
    (hp : p ∈ goldbachG11ExpandedPrimeWindow N ρ (goldbachG11SwitchedBodyProd u))
    (hqp : (goldbachG11SwitchedBodyProd u).minFac < p) :
    (⟨u.1,u.2.1,u.2.2.1,p⟩ : GoldbachG11SwitchedBody) ∈ goldbachG11CollarBoxes N ρ ∧
    u.2.2.2 ∈ roughNumbers (ρ^2*N/goldbachG11SwitchedBodyProd ⟨u.1,u.2.1,u.2.2.1,p⟩) u.2.2.1 := by
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1
  obtain ⟨_,hpp,_hzp,hprho,hprod⟩ := mem_filter.mp hp
  rw [goldbachG11SwitchedBodyProd_minFac huB] at hqp hprho
  rcases u with ⟨t,s,q,k⟩
  obtain ⟨hq,hs,ht,hcop,hzq,hqs,hst,htb,hk,_,hrough,_⟩ := mem_goldbachG11SwitchedBodies_iff.mp huB
  obtain ⟨hqsN,htN⟩ := Nat.coprime_mul_iff_left.mp hcop
  obtain ⟨hqN,hsN⟩ := Nat.coprime_mul_iff_left.mp hqsN
  have hqsR : (q : ℝ) ≤ s := by exact_mod_cast hqs
  have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hqP := mem_goldbachClosedPrimes_iff.mpr ⟨hq,hq.coprime_iff_not_dvd.mp hqN,hzq,(hqsR.trans hstR).trans htb⟩
  have hsP := mem_goldbachClosedPrimes_iff.mpr ⟨hs,hs.coprime_iff_not_dvd.mp hsN,hzq.trans hqsR,hstR.trans htb⟩
  have htP := mem_goldbachClosedPrimes_iff.mpr ⟨ht,ht.coprime_iff_not_dvd.mp htN,(hzq.trans hqsR).trans hstR,htb⟩
  have hpF : p ≤ ⌊ρ*(q : ℝ)⌋₊ :=
    (Nat.le_floor_iff ((Nat.cast_nonneg p).trans hprho.le)).2 hprho.le
  refine ⟨mem_sigma.mpr ⟨htP,mem_sigma.mpr ⟨hsP,mem_sigma.mpr ⟨hqP,mem_Ioc.mpr ⟨hqp,hpF⟩⟩⟩⟩,
    mem_roughNumbers.mpr ⟨hk,?_,(goldbachG11_rough_iff_survives _ _).mpr hrough⟩⟩
  have hd : (0 : ℝ) < goldbachG11SwitchedBodyProd ⟨t,s,q,p⟩ := by
    have hpp0 := hpp.pos
    have hq0 := hq.pos
    have hs0 := hs.pos
    have ht0 := ht.pos
    dsimp [goldbachG11SwitchedBodyProd]
    positivity
  apply (le_div_iff₀ hd).2
  have he : (k : ℝ)*(goldbachG11SwitchedBodyProd ⟨t,s,q,p⟩ : ℝ) =
      (goldbachG11SwitchedBodyProd ⟨t,s,q,k⟩ : ℝ)*p := by
    simp only [goldbachG11SwitchedBodyProd,Nat.cast_mul]
    ring
  rw [he]
  exact hprod.le

/-- Primality and ordering are dropped only on this positive collar upper
carrier. The source body and its rough cofactor still map injectively. -/
theorem goldbachG11Expanded_collar_le_rough (N : ℕ) (ρ : ℝ)
    (h : ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H) (hh : ∀ r,h r ≤ H) :
    goldbachG11ExpandedMotherSlice N ρ h (fun m p => m.minFac < p) ≤
      H*goldbachG11CollarRoughMass N ρ := by
  let S := (goldbachG11GoodSwitchedBodies N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))).sigma
    (fun u => (goldbachG11ExpandedPrimeWindow N ρ (goldbachG11SwitchedBodyProd u)).filter
      (fun p => (goldbachG11SwitchedBodyProd u).minFac < p))
  let T := (goldbachG11CollarBoxes N ρ).sigma
    (fun v => roughNumbers (ρ^2*N/goldbachG11SwitchedBodyProd v) v.2.2.1)
  let f : (Σ _u : GoldbachG11SwitchedBody,ℕ) → (Σ _v : GoldbachG11SwitchedBody,ℕ) :=
    fun a => ⟨⟨a.1.1,a.1.2.1,a.1.2.2.1,a.2⟩,a.1.2.2.2⟩
  have hmap : ∀ a ∈ S,f a ∈ T := by
    rintro ⟨u,p⟩ ha
    obtain ⟨hu,hp⟩ := mem_sigma.mp ha
    obtain ⟨hp,hqp⟩ := mem_filter.mp hp
    exact mem_sigma.mpr (goldbachG11Expanded_collar_pair_mem hu hp hqp)
  have hi : Function.LeftInverse f f := by rintro ⟨⟨t,s,q,k⟩,p⟩; rfl
  have hc : (S.card : ℝ) ≤ T.card := by
    exact_mod_cast card_le_card_of_injOn f hmap hi.injective.injOn
  have hsrc : goldbachG11ExpandedMotherSlice N ρ h (fun m p => m.minFac < p) =
      ∑ a ∈ S,h (Real.log (a.2 : ℝ)/Real.log (N : ℝ)) := by
    simp only [goldbachG11ExpandedMotherSlice,S,sum_sigma]
  calc
    _ = ∑ a ∈ S,h (Real.log (a.2 : ℝ)/Real.log (N : ℝ)) := hsrc
    _ ≤ ∑ _a ∈ S,H := sum_le_sum (fun a _ => hh _)
    _ = H*(S.card : ℝ) := by simp [mul_comm]
    _ ≤ H*(T.card : ℝ) := mul_le_mul_of_nonneg_left hc hH
    _ = _ := by simp only [T,card_sigma,Nat.cast_sum,roughCount,goldbachG11CollarRoughMass]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig