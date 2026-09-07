import MathlibNt.SieveTheory.LiLiuGoldbachG11ExpandedOrdered

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11ExpandedPrimeWindow_product_nat {N m p : ℕ} {ρ : ℝ}
    (hρ : 1 ≤ ρ) (hρu : ρ ≤ 5/4) (hp : p ∈ goldbachG11ExpandedPrimeWindow N ρ m) :
    m*p ≤ 2*N := by
  have hprod := (mem_filter.mp hp).2.2.2.2
  have hr : ρ^2 ≤ (2 : ℝ) := by nlinarith
  have hh := hprod.le.trans (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg N))
  exact_mod_cast hh

theorem goldbachG11Expanded_divisor_cards {N : ℕ} (hN : 4 ≤ N) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (hρu : ρ ≤ 5/4) :
    (∑ m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),
      (((goldbachG11ExpandedPrimeWindow N ρ m).filter (fun p => p ∣ N)).card : ℝ)) ≤
      42*N/(N : ℝ)^(4/53 : ℝ) := by
  let z := (N : ℝ)^(4/53 : ℝ)
  let E := goldbachG11ProductSupport N z ((N : ℝ)^(4/33 : ℝ))
  let W := goldbachG11ExpandedPrimeWindow N ρ
  let L := largePrimeDivisors N z
  have hz : 0 < z := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hn0 : N ≠ 0 := by omega
  have hsub (m : ℕ) : (W m).filter (fun p => p ∣ N) ⊆ L := by
    intro p hp
    obtain ⟨hpW,hpN⟩ := mem_filter.mp hp
    obtain ⟨_,hpp,hzp,_⟩ := mem_filter.mp hpW
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp,hpN,hn0⟩,hzp⟩
  have hcard (m : ℕ) : (((W m).filter (fun p => p ∣ N)).card : ℝ) =
      ∑ p ∈ L,if p ∈ W m then (1 : ℝ) else 0 := by
    calc
      _ = ∑ p ∈ (W m).filter (fun p => p ∣ N),if p ∈ W m then (1 : ℝ) else 0 := by
        simp only [sum_boole,filter_filter]
        congr 2
        apply filter_congr
        intro p hp
        simp [hp]
      _ = _ := sum_subset (hsub m) (by
        intro p hpL hp
        apply if_neg
        intro hpW
        exact hp (mem_filter.mpr ⟨hpW,(Nat.mem_primeFactors.mp (mem_filter.mp hpL).1).2.1⟩))
  have hfiber (p : ℕ) (hp : p ∈ L) : ((E.filter (fun m => p ∈ W m)).card : ℝ) ≤ 2*N/(p : ℝ) := by
    have hpp := (Nat.mem_primeFactors.mp (mem_filter.mp hp).1).1
    have hs : E.filter (fun m => p ∈ W m) ⊆ Icc 1 (2*N/p) := by
      intro m hm
      obtain ⟨hmE,hpW⟩ := mem_filter.mp hm
      exact mem_Icc.mpr ⟨(goldbachG11ProductSupport_data hmE).1,
        (Nat.le_div_iff_mul_le hpp.pos).2 (goldbachG11ExpandedPrimeWindow_product_nat hρ hρu hpW)⟩
    have hc : (E.filter (fun m => p ∈ W m)).card ≤ 2*N/p := by
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card hs
    have hh := (Nat.cast_le.mpr hc : ((E.filter (fun m => p ∈ W m)).card : ℝ) ≤ (2*N/p : ℕ))
    exact hh.trans (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Nat.cast_div_le : ((2*N/p : ℕ) : ℝ) ≤ ((2*N : ℕ) : ℝ)/p))
  change (∑ m ∈ E,(((W m).filter (fun p => p ∣ N)).card : ℝ)) ≤ 42*N/z
  calc
    _ = ∑ m ∈ E,∑ p ∈ L,if p ∈ W m then (1 : ℝ) else 0 := sum_congr rfl (fun m _ => hcard m)
    _ = ∑ p ∈ L,((E.filter (fun m => p ∈ W m)).card : ℝ) := by rw [sum_comm]; simp only [sum_boole]
    _ ≤ ∑ p ∈ L,2*N/(p : ℝ) := sum_le_sum hfiber
    _ ≤ ∑ _p ∈ L,2*N/z := sum_le_sum (fun p hp => div_le_div_of_nonneg_left (by positivity) hz (mem_filter.mp hp).2)
    _ = (L.card : ℝ)*(2*N/z) := by simp
    _ ≤ 21*(2*N/z) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast goldbachG11_largePrimeDivisors_card_le_twenty_one hN) (by positivity)
    _ = _ := by ring

theorem goldbachG11Expanded_divisor_mass {N : ℕ} (hN : 4 ≤ N) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (hρu : ρ ≤ 5/4) (h : ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H) (hh : ∀ r,h r ≤ H) :
    goldbachG11ExpandedMotherSlice N ρ h (fun _ p => p ∣ N) ≤
      16800*H*N/(N : ℝ)^(4/53 : ℝ) := by
  classical
  let W := fun m => (goldbachG11ExpandedPrimeWindow N ρ m).filter (fun p => p ∣ N)
  have heq : goldbachG11ExpandedMotherSlice N ρ h (fun _ p => p ∣ N) =
      ∑ u ∈ goldbachG11GoodSwitchedBodies N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),
        ∑ p ∈ W (goldbachG11SwitchedBodyProd u),h (Real.log (p : ℝ)/Real.log (N : ℝ)) := by
    unfold goldbachG11ExpandedMotherSlice
    apply sum_congr rfl
    intro u _
    apply sum_congr
    · ext p
      simp only [W,mem_filter]
    · intro p _; rfl
  rw [heq]
  rw [goldbachG11GoodSwitchedBodies_sum_product_real N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
    (fun m => ∑ p ∈ W m,h (Real.log (p : ℝ)/Real.log (N : ℝ)))]
  have hc := goldbachG11Expanded_divisor_cards hN hρ hρu
  calc
    _ ≤ ∑ m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),
        (400*H)*((W m).card : ℝ) := by
      apply sum_le_sum
      intro m _
      have hs : (∑ p ∈ W m,h (Real.log (p : ℝ)/Real.log (N : ℝ))) ≤ ((W m).card : ℝ)*H := by
        calc
          _ ≤ ∑ _p ∈ W m,H := sum_le_sum (fun p _ => hh (Real.log (p : ℝ)/Real.log (N : ℝ)))
          _ = _ := by simp
      have ha : (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) m : ℝ) ≤ 400 := by
        exact_mod_cast goldbachG11ProductCoefficient_le_four_hundred N m
      exact (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right ha (mul_nonneg (Nat.cast_nonneg _) hH)).trans_eq (by ring))
    _ = (400*H)*∑ m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),((W m).card : ℝ) := (mul_sum _ _ _).symm
    _ ≤ (400*H)*(42*N/(N : ℝ)^(4/53 : ℝ)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig