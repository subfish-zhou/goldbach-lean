import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindowAP
import MathlibNt.SieveTheory.LiLiuGoldbachG11MainMassTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabUpperMass

open scoped BigOperators
open Classical Finset LiLiuPrereqBuchstab
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG12MainMassGood (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
    (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => ¬r ∣ N)).card : ℝ)
def goldbachG12MainMassBad (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
    (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => r ∣ N)).card : ℝ)

theorem goldbachG12WindowWeightSum_eq_good_add_bad (N : ℕ) (ε : ℝ) :
    (∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
      ((goldbachG11LinkedPrimeWindow N ε m).card : ℝ)) =
      goldbachG12MainMassGood N ε + goldbachG12MainMassBad N ε := by
  unfold goldbachG12MainMassGood goldbachG12MainMassBad
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  rw [← mul_add, ← Nat.cast_add]
  congr 2
  simpa only [add_comm] using
    (card_filter_add_card_filter_not (s := goldbachG11LinkedPrimeWindow N ε m)
      (p := fun r => r ∣ N)).symm

theorem goldbachG12NormalizedCoefficient_mul_four_hundred (N m : ℕ) :
    400 * goldbachG12NormalizedCoefficient N m =
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) := by
  unfold goldbachG12NormalizedCoefficient
  ring

/-- Closed upper product and prime-coordinate bounds of the actual relaxed window. -/
theorem goldbachG12MainMass_window_data {N m r : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG12ActiveProductSupport N)
    (hr : r ∈ goldbachG11LinkedPrimeWindow N ε m) :
    r.Prime ∧ (N : ℝ) ^ (4 / 53 : ℝ) ≤ (r : ℝ) ∧
      r ≤ m.minFac ∧ r * m ≤ N := by
  obtain ⟨_, hp, hlo, hhi⟩ := mem_filter.mp hr
  have hlow : max ((N : ℝ) ^ (4 / 53 : ℝ)) (ε * N / m) < (r : ℝ) := by
    rcases min_lt_iff.mp hlo with hbad | hgood
    · exact False.elim (not_lt_of_ge hhi hbad)
    · exact hgood
  exact ⟨hp, ((le_max_left _ _).trans_lt hlow).le,
    by exact_mod_cast hhi.trans (min_le_left _ _),
    goldbachG12LinkedPrimeWindow_product_le hm hr⟩

/-- The coordinate permutation lands on the original cross, not the larger G11 domain. -/
theorem goldbachG12MainMass_good_pair_mem {N r : ℕ} {ε : ℝ}
    {u : GoldbachG11SwitchedBody}
    (hu : u ∈ goldbachG12GoodCrossBodies N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)))
    (hm : goldbachG11SwitchedBodyProd u ∈ goldbachG12ActiveProductSupport N)
    (hr : r ∈ goldbachG11LinkedPrimeWindow N ε (goldbachG11SwitchedBodyProd u))
    (hrN : ¬r ∣ N) :
    (⟨u.1,u.2.1,r,u.2.2.1⟩ : GoldbachG11Label) ∈
      goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
    u.2.2.2 ∈ roughNumbers
      ((N : ℝ)/goldbachG11LabelProd ⟨u.1,u.2.1,r,u.2.2.1⟩) u.2.2.1 := by
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp
    (goldbachG12GoodCrossBodies_subset _ _ _ _ hu)).1
  have hcross := (mem_filter.mp (mem_filter.mp hu).1).2
  obtain ⟨hrp,hzr,hrq,hprod⟩ := goldbachG12MainMass_window_data hm hr
  rw [goldbachG11SwitchedBodyProd_minFac huB] at hrq
  rcases u with ⟨t,s,q,k⟩
  obtain ⟨hq,hs,ht,hcop,_,hqs,_,htc,hk,_,hrough,_⟩ := mem_goldbachG11SwitchedBodies_iff.mp huB
  have hv : (⟨t,s,r,q⟩ : GoldbachG11Label) ∈
      goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) :=
    mem_goldbachG12Labels_iff.mpr ⟨hrp,hq,hs,ht,by
      simpa only [Nat.mul_assoc] using (hrp.coprime_iff_not_dvd.mpr hrN).mul_left hcop,
      hzr,hrq,hqs,hcross.1,hcross.2,htc⟩
  have hPk : goldbachG11LabelProd ⟨t,s,r,q⟩ * k ≤ N := by
    simpa only [goldbachG11LabelProd,goldbachG11SwitchedBodyProd,Nat.mul_assoc] using hprod
  refine ⟨hv,mem_roughNumbers.mpr ⟨hk,?_,(goldbachG11_rough_iff_survives _ _).mpr hrough⟩⟩
  apply (le_div_iff₀ (show (0 : ℝ) < goldbachG11LabelProd ⟨t,s,r,q⟩ by
    exact_mod_cast goldbachG11LabelProd_pos (goldbachG12Labels_subset_goldbachG11Labels _ _ _ _ hv))).mpr
  exact_mod_cast (by simpa only [Nat.mul_comm] using hPk)

private def g12ActiveGoodWindow (N : ℕ) (ε : ℝ) (m : ℕ) : Finset ℕ :=
  if m ∈ goldbachG12ActiveProductSupport N then
    (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => ¬r ∣ N) else ∅

theorem goldbachG12MainMassGood_le_fullRough (N : ℕ) (ε : ℝ) :
    400 * goldbachG12MainMassGood N ε ≤ goldbachG12FullRoughMass N := by
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  let b : ℝ := (N : ℝ) ^ (4 / 33 : ℝ)
  let c : ℝ := (N : ℝ) ^ (3/11 : ℝ)
  let W := g12ActiveGoodWindow N ε
  have hgroup :
      (∑ u ∈ goldbachG12GoodCrossBodies N z b c,
        ((W (goldbachG11SwitchedBodyProd u)).card : ℝ)) =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
    exact_mod_cast goldbachG12GoodCross_sum_product N z b c
      (fun m => ((W m).card : ℤ))
  have hmass : 400 * goldbachG12MainMassGood N ε =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
    unfold goldbachG12MainMassGood
    rw [mul_sum]
    calc
      _ = ∑ m ∈ goldbachG12ActiveProductSupport N,
          (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
        apply sum_congr rfl
        intro m hm
        simp only [W, g12ActiveGoodWindow, if_pos hm,
          ← mul_assoc, goldbachG12NormalizedCoefficient_mul_four_hundred, z, b, c]
      _ = _ := sum_subset (filter_subset _ _) (by
        intro m _ hm
        simp only [W, g12ActiveGoodWindow, if_neg hm, card_empty, Nat.cast_zero, mul_zero])
  let S := (goldbachG12GoodCrossBodies N z b c).sigma
    (fun u => W (goldbachG11SwitchedBodyProd u))
  let T := (goldbachG12Labels N z b c).sigma
    (fun v => roughNumbers ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2)
  let f : (Σ _u : GoldbachG11SwitchedBody, ℕ) → (Σ _v : GoldbachG11Label, ℕ) :=
    fun a => ⟨⟨a.1.1, a.1.2.1, a.2, a.1.2.2.1⟩, a.1.2.2.2⟩
  have hmap : ∀ a ∈ S, f a ∈ T := by
    rintro ⟨u, r⟩ ha
    obtain ⟨hu, hr⟩ := mem_sigma.mp ha
    have hm : goldbachG11SwitchedBodyProd u ∈ goldbachG12ActiveProductSupport N := by
      by_contra hn
      simp only [W, g12ActiveGoodWindow, if_neg hn, notMem_empty] at hr
    have hr' : r ∈ (goldbachG11LinkedPrimeWindow N ε
        (goldbachG11SwitchedBodyProd u)).filter (fun r => ¬r ∣ N) := by
      simpa only [W, g12ActiveGoodWindow, if_pos hm] using hr
    exact mem_sigma.mpr
      (goldbachG12MainMass_good_pair_mem hu hm (mem_filter.mp hr').1 (mem_filter.mp hr').2)
  have hinj : Set.InjOn f S := by
    rintro ⟨⟨t, s, q, k⟩, r⟩ _ ⟨⟨t', s', q', k'⟩, r'⟩ _ he
    have ht := congrArg (fun a => a.1.1) he
    have hs := congrArg (fun a => a.1.2.1) he
    have hr := congrArg (fun a => a.1.2.2.1) he
    have hq := congrArg (fun a => a.1.2.2.2) he
    have hk := congrArg (fun a => a.2) he
    dsimp [f] at ht hs hr hq hk
    subst t'; subst s'; subst r'; subst q'; subst k'
    rfl
  have hc : S.card ≤ T.card := card_le_card_of_injOn f hmap hinj
  rw [hmass, ← hgroup]
  have hS : (S.card : ℝ) =
      ∑ u ∈ goldbachG12GoodCrossBodies N z b c,
        ((W (goldbachG11SwitchedBodyProd u)).card : ℝ) := by
    simp only [S, card_sigma, Nat.cast_sum]
  have hT : (T.card : ℝ) = goldbachG12FullRoughMass N := by
    simp only [T, card_sigma, Nat.cast_sum, goldbachG12FullRoughMass, roughCount, z, b, c]
  rw [← hS, ← hT]
  exact_mod_cast hc

theorem goldbachG12MainMassBad_le {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) :
    goldbachG12MainMassBad N ε ≤ 21 * N / (N : ℝ) ^ (4 / 53 : ℝ) := by
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  let L := largePrimeDivisors N z
  let E := goldbachG12ActiveProductSupport N
  let W := goldbachG11LinkedPrimeWindow N ε
  have hN0 : N ≠ 0 := by omega
  have hz : 0 < z := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hsub (m : ℕ) (hm : m ∈ E) : (W m).filter (fun r => r ∣ N) ⊆ L := by
    intro r hr
    obtain ⟨hrW, hrN⟩ := mem_filter.mp hr
    obtain ⟨hrp, hzr, _⟩ := goldbachG12MainMass_window_data hm hrW
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hrp, hrN, hN0⟩, hzr⟩
  have hcard (m : ℕ) (hm : m ∈ E) :
      (((W m).filter (fun r => r ∣ N)).card : ℝ) =
        ∑ r ∈ L, if r ∈ W m then (1 : ℝ) else 0 := by
    calc
      _ = ∑ _r ∈ (W m).filter (fun r => r ∣ N), (1 : ℝ) := by simp
      _ = ∑ r ∈ (W m).filter (fun r => r ∣ N),
          if r ∈ W m then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro r hr
        exact (if_pos (mem_filter.mp hr).1).symm
      _ = _ := sum_subset (hsub m hm) (by
        intro r hrL hr
        apply if_neg
        intro hrW
        exact hr (mem_filter.mpr ⟨hrW,
          (Nat.mem_primeFactors.mp (mem_filter.mp hrL).1).2.1⟩))
  have hfiber (r : ℕ) (hr : r ∈ L) :
      ((E.filter (fun m => r ∈ W m)).card : ℝ) ≤ (N : ℝ) / r := by
    have hrp := (Nat.mem_primeFactors.mp (mem_filter.mp hr).1).1
    have hmsub : E.filter (fun m => r ∈ W m) ⊆ Icc 1 (N / r) := by
      intro m hm
      obtain ⟨hmE, hrW⟩ := mem_filter.mp hm
      have hm0 := (goldbachG12ActiveProductSupport_data hmE).1
      have hprod := goldbachG12LinkedPrimeWindow_product_le hmE hrW
      exact mem_Icc.mpr ⟨hm0, (Nat.le_div_iff_mul_le hrp.pos).mpr
        (by simpa only [Nat.mul_comm] using hprod)⟩
    have hc : (E.filter (fun m => r ∈ W m)).card ≤ N / r := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hmsub
    exact (Nat.cast_le.mpr hc).trans Nat.cast_div_le
  calc
    goldbachG12MainMassBad N ε ≤
        ∑ m ∈ E, (((W m).filter (fun r => r ∣ N)).card : ℝ) := by
      apply sum_le_sum
      intro m _
      exact mul_le_of_le_one_left (Nat.cast_nonneg _)
        (goldbachG12NormalizedCoefficient_bounds N m).2
    _ = ∑ m ∈ E, ∑ r ∈ L, if r ∈ W m then (1 : ℝ) else 0 :=
      sum_congr rfl hcard
    _ = ∑ r ∈ L, ((E.filter (fun m => r ∈ W m)).card : ℝ) := by
      rw [sum_comm]
      simp only [sum_boole]
    _ ≤ ∑ r ∈ L, (N : ℝ) / r := sum_le_sum hfiber
    _ ≤ ∑ _r ∈ L, (N : ℝ) / z := by
      apply sum_le_sum
      intro r hr
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hz (mem_filter.mp hr).2
    _ = (L.card : ℝ) * ((N : ℝ) / z) := by simp
    _ ≤ 21 * ((N : ℝ) / z) :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast goldbachG11_largePrimeDivisors_card_le_twenty_one hN)
        (div_nonneg (Nat.cast_nonneg _) hz.le)
    _ = 21 * N / (N : ℝ) ^ (4 / 53 : ℝ) := by rw [mul_div_assoc]

/-- The lower window endpoint is discarded only for an upper bound.
The exceptional prime divisors of N are paid separately. -/
theorem goldbachG12WindowWeightSum_le_fullRough {N : ℕ}
    (hN : 4 ≤ N) (ε : ℝ) :
    400 * (∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
      ((goldbachG11LinkedPrimeWindow N ε m).card : ℝ)) ≤
      goldbachG12FullRoughMass N + 8400 * N / (N : ℝ) ^ (4 / 53 : ℝ) := by
  rw [goldbachG12WindowWeightSum_eq_good_add_bad, mul_add]
  apply add_le_add (goldbachG12MainMassGood_le_fullRough N ε)
  calc
    400 * goldbachG12MainMassBad N ε ≤
        400 * (21 * N / (N : ℝ) ^ (4 / 53 : ℝ)) :=
      mul_le_mul_of_nonneg_left (goldbachG12MainMassBad_le hN ε) (by norm_num)
    _ = 8400 * N / (N : ℝ) ^ (4 / 53 : ℝ) := by ring

/-- The same cross mother now has the uniform Buchstab upper mass.
This still precedes the output-prime sieve, which supplies another logarithm. -/
theorem goldbachG12WindowWeightSum_le_buchstab (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ,
      400 * (∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
        ((goldbachG11LinkedPrimeWindow N ε m).card : ℝ)) ≤
        goldbachG12BuchstabUpperMass N η + 8400 * N / (N : ℝ)^(4/53 : ℝ) := by
  obtain ⟨N₀,hN₀,hn⟩ := goldbachG12FullRoughMass_le_buchstabUpper η hη
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ε
  exact (goldbachG12WindowWeightSum_le_fullRough (hN₀.trans hN) ε).trans
    (add_le_add (hn N hN) le_rfl)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig