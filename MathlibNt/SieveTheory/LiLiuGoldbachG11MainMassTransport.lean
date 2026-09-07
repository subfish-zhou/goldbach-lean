import MathlibNt.SieveTheory.LiLiuGoldbachG11GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG11CofactorWindow

open scoped BigOperators
open Classical Finset LiLiuPrereqBuchstab

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The full positive rough mother, with actual prime labels and no output-prime filter. -/
def goldbachG11FullRoughMass (N : ℕ) : ℝ :=
  ∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
    (roughCount ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 : ℝ)

def goldbachG11MainMassGood (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
    goldbachG11EffectiveProductCoefficient N ε m *
      (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => ¬r ∣ N)).card : ℝ)

def goldbachG11MainMassBad (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
    goldbachG11EffectiveProductCoefficient N ε m *
      (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => r ∣ N)).card : ℝ)

theorem goldbachG11FullRoughMass_nonneg (N : ℕ) :
    0 ≤ goldbachG11FullRoughMass N :=
  sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem goldbachG11PrimeWindowMainMass_eq_good_add_bad (N : ℕ) (ε : ℝ) :
    goldbachG11PrimeWindowMainMass N ε =
      goldbachG11MainMassGood N ε + goldbachG11MainMassBad N ε := by
  unfold goldbachG11PrimeWindowMainMass goldbachG11PrimeWindowWeight
    goldbachG11MainMassGood goldbachG11MainMassBad
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  rw [← mul_add, ← Nat.cast_add]
  congr 2
  simpa only [add_comm] using
    (card_filter_add_card_filter_not (s := goldbachG11LinkedPrimeWindow N ε m)
      (p := fun r => r ∣ N)).symm

/-- Closed upper product and prime-coordinate bounds of the actual relaxed window. -/
theorem goldbachG11MainMass_window_data {N m r : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε)
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
    goldbachG11LinkedPrimeWindow_product_le hm hr⟩

/-- Remove one prime divisor before applying the existing strict `n < N` bound. -/
theorem goldbachG11_largePrimeDivisors_card_le_twenty_one {N : ℕ} (hN : 4 ≤ N) :
    (largePrimeDivisors N ((N : ℝ) ^ (4 / 53 : ℝ))).card ≤ 21 := by
  let L := largePrimeDivisors N ((N : ℝ) ^ (4 / 53 : ℝ))
  change L.card ≤ 21
  by_cases hL : L.Nonempty
  · obtain ⟨p, hp⟩ := hL
    obtain ⟨hpp, hpN, _⟩ := Nat.mem_primeFactors.mp (mem_filter.mp hp).1
    have hN0 : 0 < N := by omega
    have hd0 : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hN0 hpN) hpp.pos
    have hdN : N / p < N := Nat.div_lt_self hN0 hpp.one_lt
    have hsub : L.erase p ⊆
        largePrimeDivisors (N / p) ((N : ℝ) ^ (4 / 53 : ℝ)) := by
      intro q hq
      obtain ⟨hqp, hqL⟩ := mem_erase.mp hq
      obtain ⟨hqf, hzq⟩ := mem_filter.mp hqL
      obtain ⟨hqq, hqN, _⟩ := Nat.mem_primeFactors.mp hqf
      have hqd : q ∣ N / p := by
        have hmul : q ∣ p * (N / p) := by rwa [Nat.mul_div_cancel' hpN]
        exact (hqq.dvd_mul.mp hmul).resolve_left
          (fun hqp' => hqp ((Nat.dvd_prime hpp).mp hqp' |>.resolve_left hqq.ne_one))
      exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hqq, hqd, hd0.ne'⟩, hzq⟩
    have hc := (card_le_card hsub).trans
      (largePrimeDivisors_card_le_twenty hd0 hdN
        (by norm_num : (1 : ℝ) / 21 < 4 / 53))
    have he := card_erase_add_one hp
    omega
  · have he : L = ∅ := not_nonempty_iff_eq_empty.mp hL
    simp [he]

/-- Coordinate permutation retains every body label and its positive rough cofactor. -/
theorem goldbachG11MainMass_good_pair_mem {N r : ℕ} {ε : ℝ}
    {u : GoldbachG11SwitchedBody}
    (hu : u ∈ goldbachG11GoodSwitchedBodies N
      ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)))
    (hm : goldbachG11SwitchedBodyProd u ∈ goldbachG11EffectiveProductSupport N ε)
    (hr : r ∈ goldbachG11LinkedPrimeWindow N ε (goldbachG11SwitchedBodyProd u))
    (hrN : ¬r ∣ N) :
    (⟨u.1, u.2.1, r, u.2.2.1⟩ : GoldbachG11Label) ∈
        goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) ∧
      u.2.2.2 ∈ roughNumbers
        ((N : ℝ) / goldbachG11LabelProd ⟨u.1, u.2.1, r, u.2.2.1⟩) u.2.2.1 := by
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1
  obtain ⟨hrp, hzr, hrq, hprod⟩ := goldbachG11MainMass_window_data hm hr
  rw [goldbachG11SwitchedBodyProd_minFac huB] at hrq
  rcases u with ⟨t, s, q, k⟩
  obtain ⟨hq, hs, ht, hcop, _, hqs, hst, htb, hk, _, hrough, _⟩ :=
    mem_goldbachG11SwitchedBodies_iff.mp huB
  have hv : (⟨t, s, r, q⟩ : GoldbachG11Label) ∈
      goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) :=
    mem_goldbachG11Labels_iff.mpr
      ⟨hrp, hq, hs, ht, by
        simpa only [Nat.mul_assoc] using (hrp.coprime_iff_not_dvd.mpr hrN).mul_left hcop,
        hzr, hrq, hqs, hst, htb⟩
  have hPk : goldbachG11LabelProd ⟨t, s, r, q⟩ * k ≤ N := by
    simpa only [goldbachG11LabelProd, goldbachG11SwitchedBodyProd, Nat.mul_assoc] using hprod
  refine ⟨hv, mem_roughNumbers.mpr ⟨hk, ?_,
    (goldbachG11_rough_iff_survives _ _).mpr hrough⟩⟩
  apply (le_div_iff₀ (show (0 : ℝ) < goldbachG11LabelProd ⟨t, s, r, q⟩ by
    exact_mod_cast goldbachG11LabelProd_pos hv)).mpr
  exact_mod_cast (by simpa only [Nat.mul_comm] using hPk)

private def activeGoodWindow (N : ℕ) (ε : ℝ) (m : ℕ) : Finset ℕ :=
  if m ∈ goldbachG11EffectiveProductSupport N ε then
    (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => ¬r ∣ N) else ∅

theorem goldbachG11MainMassGood_le_fullRough (N : ℕ) (ε : ℝ) :
    400 * goldbachG11MainMassGood N ε ≤ goldbachG11FullRoughMass N := by
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  let b : ℝ := (N : ℝ) ^ (4 / 33 : ℝ)
  let W := activeGoodWindow N ε
  have hgroup :
      (∑ u ∈ goldbachG11GoodSwitchedBodies N z b,
        ((W (goldbachG11SwitchedBodyProd u)).card : ℝ)) =
      ∑ m ∈ goldbachG11ProductSupport N z b,
        (goldbachG11ProductCoefficient N z b m : ℝ) * (W m).card := by
    exact_mod_cast goldbachG11GoodSwitchedBodies_sum_product N z b
      (fun m => ((W m).card : ℤ))
  have hmass : 400 * goldbachG11MainMassGood N ε =
      ∑ m ∈ goldbachG11ProductSupport N z b,
        (goldbachG11ProductCoefficient N z b m : ℝ) * (W m).card := by
    unfold goldbachG11MainMassGood
    rw [mul_sum]
    calc
      _ = ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
          (goldbachG11ProductCoefficient N z b m : ℝ) * (W m).card := by
        apply sum_congr rfl
        intro m hm
        simp only [W, activeGoodWindow, if_pos hm,
          goldbachG11EffectiveProductCoefficient, ← mul_assoc,
          goldbachG11NormalizedProductCoefficient_mul_four_hundred, z, b]
      _ = _ := sum_subset (filter_subset _ _) (by
        intro m _ hm
        simp only [W, activeGoodWindow, if_neg hm, card_empty, Nat.cast_zero, mul_zero])
  let S := (goldbachG11GoodSwitchedBodies N z b).sigma
    (fun u => W (goldbachG11SwitchedBodyProd u))
  let T := (goldbachG11Labels N z b).sigma
    (fun v => roughNumbers ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2)
  let f : (Σ _u : GoldbachG11SwitchedBody, ℕ) → (Σ _v : GoldbachG11Label, ℕ) :=
    fun a => ⟨⟨a.1.1, a.1.2.1, a.2, a.1.2.2.1⟩, a.1.2.2.2⟩
  have hmap : ∀ a ∈ S, f a ∈ T := by
    rintro ⟨u, r⟩ ha
    obtain ⟨hu, hr⟩ := mem_sigma.mp ha
    have hm : goldbachG11SwitchedBodyProd u ∈ goldbachG11EffectiveProductSupport N ε := by
      by_contra hn
      simp only [W, activeGoodWindow, if_neg hn, notMem_empty] at hr
    have hr' : r ∈ (goldbachG11LinkedPrimeWindow N ε
        (goldbachG11SwitchedBodyProd u)).filter (fun r => ¬r ∣ N) := by
      simpa only [W, activeGoodWindow, if_pos hm] using hr
    exact mem_sigma.mpr
      (goldbachG11MainMass_good_pair_mem hu hm (mem_filter.mp hr').1 (mem_filter.mp hr').2)
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
      ∑ u ∈ goldbachG11GoodSwitchedBodies N z b,
        ((W (goldbachG11SwitchedBodyProd u)).card : ℝ) := by
    simp only [S, card_sigma, Nat.cast_sum]
  have hT : (T.card : ℝ) = goldbachG11FullRoughMass N := by
    simp only [T, card_sigma, Nat.cast_sum, goldbachG11FullRoughMass, roughCount, z, b]
  rw [← hS, ← hT]
  exact_mod_cast hc

theorem goldbachG11MainMassBad_le {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) :
    goldbachG11MainMassBad N ε ≤ 21 * N / (N : ℝ) ^ (4 / 53 : ℝ) := by
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  let L := largePrimeDivisors N z
  let E := goldbachG11EffectiveProductSupport N ε
  let W := goldbachG11LinkedPrimeWindow N ε
  have hN0 : N ≠ 0 := by omega
  have hz : 0 < z := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hsub (m : ℕ) (hm : m ∈ E) : (W m).filter (fun r => r ∣ N) ⊆ L := by
    intro r hr
    obtain ⟨hrW, hrN⟩ := mem_filter.mp hr
    obtain ⟨hrp, hzr, _⟩ := goldbachG11MainMass_window_data hm hrW
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
      have hm0 := (goldbachG11ProductSupport_data (mem_filter.mp hmE).1).1
      have hprod := goldbachG11LinkedPrimeWindow_product_le hmE hrW
      exact mem_Icc.mpr ⟨hm0, (Nat.le_div_iff_mul_le hrp.pos).mpr
        (by simpa only [Nat.mul_comm] using hprod)⟩
    have hc : (E.filter (fun m => r ∈ W m)).card ≤ N / r := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hmsub
    exact (Nat.cast_le.mpr hc).trans Nat.cast_div_le
  calc
    goldbachG11MainMassBad N ε ≤
        ∑ m ∈ E, (((W m).filter (fun r => r ∣ N)).card : ℝ) := by
      apply sum_le_sum
      intro m _
      exact mul_le_of_le_one_left (Nat.cast_nonneg _)
        (goldbachG11EffectiveProductCoefficient_bounds N m ε).2
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
theorem goldbachG11PrimeWindowMainMass_le_fullRough {N : ℕ}
    (hN : 4 ≤ N) (ε : ℝ) :
    400 * goldbachG11PrimeWindowMainMass N ε ≤
      goldbachG11FullRoughMass N + 8400 * N / (N : ℝ) ^ (4 / 53 : ℝ) := by
  rw [goldbachG11PrimeWindowMainMass_eq_good_add_bad, mul_add]
  apply add_le_add (goldbachG11MainMassGood_le_fullRough N ε)
  calc
    400 * goldbachG11MainMassBad N ε ≤
        400 * (21 * N / (N : ℝ) ^ (4 / 53 : ℝ)) :=
      mul_le_mul_of_nonneg_left (goldbachG11MainMassBad_le hN ε) (by norm_num)
    _ = 8400 * N / (N : ℝ) ^ (4 / 53 : ℝ) := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig