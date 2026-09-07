import MathlibNt.SieveTheory.LiLiuGoldbachG11SwitchedMother
import MathlibNt.SieveTheory.LiLiuGoldbachWeightG11RoughConsumed

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11SwitchedBodyOf (v : GoldbachG11Label) (k : ℕ) :
    GoldbachG11SwitchedBody :=
  ⟨v.1, v.2.1, v.2.2.2, k⟩

theorem goldbachG11_switch_product (v : GoldbachG11Label) (k : ℕ) :
    v.2.2.1 * goldbachG11SwitchedBodyProd (goldbachG11SwitchedBodyOf v k) =
      goldbachG11LabelProd v * k := by
  dsimp [goldbachG11SwitchedBodyProd, goldbachG11SwitchedBodyOf, goldbachG11LabelProd]
  ring

theorem goldbachG11_switch_cutoff_iff {N p n : ℕ} (eps : ℝ) (heq : p + n = N) :
    (p : ℝ) < (1 - eps) * N ↔ eps * N < (n : ℝ) := by
  have heqR : (p : ℝ) + n = N := by exact_mod_cast heq
  constructor <;> intro h <;> nlinarith only [heqR, h]

theorem goldbachG11RoughPair_to_switched {N p k : ℕ} {eps z b : ℝ}
    {v : GoldbachG11Label} (hv : v ∈ goldbachG11Labels N z b)
    (hpk : (p, k) ∈ goldbachG11RoughPairs N eps v) :
    goldbachG11SwitchedBodyOf v k ∈ goldbachG11SwitchedBodies N z b ∧
      v.2.2.1 ∈ goldbachG11FirstPrimeFiber N eps z (goldbachG11SwitchedBodyOf v k) ∧
        p = N - v.2.2.1 * goldbachG11SwitchedBodyProd (goldbachG11SwitchedBodyOf v k) := by
  rcases v with ⟨t, s, r, q⟩
  obtain ⟨hr, hq, hs, ht, hcop, hzr, hrq, hqs, hst, htb⟩ :=
    mem_goldbachG11Labels_iff.mp hv
  obtain ⟨_, hk1, hkN, hp, hcut, heq, hrough⟩ := mem_goldbachG11RoughPairs_iff.mp hpk
  have heq' : p + r * (q * s * t * k) = N := by
    rw [← goldbachG11_switch_product] at heq
    exact heq
  have hnN : r * (q * s * t * k) < N := by
    have hp0 := hp.pos
    omega
  have hBN : q * s * t * k < N := by
    have hr2 := hr.two_le
    have : q * s * t * k ≤ r * (q * s * t * k) := by nlinarith
    exact this.trans_lt hnN
  have hc : Nat.Coprime r N ∧ Nat.Coprime (q * s * t) N := by
    rw [← Nat.coprime_mul_iff_left]
    simpa only [Nat.mul_assoc] using hcop
  have hpEq : p = N - r * (q * s * t * k) := by omega
  refine ⟨mem_goldbachG11SwitchedBodies_iff.mpr
    ⟨hq, hs, ht, hc.2, hzr.trans (by exact_mod_cast hrq), hqs, hst, htb,
      hk1, hkN, (goldbachG11_survives_one_iff q k).mpr hrough, hBN⟩, ?_, hpEq⟩
  exact mem_goldbachG11FirstPrimeFiber_iff.mpr
    ⟨hr, hr.coprime_iff_not_dvd.mp hc.1, hzr, hrq,
      (goldbachG11_switch_cutoff_iff eps heq').mp hcut, hnN, hpEq ▸ hp⟩

theorem goldbachG11Switched_to_roughPair {N r : ℕ} {eps z b : ℝ}
    {u : GoldbachG11SwitchedBody} (hu : u ∈ goldbachG11SwitchedBodies N z b)
    (hr : r ∈ goldbachG11FirstPrimeFiber N eps z u) :
    (⟨u.1, u.2.1, r, u.2.2.1⟩ : GoldbachG11Label) ∈ goldbachG11Labels N z b ∧
      (N - r * goldbachG11SwitchedBodyProd u, u.2.2.2) ∈
        goldbachG11RoughPairs N eps ⟨u.1, u.2.1, r, u.2.2.1⟩ := by
  rcases u with ⟨t, s, q, k⟩
  obtain ⟨hq, hs, ht, hcop, _, hqs, hst, htb, hk1, hkN, hrough, _⟩ :=
    mem_goldbachG11SwitchedBodies_iff.mp hu
  obtain ⟨hrp, hrN, hzr, hrq, hcut, hnN, hp⟩ :=
    mem_goldbachG11FirstPrimeFiber_iff.mp hr
  have heq : N - r * (q * s * t * k) + r * (q * s * t * k) = N :=
    Nat.sub_add_cancel hnN.le
  refine ⟨mem_goldbachG11Labels_iff.mpr
    ⟨hrp, hq, hs, ht, ?_, hzr, hrq, hqs, hst, htb⟩,
    mem_goldbachG11RoughPairs_iff.mpr ⟨Nat.sub_le _ _, hk1, hkN, hp,
      (goldbachG11_switch_cutoff_iff eps heq).mpr hcut, ?_,
      (goldbachG11_survives_one_iff q k).mp hrough⟩⟩
  · simpa only [Nat.mul_assoc] using (hrp.coprime_iff_not_dvd.mpr hrN).mul_left hcop
  · rw [← goldbachG11_switch_product]
    exact heq

abbrev GoldbachG11RoughAtom := Σ _v : GoldbachG11Label, ℕ × ℕ
abbrev GoldbachG11SwitchedAtom := Σ _u : GoldbachG11SwitchedBody, ℕ

noncomputable def goldbachG11RoughFamily (N : ℕ) (eps z b : ℝ) :
    Finset GoldbachG11RoughAtom :=
  (goldbachG11Labels N z b).sigma (goldbachG11RoughPairs N eps)

noncomputable def goldbachG11SwitchedFamily (N : ℕ) (eps z b : ℝ) :
    Finset GoldbachG11SwitchedAtom :=
  (goldbachG11SwitchedBodies N z b).sigma (goldbachG11FirstPrimeFiber N eps z)

def goldbachG11SwitchForward (x : GoldbachG11RoughAtom) : GoldbachG11SwitchedAtom :=
  ⟨goldbachG11SwitchedBodyOf x.1 x.2.2, x.1.2.2.1⟩

def goldbachG11SwitchBackward (N : ℕ) (y : GoldbachG11SwitchedAtom) :
    GoldbachG11RoughAtom :=
  ⟨⟨y.1.1, y.1.2.1, y.2, y.1.2.2.1⟩,
    N - y.2 * goldbachG11SwitchedBodyProd y.1, y.1.2.2.2⟩

theorem goldbachG11SwitchForward_mem {N : ℕ} {eps z b : ℝ}
    {x : GoldbachG11RoughAtom} (hx : x ∈ goldbachG11RoughFamily N eps z b) :
    goldbachG11SwitchForward x ∈ goldbachG11SwitchedFamily N eps z b := by
  obtain ⟨hv, hpk⟩ := Finset.mem_sigma.mp hx
  have h := goldbachG11RoughPair_to_switched hv hpk
  exact Finset.mem_sigma.mpr ⟨h.1, h.2.1⟩

theorem goldbachG11SwitchBackward_mem {N : ℕ} {eps z b : ℝ}
    {y : GoldbachG11SwitchedAtom} (hy : y ∈ goldbachG11SwitchedFamily N eps z b) :
    goldbachG11SwitchBackward N y ∈ goldbachG11RoughFamily N eps z b := by
  obtain ⟨hu, hr⟩ := Finset.mem_sigma.mp hy
  exact Finset.mem_sigma.mpr (goldbachG11Switched_to_roughPair hu hr)

theorem goldbachG11SwitchBackward_forward {N : ℕ} {eps z b : ℝ}
    {x : GoldbachG11RoughAtom} (hx : x ∈ goldbachG11RoughFamily N eps z b) :
    goldbachG11SwitchBackward N (goldbachG11SwitchForward x) = x := by
  rcases x with ⟨⟨t, s, r, q⟩, p, k⟩
  obtain ⟨hv, hpk⟩ := Finset.mem_sigma.mp hx
  have hp := (goldbachG11RoughPair_to_switched hv hpk).2.2
  change p = N - r * (q * s * t * k) at hp
  simp only [goldbachG11SwitchBackward, goldbachG11SwitchForward,
    goldbachG11SwitchedBodyOf, goldbachG11SwitchedBodyProd, ← hp]

theorem goldbachG11SwitchForward_backward (N : ℕ) (y : GoldbachG11SwitchedAtom) :
    goldbachG11SwitchForward (goldbachG11SwitchBackward N y) = y := by
  rcases y with ⟨⟨t, s, q, k⟩, r⟩
  rfl

noncomputable def goldbachG11SwitchEquiv (N : ℕ) (eps z b : ℝ) :
    {x // x ∈ goldbachG11RoughFamily N eps z b} ≃
      {y // y ∈ goldbachG11SwitchedFamily N eps z b} where
  toFun x := ⟨goldbachG11SwitchForward x.1, goldbachG11SwitchForward_mem x.2⟩
  invFun y := ⟨goldbachG11SwitchBackward N y.1, goldbachG11SwitchBackward_mem y.2⟩
  left_inv x := Subtype.ext (goldbachG11SwitchBackward_forward x.2)
  right_inv y := Subtype.ext (goldbachG11SwitchForward_backward N y.1)

theorem goldbachG11Switch_card (N : ℕ) (eps z b : ℝ) :
    (goldbachG11RoughFamily N eps z b).card =
      (goldbachG11SwitchedFamily N eps z b).card := by
  classical
  simpa only [Fintype.card_coe] using Fintype.card_congr (goldbachG11SwitchEquiv N eps z b)

theorem goldbachG11Switch_sum (N : ℕ) (eps z b : ℝ)
    (w : GoldbachG11SwitchedBody → ℤ) :
    (∑ v ∈ goldbachG11Labels N z b, ∑ pk ∈ goldbachG11RoughPairs N eps v,
      w (goldbachG11SwitchedBodyOf v pk.2)) =
      ∑ u ∈ goldbachG11SwitchedBodies N z b,
        ∑ _r ∈ goldbachG11FirstPrimeFiber N eps z u, w u := by
  classical
  have h :
      (∑ x ∈ goldbachG11RoughFamily N eps z b, w (goldbachG11SwitchForward x).1) =
        ∑ y ∈ goldbachG11SwitchedFamily N eps z b, w y.1 := by
    apply Finset.sum_bij (fun x _ => goldbachG11SwitchForward x)
    · intro x hx
      exact goldbachG11SwitchForward_mem hx
    · intro x hx y hy hxy
      calc
        x = goldbachG11SwitchBackward N (goldbachG11SwitchForward x) :=
          (goldbachG11SwitchBackward_forward hx).symm
        _ = goldbachG11SwitchBackward N (goldbachG11SwitchForward y) := congrArg _ hxy
        _ = y := goldbachG11SwitchBackward_forward hy
    · intro y hy
      exact ⟨goldbachG11SwitchBackward N y, goldbachG11SwitchBackward_mem hy,
        goldbachG11SwitchForward_backward N y⟩
    · intro x _
      rfl
  simpa only [goldbachG11RoughFamily, goldbachG11SwitchedFamily,
    Finset.sum_sigma', goldbachG11SwitchForward] using h

theorem goldbachG11RoughCount_sum_eq_switchedTotal (N : ℕ) (eps z b : ℝ) :
    (∑ v ∈ goldbachG11Labels N z b, goldbachG11RoughCount N eps v) =
      goldbachG11SwitchedTotal N eps z b := by
  simpa [goldbachG11RoughCount, goldbachG11SwitchedTotal] using
    goldbachG11Switch_sum N eps z b (fun _ => 1)

open Classical in
theorem goldbachG11Switch_filter_count (N : ℕ) (eps z b : ℝ)
    (C : GoldbachG11SwitchedBody → Prop) :
    (∑ v ∈ goldbachG11Labels N z b,
      (((goldbachG11RoughPairs N eps v).filter fun pk =>
        C (goldbachG11SwitchedBodyOf v pk.2)).card : ℤ)) =
      ∑ u ∈ (goldbachG11SwitchedBodies N z b).filter C,
        ((goldbachG11FirstPrimeFiber N eps z u).card : ℤ) := by
  have h := goldbachG11Switch_sum N eps z b (fun u => if C u then 1 else 0)
  simpa [Finset.sum_filter] using h

theorem goldbachG11BadRoughPair_mem_NException {N : ℕ} {eps z b : ℝ}
    {v : GoldbachG11Label} {pk : ℕ × ℕ} (heps : 0 ≤ eps)
    (hv : v ∈ goldbachG11Labels N z b) (hpk : pk ∈ goldbachG11RoughPairs N eps v)
    (hbad : ¬Nat.Coprime (goldbachG11SwitchedBodyProd (goldbachG11SwitchedBodyOf v pk.2)) N) :
    goldbachG11LabelProd v * pk.2 ∈
      goldbachG11NException (goldbachDifferenceCarrier N eps) N v := by
  classical
  obtain ⟨hn, hd, _⟩ := goldbachG11_quotient_backward heps (Finset.mem_filter.mp hpk).1
  have hr := (goldbachG11RoughPair_to_switched hv hpk).2.1
  refine Finset.mem_filter.mpr ⟨hn, hd, ?_⟩
  intro hc
  apply hbad
  apply (goldbachG11FirstPrimeFiber_coprime_iff hr).mp
  rwa [goldbachG11_switch_product]

theorem goldbachG11RoughPair_output_injective (N : ℕ) (eps : ℝ)
    (v : GoldbachG11Label) (hv : 0 < goldbachG11LabelProd v) :
    Set.InjOn (fun pk : ℕ × ℕ => goldbachG11LabelProd v * pk.2)
      (goldbachG11RoughPairs N eps v) := by
  intro a ha b hb hab
  have hk : a.2 = b.2 := by nlinarith
  have hea := (mem_goldbachG11RoughPairs_iff.mp ha).2.2.2.2.2.1
  have heb := (mem_goldbachG11RoughPairs_iff.mp hb).2.2.2.2.2.1
  rw [hk] at hea
  exact Prod.ext (by omega) hk

open Classical in
theorem goldbachG11BadRoughCount_le_NCount {N : ℕ} {eps z b : ℝ}
    (heps : 0 ≤ eps) {v : GoldbachG11Label} (hv : v ∈ goldbachG11Labels N z b) :
    (((goldbachG11RoughPairs N eps v).filter fun pk =>
      ¬Nat.Coprime (goldbachG11SwitchedBodyProd (goldbachG11SwitchedBodyOf v pk.2)) N).card : ℤ) ≤
      goldbachG11NCount (goldbachDifferenceCarrier N eps) N v := by
  have h := Finset.card_le_card_of_injOn (fun pk : ℕ × ℕ => goldbachG11LabelProd v * pk.2)
    (s := (goldbachG11RoughPairs N eps v).filter fun pk =>
      ¬Nat.Coprime (goldbachG11SwitchedBodyProd (goldbachG11SwitchedBodyOf v pk.2)) N)
    (t := goldbachG11NException (goldbachDifferenceCarrier N eps) N v)
    (by
      intro pk hpk
      obtain ⟨hpk, hbad⟩ := Finset.mem_filter.mp hpk
      exact goldbachG11BadRoughPair_mem_NException heps hv hpk hbad)
    (by
      intro a ha b hb hab
      exact goldbachG11RoughPair_output_injective N eps v (goldbachG11LabelProd_pos hv)
        (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab)
  unfold goldbachG11NCount
  exact_mod_cast h

theorem goldbachG11BadSwitchedTotal_le_NCount_sum (N : ℕ) (eps z b : ℝ)
    (heps : 0 ≤ eps) :
    goldbachG11BadSwitchedTotal N eps z b ≤
      ∑ v ∈ goldbachG11Labels N z b,
        goldbachG11NCount (goldbachDifferenceCarrier N eps) N v := by
  classical
  calc
    goldbachG11BadSwitchedTotal N eps z b =
        ∑ v ∈ goldbachG11Labels N z b,
          (((goldbachG11RoughPairs N eps v).filter fun pk =>
            ¬Nat.Coprime (goldbachG11SwitchedBodyProd
              (goldbachG11SwitchedBodyOf v pk.2)) N).card : ℤ) := by
      convert (goldbachG11Switch_filter_count N eps z b
        (fun u => ¬Nat.Coprime (goldbachG11SwitchedBodyProd u) N)).symm using 1
      · unfold goldbachG11BadSwitchedTotal
        apply Finset.sum_congr
        · ext u
          simp
        · intro u _
          rfl
      · apply Finset.sum_congr rfl
        intro v _
        congr 1
        apply congrArg Finset.card
        ext pk
        simp
    _ ≤ _ := Finset.sum_le_sum fun _ hv => goldbachG11BadRoughCount_le_NCount heps hv

theorem goldbachG11SwitchedTotal_le_good_add_NCount (N : ℕ) (eps z b : ℝ)
    (heps : 0 ≤ eps) :
    goldbachG11SwitchedTotal N eps z b ≤ goldbachG11GoodSwitchedTotal N eps z b +
      ∑ v ∈ goldbachG11Labels N z b,
        goldbachG11NCount (goldbachDifferenceCarrier N eps) N v := by
  rw [goldbachG11SwitchedTotal_eq_good_add_bad]
  exact add_le_add le_rfl (goldbachG11BadSwitchedTotal_le_NCount_sum N eps z b heps)

theorem goldbachG11RoughTotal_eq_switchedTotal (N : ℕ) (eps : ℝ) :
    goldbachG11RoughTotal N eps =
      goldbachG11SwitchedTotal N eps ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) :=
  goldbachG11RoughCount_sum_eq_switchedTotal N eps _ _

theorem goldbachG11RoughTotal_good_comparison (N : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    0 ≤ goldbachG11RoughTotal N eps -
        goldbachG11GoodSwitchedTotal N eps ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) ∧
      goldbachG11RoughTotal N eps ≤
        goldbachG11GoodSwitchedTotal N eps ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) +
          ∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
            goldbachG11NCount (goldbachDifferenceCarrier N eps) N v := by
  rw [goldbachG11RoughTotal_eq_switchedTotal]
  exact ⟨goldbachG11SwitchedTotal_sub_good_nonneg N eps _ _,
    goldbachG11SwitchedTotal_le_good_add_NCount N eps _ _ heps⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig