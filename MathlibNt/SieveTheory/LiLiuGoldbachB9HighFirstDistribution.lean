import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstMainMass
import MathlibNt.SieveTheory.LiLiuGoldbachB9PaidUpper

open scoped BigOperators
open Finset Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachB9HighFirstDivCount (N d : ℕ) : ℕ :=
  (goldbachB10DivisorAtoms N d 0 ((N : ℝ) ^ (1 / 10 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ))).card

noncomputable def goldbachX9HighGated (N d : ℕ) : ℝ := by
  classical
  exact ∑ m ∈ goldbachB9HighFirstSupport N,
    if Nat.Coprime m d then goldbachB9PlusLiWeight N m else 0

noncomputable def goldbachX9HighDeleted (N d : ℕ) : ℝ := by
  classical
  exact ∑ m ∈ goldbachB9HighFirstSupport N with ¬Nat.Coprime m d,
    goldbachB9PlusLiWeight N m

noncomputable def goldbachB9HighFirstGatedRemainder (N d : ℕ) : ℝ :=
  (goldbachB9HighFirstDivCount N d : ℝ) - goldbachX9HighGated N d / d.totient

noncomputable def goldbachB9HighFirstCommonRemainder (N d : ℕ) : ℝ :=
  (goldbachB9HighFirstDivCount N d : ℝ) - goldbachX9High N / d.totient

theorem goldbachX9High_eq_gated_add_deleted (N d : ℕ) :
    goldbachX9High N = goldbachX9HighGated N d + goldbachX9HighDeleted N d := by
  classical
  unfold goldbachX9High goldbachX9HighGated goldbachX9HighDeleted
  rw [← sum_filter]
  exact (sum_filter_add_sum_filter_not _ _ _).symm

theorem goldbachB9HighFirstCommonRemainder_eq (N d : ℕ) :
    goldbachB9HighFirstCommonRemainder N d =
      goldbachB9HighFirstGatedRemainder N d - goldbachX9HighDeleted N d / d.totient := by
  unfold goldbachB9HighFirstCommonRemainder goldbachB9HighFirstGatedRemainder
  rw [goldbachX9High_eq_gated_add_deleted N d]
  ring

theorem goldbachB9HighFirstCommonRemainder_one (N : ℕ) :
    goldbachX9HighDeleted N 1 = 0 ∧
      goldbachB9HighFirstCommonRemainder N 1 = goldbachB9HighFirstGatedRemainder N 1 := by
  have hz : goldbachX9HighDeleted N 1 = 0 := by simp [goldbachX9HighDeleted]
  exact ⟨hz, by rw [goldbachB9HighFirstCommonRemainder_eq, hz]; simp⟩

theorem goldbachB9HighFirstSupport_eventually_panInterval (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, goldbachB9HighFirstSupport N ⊆
      Ioc (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) := by
  filter_upwards [goldbachB9ProductSupport_eventually_panInterval B,
    eventually_ge_atTop (2 : ℕ)] with N hs hN
  exact (goldbachB9HighFirstSupport_subset N hN).trans hs

/-- Generic inverse residue geometry and the strict/closed prime prefix are reused pointwise. -/
theorem goldbachB9HighFirstDivCount_eq_product_sum {N d : ℕ}
    (hN : 2 ≤ N) (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    (goldbachB9HighFirstDivCount N d : ℝ) =
      ∑ m ∈ goldbachB9HighFirstSupport N,
        if Nat.Coprime m d then (primesInAPBelow N m d (N % d) : ℝ) else 0 := by
  classical
  rw [goldbachB9HighFirstDivCount,
    goldbachB10DivisorAtoms_card_eq_sum_productSupport _ _ _ hd hdN, Nat.cast_sum]
  apply sum_congr rfl
  intro m hm
  rw [goldbachC10Coeff_eq_one_of_mem_productSupport hm, one_mul]
  by_cases hc : Nat.Coprime m d
  · rw [if_pos hc, if_pos hc, goldbachB9PlusProductResidueQFiber_card_eq_prefix
      (goldbachB9HighFirstSupport_subset N hN hm) hc]
  · simp only [if_neg hc, Nat.cast_zero]

private theorem highFirst_coeff_sum {N A₁ A₂ : ℕ} (f : ℕ → ℝ)
    (hs : goldbachB9HighFirstSupport N ⊆ Ioc A₁ A₂) :
    (∑ m ∈ Ioc A₁ A₂,
      goldbachC10CoeffReal N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) m * f m) =
      ∑ m ∈ goldbachB9HighFirstSupport N, f m := by
  classical
  calc
    _ = ∑ m ∈ goldbachB9HighFirstSupport N,
        goldbachC10CoeffReal N ((N : ℝ) ^ (1 / 10 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) m * f m := by
      symm
      apply sum_subset hs
      intro m _ hm
      have hz : goldbachC10CoeffReal N ((N : ℝ) ^ (1 / 10 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) m = 0 :=
        not_not.mp (fun h => hm (goldbachC10CoeffReal_ne_zero_iff.mp h))
      rw [hz, zero_mul]
    _ = _ := sum_congr rfl (fun _ hm => by
      rw [goldbachC10CoeffReal_eq_one_of_mem_productSupport hm, one_mul])

/-- The entire high m-sum equals PanError before any absolute value is taken. -/
theorem goldbachB9HighFirstGatedRemainder_eq_panError {N A₁ A₂ d : ℕ}
    (hN : 2 ≤ N) (hd : 1 ≤ d) (hdN : Nat.Coprime d N)
    (hs : goldbachB9HighFirstSupport N ⊆ Ioc A₁ A₂) :
    goldbachB9HighFirstGatedRemainder N d =
      liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d (N % d)
        (goldbachC10CoeffReal N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) := by
  classical
  unfold liuMainPanCoprimeIntervalSum
  have heq := highFirst_coeff_sum (fun m => if Nat.Coprime m d then
    liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N m d (N % d) else 0) hs
  simp only [mul_ite, mul_zero] at heq
  rw [heq, goldbachB9HighFirstGatedRemainder,
    goldbachB9HighFirstDivCount_eq_product_sum hN hd hdN, goldbachX9HighGated,
    sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  by_cases hc : Nat.Coprime m d
  · simp only [if_pos hc, liuScaledAPError, goldbachB9PlusLiWeight]
  · simp only [if_neg hc, zero_div, sub_self]

private theorem highFirst_abs_le_maxL {N A₁ A₂ d : ℕ}
    (hN : 2 ≤ N) (hd : 1 ≤ d) (hdN : Nat.Coprime d N)
    (hs : goldbachB9HighFirstSupport N ⊆ Ioc A₁ A₂) :
    |goldbachB9HighFirstGatedRemainder N d| ≤
      liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d
        (goldbachC10CoeffReal N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) := by
  classical
  rw [goldbachB9HighFirstGatedRemainder_eq_panError hN hd hdN hs]
  have hl : N % d ∈ unitResidues d :=
    mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt N (by omega)),
      (ZMod.coprime_mod_iff_coprime N d).mpr hdN.symm⟩
  have hS : (unitResidues d).Nonempty := ⟨N % d, hl⟩
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  rw [dif_pos hS]
  exact le_max' ((unitResidues d).image (fun l =>
    |liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
      N A₁ A₂ d l
      (goldbachC10CoeffReal N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))|))
    _ (mem_image.mpr ⟨N % d, hl, rfl⟩)

/-- Bounded Pan is called again with the actual high coefficient, bounded by one. -/
theorem goldbachB9HighFirstGatedRemainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
          |goldbachB9HighFirstGatedRemainder N d| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  classical
  obtain ⟨C, hC, B, hB, Na, ha⟩ :=
    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving U hU
  obtain ⟨Ns, hs⟩ := eventually_atTop.mp (goldbachB9HighFirstSupport_eventually_panInterval B)
  refine ⟨C, hC, B, hB, max 4 (max Na Ns), le_max_left _ _, ?_⟩
  intro N hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNs : Ns ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let A₁ := liuPanSourceIntervalLower N B
  let A₂ := liuPanSourceIntervalUpper N
  let f := goldbachC10CoeffReal N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
  let F := fun d => liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
    N A₁ A₂ d f
  calc
    _ ≤ ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N), F d := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hdI, hdc⟩ := mem_filter.mp hd
      exact highFirst_abs_le_maxL (by omega) (mem_Icc.mp hdI).1 hdc (hs N hNs)
    _ ≤ ∑ d ∈ Icc 1 (panModulusCutoff N B), F d :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => liuMainPanCoprimeIntervalMaxL_nonneg _ _ _ _ _ _)
    _ ≤ _ := ha N hNa A₁ A₂ f
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (le_of_lt (log_rpow_lt_liuPanSourceIntervalLower N B))
      (abs_goldbachC10CoeffReal_le_one N _ _)

theorem abs_goldbachB9HighFirstCommonRemainder_le (N d : ℕ) :
    |goldbachB9HighFirstCommonRemainder N d| ≤ |goldbachB9HighFirstGatedRemainder N d| +
      gateLoss N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        (goldbachB9PlusLiWeight N) d := by
  have heq : |goldbachX9HighDeleted N d / d.totient| =
      gateLoss N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        (goldbachB9PlusLiWeight N) d := by
    simp only [goldbachX9HighDeleted, goldbachB9HighFirstSupport, gateLoss,
      div_eq_mul_inv, mul_comm]
  rw [goldbachB9HighFirstCommonRemainder_eq, ← heq]
  exact abs_sub _ _

theorem goldbachB9HighFirstCommonRemainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
          |goldbachB9HighFirstCommonRemainder N d| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  classical
  obtain ⟨C, hC, B, hB, Np, hNp, hp⟩ := goldbachB9HighFirstGatedRemainder_log_saving U hU
  obtain ⟨Ng, _hNg, hg⟩ := goldbachB9HighFirst_gate_log_saving U
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp (eventually_pan_conductor_bounds B hB)
  refine ⟨C + 1, by linarith, B, hB, max Np (max Ng Nc),
    hNp.trans (le_max_left _ _), ?_⟩
  intro N hN
  have hpN : Np ≤ N := (le_max_left _ _).trans hN
  have hgN : Ng ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hcN : Nc ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨_, _, _, _, hDN⟩ := hc N hcN
  let T := (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N)
  have hgate : ∑ d ∈ T, gateLoss N ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) (goldbachB9PlusLiWeight N) d ≤
        (N : ℝ) / Real.log (N : ℝ) ^ U :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)).trans
      (hg N hgN _ hDN)
  calc
    _ ≤ ∑ d ∈ T, (|goldbachB9HighFirstGatedRemainder N d| +
        gateLoss N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
          (goldbachB9PlusLiWeight N) d) :=
      sum_le_sum (fun d _ => abs_goldbachB9HighFirstCommonRemainder_le N d)
    _ = (∑ d ∈ T, |goldbachB9HighFirstGatedRemainder N d|) +
        ∑ d ∈ T, gateLoss N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
          (goldbachB9PlusLiWeight N) d := sum_add_distrib
    _ ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U + (N : ℝ) / Real.log (N : ℝ) ^ U :=
      add_le_add (hp N hpN) hgate
    _ = _ := by ring

theorem goldbachB9HighFirstBoundingSieve_rem_eq {N d : ℕ}
    (hEven : Even N) {Z : ℝ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachX9High N)).rem d =
        goldbachB9HighFirstCommonRemainder N d :=
  goldbachB10BoundingSieve_rem_eq_card_sub hEven hd

/-- The actual strict Rosser support and |lambda| <= 1, with d=1 retained. -/
theorem goldbachB9HighFirst_upperErrSum_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N, ∀ Z : ℝ,
        let Δ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1)
        let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (1 / 10 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachX9High N)
        LinearSieve.upperErrSum S (Nat.floor Δ + 1)
          (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  classical
  obtain ⟨C, hC, B, hB, Nr, hNr, hr⟩ := goldbachB9HighFirstCommonRemainder_log_saving U hU
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨C, hC, B, hB, max Nr Nl, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z
  have hrN : Nr ≤ N := (le_max_left _ _).trans hN
  have hlN : Nl ≤ N := (le_max_right _ _).trans hN
  let Δ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1)
  let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (1 / 10 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachX9High N)
  have hsub : S.prodPrimes.divisors.filter (fun d => d < Nat.floor Δ + 1) ⊆
      (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N) := by
    intro d hd
    have hh := goldbachB9PlusBoundingSieve_levelSupport_subset N Z Δ _
      (goldbachB8Plus_floor_paidLevel_le_panModulusCutoff N B (hl N hlN)) hd
    exact mem_filter.mpr ⟨(mem_filter.mp hh).1,
      goldbachB10_dvd_prodPrimes_coprime_N (mem_filter.mp hh).2⟩
  change LinearSieve.upperErrSum S (Nat.floor Δ + 1)
    (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤ _
  unfold LinearSieve.upperErrSum
  calc
    _ ≤ ∑ d ∈ S.prodPrimes.divisors.filter (fun d => d < Nat.floor Δ + 1),
        |goldbachB9HighFirstCommonRemainder N d| := by
      apply sum_le_sum
      intro d hd
      have heq := goldbachB9HighFirstBoundingSieve_rem_eq hEven
        (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      exact ((mul_le_mul_of_nonneg_right
        (LinearSieve.abs_upperRosserWeight_le_one _ _ d) (abs_nonneg _)).trans_eq
          (one_mul _)).trans_eq (congrArg abs heq)
    _ ≤ ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
        |goldbachB9HighFirstCommonRemainder N d| :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ ≤ _ := hr N hrN

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig