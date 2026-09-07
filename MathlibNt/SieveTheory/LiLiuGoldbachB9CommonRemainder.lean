import MathlibNt.SieveTheory.LiLiuGoldbachB9PanDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachB10FibreSieve

open scoped BigOperators
open Finset Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB9CommonRemainder (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The common mass is the genuine full Li prefix, not the old B10 endpoint difference. -/
noncomputable def goldbachB9PlusCommonRemainder (N d : ℕ) : ℝ :=
  (goldbachB9PlusDivCount N d : ℝ) - goldbachB9PlusMainMass N / d.totient

noncomputable def goldbachB9PlusDeletedMain (N d : ℕ) : ℝ :=
  ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) with ¬Nat.Coprime m d, goldbachB9PlusLiWeight N m

theorem goldbachB9PlusMainMass_eq_gated_add_deleted (N d : ℕ) :
    goldbachB9PlusMainMass N =
      goldbachB9PlusGatedMainMass N d + goldbachB9PlusDeletedMain N d := by
  unfold goldbachB9PlusMainMass goldbachB9PlusGatedMainMass goldbachB9PlusDeletedMain
  rw [← sum_filter]
  exact (sum_filter_add_sum_filter_not _ _ _).symm

/-- The deleted main term has a negative sign and is not discarded. -/
theorem goldbachB9PlusCommonRemainder_eq_gated_sub_deleted (N d : ℕ) :
    goldbachB9PlusCommonRemainder N d =
      goldbachB9PlusGatedRemainder N d - goldbachB9PlusDeletedMain N d / d.totient := by
  unfold goldbachB9PlusCommonRemainder goldbachB9PlusGatedRemainder
  rw [goldbachB9PlusMainMass_eq_gated_add_deleted N d]
  ring

theorem goldbachB9PlusDeletedMain_one (N : ℕ) :
    goldbachB9PlusDeletedMain N 1 = 0 := by
  simp [goldbachB9PlusDeletedMain]

theorem goldbachB9PlusCommonRemainder_one (N : ℕ) :
    goldbachB9PlusCommonRemainder N 1 = goldbachB9PlusGatedRemainder N 1 := by
  rw [goldbachB9PlusCommonRemainder_eq_gated_sub_deleted, goldbachB9PlusDeletedMain_one]
  simp

theorem goldbachB9PlusDeletedMain_div_abs_eq_gateLoss (N d : ℕ) :
    |goldbachB9PlusDeletedMain N d / d.totient| =
      gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        (goldbachB9PlusLiWeight N) d := by
  simp only [goldbachB9PlusDeletedMain, gateLoss, div_eq_mul_inv, mul_comm]

theorem abs_goldbachB9PlusCommonRemainder_le (N d : ℕ) :
    |goldbachB9PlusCommonRemainder N d| ≤ |goldbachB9PlusGatedRemainder N d| +
      gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        (goldbachB9PlusLiWeight N) d := by
  rw [goldbachB9PlusCommonRemainder_eq_gated_sub_deleted,
    ← goldbachB9PlusDeletedMain_div_abs_eq_gateLoss]
  exact abs_sub _ _

/-- B and the threshold precede N; the gate budget is consumed only after proving D <= N. -/
theorem goldbachB9PlusCommonRemainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
          |goldbachB9PlusCommonRemainder N d| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, Np, hNp, hp⟩ := goldbachB9PlusGatedRemainder_log_saving U hU
  obtain ⟨Ng, _hNg, hg⟩ := goldbachB9PlusLiWeight_sum_gateLoss_log_saving_one U
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp (eventually_pan_conductor_bounds B hB)
  refine ⟨C + 1, by linarith, B, hB, max Np (max Ng Nc),
    hNp.trans (le_max_left _ _), ?_⟩
  intro N hN
  have hNp' : Np ≤ N := (le_max_left _ _).trans hN
  have hNg' : Ng ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNc' : Nc ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨_, _, _, _, hDN⟩ := hc N hNc'
  let D := panModulusCutoff N B
  let T := (Icc 1 D).filter (fun d => Nat.Coprime d N)
  have hgate :
      ∑ d ∈ T, gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        (goldbachB9PlusLiWeight N) d ≤ (N : ℝ) / Real.log (N : ℝ) ^ U := by
    calc
      _ ≤ ∑ d ∈ Icc 1 D,
          gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
            (goldbachB9PlusLiWeight N) d :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
      _ ≤ _ := hg N hNg' D hDN
  calc
    _ ≤ ∑ d ∈ T, (|goldbachB9PlusGatedRemainder N d| +
        gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
          (goldbachB9PlusLiWeight N) d) :=
      sum_le_sum (fun d _ => abs_goldbachB9PlusCommonRemainder_le N d)
    _ = (∑ d ∈ T, |goldbachB9PlusGatedRemainder N d|) +
        ∑ d ∈ T, gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
          (goldbachB9PlusLiWeight N) d := sum_add_distrib
    _ ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U + (N : ℝ) / Real.log (N : ℝ) ^ U :=
      add_le_add (hp N hNp') hgate
    _ = _ := by ring

/-- Only the production squarefree sieve-divisor identification of nu is used.
There is no restriction comparing Z with either prime factor of m. -/
theorem goldbachB9PlusBoundingSieve_rem_eq_commonRemainder
    {N d : ℕ} (hEven : Even N) {Z : ℝ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)).rem d =
        goldbachB9PlusCommonRemainder N d := by
  exact goldbachB10BoundingSieve_rem_eq_card_sub hEven hd

theorem goldbachB9PlusBoundingSieve_remainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N, ∀ Z : ℝ,
        ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter
          (fun d => d ∣ goldbachB10ProdPrimes N Z),
          |(goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
            ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)).rem d| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, N₀, hN₀, hr⟩ := goldbachB9PlusCommonRemainder_log_saving U hU
  refine ⟨C, hC, B, hB, N₀, hN₀, ?_⟩
  intro N hN hEven Z
  calc
    _ = ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter
        (fun d => d ∣ goldbachB10ProdPrimes N Z), |goldbachB9PlusCommonRemainder N d| := by
      apply sum_congr rfl
      intro d hd
      rw [goldbachB9PlusBoundingSieve_rem_eq_commonRemainder hEven (mem_filter.mp hd).2]
    _ ≤ ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
        |goldbachB9PlusCommonRemainder N d| := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        obtain ⟨hdI, hdP⟩ := mem_filter.mp hd
        exact mem_filter.mpr ⟨hdI, goldbachB10_dvd_prodPrimes_coprime_N hdP⟩
      · exact fun _ _ _ => abs_nonneg _
    _ ≤ _ := hr N hN

/-- Inclusion of the actual strict-level divisor support, still including d = 1. -/
theorem goldbachB9PlusBoundingSieve_levelSupport_subset
    (N : ℕ) (Z Δ : ℝ) (Q : ℕ) (hQ : Nat.floor Δ ≤ Q) :
    (goldbachB10ProdPrimes N Z).divisors.filter (fun d => d < Nat.floor Δ + 1) ⊆
      (Icc 1 Q).filter (fun d => d ∣ goldbachB10ProdPrimes N Z) := by
  intro d hd
  obtain ⟨hdiv, hlt⟩ := mem_filter.mp hd
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdiv, by omega⟩,
    (Nat.mem_divisors.mp hdiv).1⟩

theorem goldbachB9PlusBoundingSieve_levelRemainderSum_le
    (N : ℕ) (hEven : Even N) (Z Δ : ℝ) (Q : ℕ) (hQ : Nat.floor Δ ≤ Q) :
    let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)
    ∑ d ∈ S.prodPrimes.divisors.filter (fun d => d < Nat.floor Δ + 1), |S.rem d| ≤
      ∑ d ∈ (Icc 1 Q).filter (fun d => d ∣ goldbachB10ProdPrimes N Z), |S.rem d| := by
  exact sum_le_sum_of_subset_of_nonneg
    (goldbachB9PlusBoundingSieve_levelSupport_subset N Z Δ Q hQ) (fun _ _ _ => abs_nonneg _)

/-- Ready for the next sieve consumer; no Rosser main term or density estimate is asserted. -/
theorem goldbachB9PlusBoundingSieve_levelRemainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N, ∀ Z Δ : ℝ,
        Nat.floor Δ ≤ panModulusCutoff N B →
        let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)
        ∑ d ∈ S.prodPrimes.divisors.filter (fun d => d < Nat.floor Δ + 1), |S.rem d| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, N₀, hN₀, hr⟩ :=
    goldbachB9PlusBoundingSieve_remainder_log_saving U hU
  refine ⟨C, hC, B, hB, N₀, hN₀, ?_⟩
  intro N hN hEven Z Δ hΔ
  exact (goldbachB9PlusBoundingSieve_levelRemainderSum_le N hEven Z Δ
    (panModulusCutoff N B) hΔ).trans (hr N hN hEven Z)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig