import Wu18938Campaign.M6.EighthEndpoint
import MathlibNt.Wu2008DoubleSieve.SeventhEighthPhysicalSieveEndpoint
import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalQuadrature
import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalMass

noncomputable section
open Finset Filter Real
open Wu2008DoubleSieve Wu2008DoubleSieve.SeventhEighth
open LiLiuPrereqBuchstab
open scoped Classical Interval

namespace Wu18938Campaign.M6

def firstPrimeBandPairs (N : ℕ) (κ : ℝ) : Finset (ℕ × ℕ) :=
  (eighthPairs N).filter fun p =>
    (N : ℝ) ^ (1 / 10 - κ) ≤ p.1 ∧ (p.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)

def firstPrimeBand (N : ℕ) (κ : ℝ) : Finset NinthLabel :=
  (paperSmallEighth N).filter fun x => (N : ℝ) ^ (1 / 10 - κ) ≤ x.1.1

def firstPrimeInterior (N : ℕ) (κ : ℝ) : Finset NinthLabel :=
  (paperSmallEighth N).filter fun x => (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 - κ)

theorem firstPrimeBand_eq_physical (N : ℕ) (κ : ℝ) :
    firstPrimeBand N κ = physical N (firstPrimeBandPairs N κ) := by
  ext x
  simp only [firstPrimeBand, paperSmallEighth, firstPrimeBandPairs,
    physicalT8, physical, mem_filter, mem_sigma]
  tauto

theorem paperSmallEighth_firstPrime_split (N : ℕ) (κ : ℝ) :
    (paperSmallEighth N).card =
      (firstPrimeInterior N κ).card + (firstPrimeBand N κ).card := by
  simpa only [firstPrimeInterior, firstPrimeBand, not_lt] using
    (card_filter_add_card_filter_not (s := paperSmallEighth N)
      (fun x => (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 - κ))).symm

theorem firstPrimeBand_reciprocal {κ : ℝ} (hκ : 0 < κ) (hκu : κ ≤ 1 / 100) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ primesIcc ((N : ℝ) ^ (1 / 10 - κ)) ((N : ℝ) ^ (1 / 10 : ℝ)),
        1 / (p : ℝ)) ≤ 21 * κ := by
  obtain ⟨N₀, _, hN₀⟩ := classical_low_weighted_uniform 1 0 κ
    (by norm_num) (by norm_num) hκ
  refine ⟨N₀, ?_⟩
  intro N hN
  have h := hN₀ N hN (fun _ => 1) (1 / 10 - κ) (1 / 10)
    continuousOn_const (by intro t ht; norm_num)
    (by intro x hx y hy; norm_num) (by linarith) (by linarith) (by norm_num)
  have ha : 0 < (1 / 10 : ℝ) - κ := by linarith
  have hi : (∫ t in (1 / 10 - κ)..(1 / 10 : ℝ), 1 / t) ≤ 20 * κ := by
    have hi_eq : (∫ t in (1 / 10 - κ)..(1 / 10 : ℝ), 1 / t) =
        log ((1 / 10 : ℝ) / (1 / 10 - κ)) := by
      simpa only [one_div] using
        (integral_inv_of_pos ha (by norm_num : (0 : ℝ) < 1 / 10))
    rw [hi_eq]
    have hl := log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 1 / 10) ha)
    have hr : (1 / 10 : ℝ) / (1 / 10 - κ) - 1 ≤ 20 * κ := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ ha).mpr
      nlinarith [mul_nonneg hκ.le (show 0 ≤ 1 - 20 * κ by linarith)]
    exact hl.trans hr
  change |(∑ p ∈ primesIcc ((N : ℝ) ^ (1 / 10 - κ)) ((N : ℝ) ^ (1 / 10 : ℝ)),
    1 / (p : ℝ)) - (∫ t in (1 / 10 - κ)..(1 / 10 : ℝ), 1 / t)| < κ at h
  linarith [(abs_lt.mp h).2]

theorem firstPrimeBand_pairSum {κ : ℝ} (hκ : 0 < κ) (hκu : κ ≤ 1 / 100) :
    ∃ N₀ : ℕ, 512 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      classicalPairSum N (firstPrimeBandPairs N κ) ≤ 315 * κ := by
  obtain ⟨Ta, hTa⟩ := firstPrimeBand_reciprocal hκ hκu
  obtain ⟨Tb, hTb⟩ := eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually (primeOrdered_reciprocal_uniform 1 (by norm_num)))
  refine ⟨max 512 (max Ta Tb), le_max_left _ _, ?_⟩
  intro N hN
  have h512 : 512 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN1)
  let U := primesIcc ((N : ℝ) ^ (1 / 10 - κ)) ((N : ℝ) ^ (1 / 10 : ℝ))
  let V := primesIcc ((N : ℝ) ^ (1 / 3 : ℝ)) ((N : ℝ) ^ (1 / 2 : ℝ))
  have hU : (∑ p ∈ U, 1 / (p : ℝ)) ≤ 21 * κ :=
    hTa N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hV : (∑ p ∈ V, 1 / (p : ℝ)) ≤ 5 := by
    have h := hTb N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
      (1 / 3) (1 / 2) (by norm_num) (by norm_num) le_rfl
    have hi := (primeOrdered_exponent_density_bounds
      (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2)
      (le_rfl : (1 / 2 : ℝ) ≤ 1 / 2)).2
    dsimp [V]
    linarith [(abs_lt.mp h).2]
  have hsub : firstPrimeBandPairs N κ ⊆ U ×ˢ V := by
    intro p hp
    obtain ⟨hp, hlo, hhi⟩ := mem_filter.mp hp
    obtain ⟨ha, hb, _, _, _, hblo, _, _⟩ := lowerPairs_data (mem_filter.mp hp).1
    have hd := eighth_pair_log_domain hN1 hp
    have hpa : p.1 ∈ U := (mem_primesIcc (rpow_nonneg hN0.le _)).mpr ⟨ha, hlo, hhi⟩
    have hb0 : (0 : ℝ) < p.2 := by exact_mod_cast hb.pos
    have hbhi : (p.2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      apply (log_le_log_iff hb0 (rpow_pos_of_pos hN0 _)).mp
      rw [log_rpow hN0]
      have hc : ninthMainCoordinate N p.2 ≤ 1 / 2 := by
        have hα : (0 : ℝ) < alpha := by norm_num [alpha]
        linarith [hd.1, hd.2.2.2]
      exact (div_le_iff₀ hL).mp hc
    exact mem_product.mpr ⟨hpa,
      (mem_primesIcc (rpow_nonneg hN0.le _)).mpr ⟨hb, hblo, hbhi⟩⟩
  have hk : classicalPairSum N (firstPrimeBandPairs N κ) ≤
      ∑ p ∈ firstPrimeBandPairs N κ, 3 / ((p.1 : ℝ) * p.2) := by
    apply sum_le_sum
    intro p hp
    have hd := eighth_pair_log_domain hN1 (mem_filter.mp hp).1
    have hu := (ninthMain_coordinate_mem hN1 (mem_product.mp (hsub hp)).1).2
    have hgap : 0 < 1 - ninthMainCoordinate N p.1 - ninthMainCoordinate N p.2 := by
      linarith [hd.2.2.2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (div_le_iff₀ hgap).mpr
    linarith [hd.2.2.2]
  have hs : classicalPairSum N (firstPrimeBandPairs N κ) ≤
      3 * (∑ a ∈ U, 1 / (a : ℝ)) * (∑ b ∈ V, 1 / (b : ℝ)) := by
    calc
      _ ≤ _ := hk
      _ ≤ ∑ p ∈ U ×ˢ V, 3 / ((p.1 : ℝ) * p.2) :=
        sum_le_sum_of_subset_of_nonneg hsub (by intro p hp hnot; positivity)
      _ = ∑ a ∈ U, (3 * (1 / (a : ℝ))) * (∑ b ∈ V, 1 / (b : ℝ)) := by
        rw [sum_product]
        apply sum_congr rfl
        intro a ha
        rw [mul_sum]
        apply sum_congr rfl
        intro b hb
        ring
      _ = _ := by rw [← sum_mul, ← mul_sum]
  have hV0 : 0 ≤ ∑ b ∈ V, 1 / (b : ℝ) := by positivity
  exact hs.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hU (by norm_num))
    hV hV0 (by positivity)).trans_eq (by ring))

theorem firstPrimeBand_mass {κ : ℝ} (hκ : 0 < κ) (hκu : κ ≤ 1 / 100) :
    ∃ N₀ : ℕ, 512 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      classicalMass N (firstPrimeBandPairs N κ) ≤ 630 * κ * (N : ℝ) / log N := by
  obtain ⟨Tp, hTp, hp⟩ := firstPrimeBand_pairSum hκ hκu
  obtain ⟨Tm, hm⟩ := eventually_atTop.mp (classicalMass_sharp_pair_bound (by norm_num : (0 : ℝ) < 1))
  refine ⟨max Tp Tm, hTp.trans (le_max_left _ _), ?_⟩
  intro N hN
  have hNp := (le_max_left _ _).trans hN
  have h512 := hTp.trans hNp
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hS : ClassicalPairGeometry N (firstPrimeBandPairs N κ) :=
    fun p hp => eighth_classicalPairGeometry h512 p (mem_filter.mp hp).1
  calc
    _ ≤ _ := hm N ((le_max_right _ _).trans hN) _ hS
    _ ≤ (1 + (1 : ℝ)) * ((N : ℝ) / log N) * (315 * κ) :=
      mul_le_mul_of_nonneg_left (hp N hNp) (by positivity)
    _ = _ := by ring

theorem firstPrimeBand_paid {σ : ℝ} (hσ : 0 < σ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 100 ∧ ∃ N₀ : ℕ, 512 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      ((firstPrimeBand N κ).card : ℝ) ≤
        σ * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * N / log N ^ 2 := by
  let κ : ℝ := min (1 / 100) (σ / 6000)
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκu : κ ≤ 1 / 100 := min_le_left _ _
  have hκσ : 6000 * κ ≤ σ := by
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 6000)).mp
      (min_le_right (1 / 100 : ℝ) (σ / 6000))
    dsimp [κ]
    nlinarith
  have hc : (8 + κ) * (630 * κ) + κ ≤ σ := by
    nlinarith [mul_nonneg hκ.le (show 0 ≤ 1 - κ by linarith)]
  obtain ⟨Ts, hTs, hs⟩ := classicalPhysical_upper_coefficient_eight hκ
  obtain ⟨Tm, _, hm⟩ := firstPrimeBand_mass hκ hκu
  refine ⟨κ, hκ, hκu, max Ts Tm, hTs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNs := (le_max_left _ _).trans hN
  have h512 := hTs.trans hNs
  have hNpos : 0 < N := by omega
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N hNpos
  have hS : ClassicalPairGeometry N (firstPrimeBandPairs N κ) :=
    fun p hp => eighth_classicalPairGeometry h512 p (mem_filter.mp hp).1
  have hmain := mul_le_mul_of_nonneg_left (hm N ((le_max_right _ _).trans hN))
    (show 0 ≤ (8 + κ) * wuSingularSeries N / log N by positivity)
  rw [firstPrimeBand_eq_physical, ← wuSingularSeries_eq_liu N hNpos]
  calc
    _ ≤ _ := hs N hNs hEven _ hS
    _ ≤ ((8 + κ) * wuSingularSeries N / log N) * (630 * κ * (N : ℝ) / log N) +
        κ * wuSingularSeries N * N / log N ^ 2 := add_le_add hmain le_rfl
    _ = ((8 + κ) * (630 * κ) + κ) * (wuSingularSeries N * N / log N ^ 2) := by ring
    _ ≤ σ * (wuSingularSeries N * N / log N ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem paperSmallEighth_le_interior_paid {σ : ℝ} (hσ : 0 < σ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 100 ∧ ∃ N₀ : ℕ, 512 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      ((paperSmallEighth N).card : ℝ) ≤ (firstPrimeInterior N κ).card +
        σ * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * N / log N ^ 2 := by
  obtain ⟨κ, hκ, hκu, N₀, hN₀, hpay⟩ := firstPrimeBand_paid hσ
  refine ⟨κ, hκ, hκu, N₀, hN₀, ?_⟩
  intro N hN hEven
  rw [paperSmallEighth_firstPrime_split N κ, Nat.cast_add]
  exact add_le_add le_rfl (hpay N hN hEven)

end Wu18938Campaign.M6
