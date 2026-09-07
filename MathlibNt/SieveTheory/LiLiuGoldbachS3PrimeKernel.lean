import MathlibNt.SieveTheory.LiLiuGoldbachS3RatioGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachUpperThirdInterval
import MathlibNt.SieveTheory.LiLiuGoldbachRationalEndpoints
import MathlibNt.SieveTheory.LiLiuGoldbachTotientCorrection
import MathlibNt.SieveTheory.MertensTheorem

open scoped BigOperators
open Filter
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachS3_primeKernelIntegral (β : ℝ) : ℝ :=
  ∫ u in (4 / 53 : ℝ)..β,
    suzukiContinuousUpperFactor (((1 / 2 : ℝ) - u) / (4 / 53 : ℝ)) / u

private noncomputable def S3Kernel_model (u : ℝ) : ℝ :=
  suzukiContinuousUpperFactor (((1 / 2 : ℝ) - u) / (4 / 53 : ℝ))

private theorem S3Kernel_argument_mem
    {u : ℝ} (hu : u ∈ Set.Icc (4 / 53 : ℝ) (1 / 3 : ℝ)) :
    ((1 / 2 : ℝ) - u) / (4 / 53 : ℝ) ∈ Set.Icc (3 / 2 : ℝ) 7 := by
  constructor <;> linarith [hu.1, hu.2]

private theorem S3Kernel_log_mem
    {N p : ℕ} {a b : ℝ} (hN : 4 ≤ N) (hp : 0 < p)
    (hl : (N : ℝ) ^ a ≤ (p : ℝ)) (hu : (p : ℝ) ≤ (N : ℝ) ^ b) :
    Real.log (p : ℝ) / Real.log (N : ℝ) ∈ Set.Icc a b := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hll := Real.log_le_log (Real.rpow_pos_of_pos hN0 a) hl
  have hlu := Real.log_le_log hp0 hu
  rw [Real.log_rpow hN0] at hll hlu
  exact ⟨(le_div_iff₀ hL).2 hll, (div_le_iff₀ hL).2 hlu⟩

private theorem S3Kernel_model_continuous
    {β : ℝ} (hβ : β ≤ (1 / 3 : ℝ)) :
    ContinuousOn S3Kernel_model (Set.Icc (4 / 53 : ℝ) β) := by
  apply goldbach_suzukiUpperFactor_continuousOn_threeHalves_seven.comp
    ((continuous_const.sub continuous_id).div_const (4 / 53 : ℝ)).continuousOn
  intro u hu
  exact S3Kernel_argument_mem ⟨hu.1, hu.2.trans hβ⟩

private theorem S3Kernel_uniform
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, 1 ≤ p →
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      0 ≤ suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) ∧
      |suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) -
        S3Kernel_model (Real.log (p : ℝ) / Real.log (N : ℝ))| ≤ ε := by
  have hc := isCompact_Icc.uniformContinuousOn_of_continuous
    goldbach_suzukiUpperFactor_continuousOn_threeHalves_seven
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff_le.mp hc ε hε
  obtain ⟨N₀, hN₀, hratio⟩ := goldbachS3_ratio_geometry B δ hB hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN p hp hl hu
  have hN4 := hN₀.trans hN
  obtain ⟨_, hslo, hshi, hsclose⟩ := hratio N hN p hp hl hu
  have hs : goldbachS3_sieveRatio N B p ∈ Set.Icc (3 / 2 : ℝ) 7 :=
    ⟨hslo, by linarith⟩
  have ht := S3Kernel_argument_mem (S3Kernel_log_mem hN4 (by omega) hl hu)
  refine ⟨le_trans (by norm_num) (goldbach_one_le_suzukiUpperFactor (by linarith)), ?_⟩
  exact hclose _ hs _ ht (by simpa only [Real.dist_eq] using hsclose)

private theorem S3Kernel_carrier_subset (N : ℕ) (β : ℝ) :
    goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β) ⊆
      (Finset.Ioc (MertensTheorem.rpowFloor N (4 / 53 : ℝ))
        (MertensTheorem.rpowFloor N β)).filter Nat.Prime := by
  intro p hp
  rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hprime, hpN, hl, hu⟩
  have hne : (p : ℝ) ≠ (N : ℝ) ^ (4 / 53 : ℝ) :=
    goldbachPrime_ne_rpow_of_not_dvd N p 4 53 hprime hpN (by norm_num)
  exact Finset.mem_filter.mpr
    ⟨MertensTheorem.mem_Ioc_rpowFloor_iff.mpr ⟨lt_of_le_of_ne hl hne.symm, hu⟩, hprime⟩

private theorem S3Kernel_window_nonneg
    {N p : ℕ} {β : ℝ} (hN : 4 ≤ N) (hβ : β ≤ (1 / 3 : ℝ))
    (hp : p ∈ (Finset.Ioc (MertensTheorem.rpowFloor N (4 / 53 : ℝ))
      (MertensTheorem.rpowFloor N β)).filter Nat.Prime) :
    0 ≤ S3Kernel_model (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) := by
  obtain ⟨hwindow, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hl, hu⟩ := MertensTheorem.mem_Ioc_rpowFloor_iff.mp hwindow
  have hlog := S3Kernel_log_mem hN hprime.pos hl.le hu
  have hs := S3Kernel_argument_mem ⟨hlog.1, hlog.2.trans hβ⟩
  apply div_nonneg _ (Nat.cast_nonneg p)
  exact le_trans (by norm_num) (goldbach_one_le_suzukiUpperFactor (by linarith [hs.1]))

private theorem S3Kernel_const_eventually
    {β ε : ℝ} (hβ : (4 / 53 : ℝ) < β) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      MertensTheorem.weightedPrimeReciprocalLogSum (fun _ : ℝ => 1)
        N (4 / 53 : ℝ) β ≤ Real.log (β / (4 / 53 : ℝ)) + ε := by
  have ht := MertensTheorem.tendsto_weightedPrimeReciprocalLogSum_const
    (c := 1) (by norm_num : (0 : ℝ) < 4 / 53) hβ
  have hc := (Metric.tendsto_nhds.1 ht) ε hε
  filter_upwards [hc] with N hN
  simp only [one_mul, Real.dist_eq] at hN
  linarith [(abs_lt.mp hN).2]

private theorem S3Kernel_unit_reciprocal_le (N : ℕ) (β : ℝ) :
    (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
      (1 : ℝ) / (p : ℝ)) ≤
      MertensTheorem.weightedPrimeReciprocalLogSum (fun _ : ℝ => 1)
        N (4 / 53 : ℝ) β := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (S3Kernel_carrier_subset N β)
    (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))

private theorem S3Kernel_reciprocal_eventually
    (B β η : ℝ) (hB : 0 ≤ B) (hβ : (4 / 53 : ℝ) < β)
    (hβu : β ≤ (1 / 3 : ℝ)) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) / (p : ℝ)) ≤
        goldbachS3_primeKernelIntegral β + η := by
  let K : ℝ := Real.log (β / (4 / 53 : ℝ)) + 1
  have hK : 0 < K := by
    have hr : 1 < β / (4 / 53 : ℝ) := (one_lt_div (by norm_num)).2 hβ
    dsimp [K]
    linarith [Real.log_pos hr]
  let ε : ℝ := η / (2 * K)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨M, hM4, hM⟩ := S3Kernel_uniform B ε hB hε
  have ht := MertensTheorem.tendsto_weightedPrimeReciprocalLogSum
    (by norm_num : (0 : ℝ) < 4 / 53) hβ (S3Kernel_model_continuous hβu)
  have hmain : ∀ᶠ N : ℕ in atTop,
      MertensTheorem.weightedPrimeReciprocalLogSum S3Kernel_model N (4 / 53 : ℝ) β ≤
        goldbachS3_primeKernelIntegral β + η / 2 := by
    have hc := (Metric.tendsto_nhds.1 ht) (η / 2) (by positivity)
    filter_upwards [hc] with N hN
    change dist _ (goldbachS3_primeKernelIntegral β) < η / 2 at hN
    rw [Real.dist_eq] at hN
    linarith [(abs_lt.mp hN).2]
  filter_upwards [eventually_ge_atTop M, hmain,
    S3Kernel_const_eventually hβ zero_lt_one] with N hN hm hc
  have hN4 : 4 ≤ N := hM4.trans hN
  let S := goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β)
  have hmove :
      (∑ p ∈ S, suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) / (p : ℝ)) ≤
        (∑ p ∈ S, S3Kernel_model (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) +
          ε * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hprime, _, hl, hu⟩
    have hupper : (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := hu.trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hβu)
    have hdiff := (hM N hN p hprime.one_le hl hupper).2
    have hpoint : suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) ≤
        S3Kernel_model (Real.log (p : ℝ) / Real.log (N : ℝ)) + ε := by
      linarith [(abs_le.mp hdiff).2]
    calc
      _ ≤ (S3Kernel_model (Real.log (p : ℝ) / Real.log (N : ℝ)) + ε) / (p : ℝ) :=
        div_le_div_of_nonneg_right hpoint (Nat.cast_nonneg p)
      _ = _ := by ring
  have hmodel :
      (∑ p ∈ S, S3Kernel_model (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) ≤
        MertensTheorem.weightedPrimeReciprocalLogSum S3Kernel_model N (4 / 53 : ℝ) β :=
    Finset.sum_le_sum_of_subset_of_nonneg (S3Kernel_carrier_subset N β)
      (fun p hp _ => S3Kernel_window_nonneg hN4 hβu hp)
  have hunit : (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) ≤ K :=
    (S3Kernel_unit_reciprocal_le N β).trans hc
  have herr : ε * K = η / 2 := by
    dsimp [ε]
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hunit hε.le
  change (∑ p ∈ S, _) ≤ _
  linarith

private theorem S3Kernel_totient_transfer
    (β L : ℝ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        0 ≤ w N p)
    (hm : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        w N p / (p : ℝ)) ≤ L + ε)
    (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        w N p / (p.totient : ℝ)) ≤ L + η := by
  let ε : ℝ := min 1 (η / (2 * (|L| + 2)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hbudget : ε * (|L| + 2) ≤ η / 2 := by
    have he : ε ≤ η / (2 * (|L| + 2)) := min_le_right _ _
    have hd : 0 < 2 * (|L| + 2) := by positivity
    have hh := (le_div_iff₀ hd).mp he
    nlinarith
  obtain ⟨M, _, hM⟩ := goldbachS3PrimeWeights_totient_upper_eventually
    (4 / 53 : ℝ) ε (by norm_num) hε
  have he : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        w N p / (p.totient : ℝ)) ≤ L + η := by
    filter_upwards [eventually_ge_atTop M, hw, hm ε hε] with N hN hn hmain
    have hpaid := hM N hN ((N : ℝ) ^ β) (w N) hn
    have hmul := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ 1 + ε)
    have hsq : ε * ε ≤ ε := by nlinarith
    have hL := mul_le_mul_of_nonneg_left (le_abs_self L) hε.le
    nlinarith
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp he
  refine ⟨max 4 M₀, le_max_left _ _, ?_⟩
  intro N hN
  exact hM₀ N ((le_max_right _ _).trans hN)

/-- The main-term payment for the actual closed S3 prime set, with the
genuine rounded Pan ratio and the positive inverse-totient correction. -/
theorem goldbachS3_primeKernel_upper
    (B β η : ℝ) (hB : 0 ≤ B) (hβ : (4 / 53 : ℝ) < β)
    (hβu : β ≤ (1 / 3 : ℝ)) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) / (p.totient : ℝ)) ≤
        goldbachS3_primeKernelIntegral β + η := by
  apply S3Kernel_totient_transfer β (goldbachS3_primeKernelIntegral β)
    (fun N p => suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p)) _ _ η hη
  · obtain ⟨M, hM4, hM⟩ := S3Kernel_uniform B 1 hB zero_lt_one
    filter_upwards [eventually_ge_atTop M] with N hN
    intro p hp
    rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hprime, _, hl, hu⟩
    have hN4 := hM4.trans hN
    apply (hM N hN p hprime.one_le hl _).1
    exact hu.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) hβu)
  · intro ε hε
    exact S3Kernel_reciprocal_eventually B β ε hB hβ hβu hε

/-- Unit-weight payment for additive noise on the same actual closed carrier. -/
theorem goldbachS3_unitKernel_upper
    (β η : ℝ) (hβ : (4 / 53 : ℝ) < β) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        (1 : ℝ) / (p.totient : ℝ)) ≤ Real.log (β / (4 / 53 : ℝ)) + η := by
  apply S3Kernel_totient_transfer β (Real.log (β / (4 / 53 : ℝ)))
    (fun _ _ => 1) _ _ η hη
  · exact Eventually.of_forall (fun _ _ _ => zero_le_one)
  · intro ε hε
    filter_upwards [S3Kernel_const_eventually hβ hε] with N hN
    exact (S3Kernel_unit_reciprocal_le N β).trans hN

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig