import MathlibNt.SieveTheory.LiLiuGoldbachB10MainWeight

open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachB10ContinuousMainWeight (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  liuLogarithmicIntegral goldbachB10PanKappa0 ((N : ℝ) / m) -
    liuLogarithmicIntegral goldbachB10PanKappa0 (ε * (N : ℝ) / m)

noncomputable def goldbachB10ContinuousMainMass (N : ℕ) (ε b c : ℝ) : ℝ :=
  ∑ m ∈ goldbachC10ProductSupport N b c, goldbachB10ContinuousMainWeight N ε m

/-- Flooring increases the main weight; the interval correction is charged with its sign. -/
theorem goldbachB10MainWeight_sub_continuous_nonneg_le
    {N m : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hm : 0 < m)
    (hlo : 2 ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) / m) :
    0 ≤ goldbachB10MainWeight N ε m - goldbachB10ContinuousMainWeight N ε m ∧
      goldbachB10MainWeight N ε m - goldbachB10ContinuousMainWeight N ε m ≤
        (1 / Real.log 2) * (1 / (m : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hf := Nat.floor_le (mul_nonneg hε (Nat.cast_nonneg N))
  have hf' := Nat.lt_floor_add_one (ε * (N : ℝ))
  have hi := b10_li_difference_nonneg_le goldbachB10PanKappa0
    ((⌊ε * (N : ℝ)⌋₊ : ℝ) / m) (ε * (N : ℝ) / m) hlo
    (div_le_div_of_nonneg_right hf hmpos.le)
  have heq : goldbachB10MainWeight N ε m - goldbachB10ContinuousMainWeight N ε m =
      liuLogarithmicIntegral goldbachB10PanKappa0 (ε * (N : ℝ) / m) -
        liuLogarithmicIntegral goldbachB10PanKappa0 ((⌊ε * (N : ℝ)⌋₊ : ℝ) / m) := by
    unfold goldbachB10MainWeight goldbachB10ContinuousMainWeight
    ring
  rw [heq]
  refine ⟨hi.1, hi.2.trans ?_⟩
  calc
    _ ≤ (1 / (m : ℝ)) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith) hmpos.le
    _ = _ := by ring

/-- Same-support finite floor correction; no prime labels or endpoints are removed. -/
theorem goldbachB10MainMass_sub_continuous_nonneg_le
    {N : ℕ} {ε b c : ℝ} (hε : 0 ≤ ε)
    (hlo : ∀ m ∈ goldbachC10ProductSupport N b c,
      0 < m ∧ 2 ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) / m) :
    0 ≤ goldbachB10MainMass N ε b c - goldbachB10ContinuousMainMass N ε b c ∧
      goldbachB10MainMass N ε b c - goldbachB10ContinuousMainMass N ε b c ≤
        (1 / Real.log 2) * ∑ m ∈ goldbachC10ProductSupport N b c, 1 / (m : ℝ) := by
  unfold goldbachB10MainMass goldbachB10ContinuousMainMass
  rw [← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun m hm =>
      (goldbachB10MainWeight_sub_continuous_nonneg_le hε (hlo m hm).1 (hlo m hm).2).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun m hm =>
      (goldbachB10MainWeight_sub_continuous_nonneg_le hε (hlo m hm).1 (hlo m hm).2).2)

private theorem B10Floor_two_mul_le_of_rpow {Y m : ℕ} (hY : 8 ≤ Y)
    (hm : (m : ℝ) ≤ (Y : ℝ) ^ ((2 : ℝ) / 3)) : 2 * (m : ℝ) ≤ Y := by
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
    calc
      (8 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by norm_num
      _ = (2 : ℝ) ^ ((3 : ℝ) * (1 / 3)) := (Real.rpow_mul (by norm_num) _ _).symm
      _ = 2 := by norm_num
  have hr : (2 : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← h8]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hY) (by norm_num)
  calc
    2 * (m : ℝ) ≤ 2 * (Y : ℝ) ^ ((2 : ℝ) / 3) := by gcongr
    _ ≤ (Y : ℝ) ^ ((1 : ℝ) / 3) * (Y : ℝ) ^ ((2 : ℝ) / 3) := by gcongr
    _ = Y := by rw [← Real.rpow_add hYpos]; norm_num

/-- A uniform-in-beta floor payment. The coarse power bound suffices for the main scale. -/
theorem goldbachB10MainMass_floor_payment_eventually
    (ε γ : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ, (1 : ℝ) / 18 < β →
      0 ≤ goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
          goldbachB10ContinuousMainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ∧
        goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
          goldbachB10ContinuousMainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≤
            (1 / Real.log 2) * (N : ℝ) ^ ((2 : ℝ) / 3) := by
  classical
  obtain ⟨N₀, hN₀, hgeo⟩ := B10PanGeometry_consumer_threshold ε γ 0 0 8
    hε hεlt hγ (by norm_num) (by norm_num)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN β hβ
  rcases hgeo N hN with ⟨_, hY8, _, _, _, hA2Y, _, _, _, _, hsupp⟩
  have hsub := hsupp β hβ
  have hYle : (⌊ε * (N : ℝ)⌋₊ : ℝ) ≤ N :=
    (Nat.floor_le (by positivity : 0 ≤ ε * (N : ℝ))).trans (by nlinarith)
  have hlow : ∀ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ),
      0 < m ∧ 2 ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) / m := by
    intro m hm
    have hmi := Finset.mem_Ioc.mp (hsub m hm)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmA2 : (m : ℝ) ≤ B10PanGeometryUpperWindow N γ := by exact_mod_cast hmi.2
    exact ⟨by omega, (le_div_iff₀ hmpos).mpr (B10Floor_two_mul_le_of_rpow hY8 (hmA2.trans hA2Y))⟩
  have hc := goldbachB10MainMass_sub_continuous_nonneg_le hε.le hlow
  refine ⟨hc.1, hc.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ), 1 / (m : ℝ)) ≤
        (goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card := by
      calc
        _ ≤ ∑ _m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (hlow m hm).1
          simpa using one_div_le_one_div_of_le (by norm_num) hm1
        _ = _ := by simp
    _ ≤ (B10PanGeometryUpperWindow N γ : ℝ) := by
      exact_mod_cast (Finset.card_le_card (fun m hm => hsub m hm)).trans (by simp [Nat.card_Ioc])
    _ ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ ((2 : ℝ) / 3) := hA2Y
    _ ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) hYle (by norm_num)

theorem goldbachB10MainMass_floor_payment_mainScale
    (ε γ η : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ, (1 : ℝ) / 18 < β →
      0 ≤ goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
          goldbachB10ContinuousMainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ∧
        goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
          goldbachB10ContinuousMainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≤
            η * (N : ℝ) / Real.log (N : ℝ) := by
  obtain ⟨Nf, hNf, hf⟩ := goldbachB10MainMass_floor_payment_eventually ε γ hε hεlt hγ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
    (show 0 < (1 : ℝ) / 3 by norm_num)).bound (mul_pos hη hlog2)
  obtain ⟨Np, hp⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually hsmall)
  refine ⟨max Nf Np, hNf.trans (le_max_left _ _), ?_⟩
  intro N hN β hβ
  have hNf' : Nf ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := hNf.trans hNf'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpay : Real.log (N : ℝ) ≤ (η * Real.log 2) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
    simpa only [Real.rpow_one, Real.norm_of_nonneg hlog.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] using hp N ((le_max_right _ _).trans hN)
  have hfN := hf N hNf' β hβ
  refine ⟨hfN.1, hfN.2.trans ((le_div_iff₀ hlog).mpr ?_)⟩
  calc
    (1 / Real.log 2) * (N : ℝ) ^ ((2 : ℝ) / 3) * Real.log (N : ℝ) ≤
        (1 / Real.log 2) * (N : ℝ) ^ ((2 : ℝ) / 3) *
          ((η * Real.log 2) * (N : ℝ) ^ ((1 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left hpay (by positivity)
    _ = (1 / Real.log 2 * Real.log 2) * η *
        ((N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3)) := by ring
    _ = η * (N : ℝ) := by
      rw [one_div_mul_cancel (ne_of_gt hlog2), one_mul, ← Real.rpow_add hNpos]
      norm_num

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig