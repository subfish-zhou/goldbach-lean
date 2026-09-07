import MathlibNt.SieveTheory.LiLiuGoldbachG11EffectiveProductSupport
import MathlibNt.SieveTheory.LiuPanPrincipalPNT

open scoped BigOperators Topology
open Finset Filter
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.PanPrincipal

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG11PiLiHi (N m : ℕ) : ℝ :=
  min (m.minFac : ℝ) ((N : ℝ) / m)

noncomputable def goldbachG11PiLiLo (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  min (goldbachG11PiLiHi N m) (max ((N : ℝ) ^ (4 / 53 : ℝ)) (ε * N / m))

theorem goldbachG11PiLiEndpoints_bounds {N m : ℕ} {ε : ℝ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    (N : ℝ) ^ (4 / 53 : ℝ) ≤ goldbachG11PiLiLo N ε m ∧
      goldbachG11PiLiLo N ε m ≤ goldbachG11PiLiHi N m ∧
      goldbachG11PiLiHi N m ≤ (N : ℝ) / m := by
  classical
  obtain ⟨hs, _, hm49⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm0, _, _, hfac⟩ := goldbachG11ProductSupport_data hs
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hprod : (N : ℝ) ^ (4 / 53 : ℝ) * (N : ℝ) ^ (49 / 53 : ℝ) = N := by
    rw [← Real.rpow_add hNR]
    norm_num
  have hquot : (N : ℝ) ^ (4 / 53 : ℝ) < (N : ℝ) / m := by
    apply (lt_div_iff₀ hmR).mpr
    calc
      _ < (N : ℝ) ^ (4 / 53 : ℝ) * (N : ℝ) ^ (49 / 53 : ℝ) :=
        mul_lt_mul_of_pos_left hm49 (Real.rpow_pos_of_pos hNR _)
      _ = N := hprod
  have hhi : (N : ℝ) ^ (4 / 53 : ℝ) ≤ goldbachG11PiLiHi N m :=
    le_min hfac hquot.le
  exact ⟨le_min hhi (le_max_left _ _), min_le_left _ _, min_le_right _ _⟩

theorem goldbachG11PiLiLi_normalization (κ x : ℝ) :
    liuLogarithmicIntegral κ x - liuLogarithmicIntegral (2 / Real.log 2) x =
      κ - 2 / Real.log 2 := by
  unfold liuLogarithmicIntegral
  ring

/-- Natural-endpoint PNT, with the actual floor-to-real interval paid separately. -/
theorem goldbachG11PiLi_real_pnt (κ s γ : ℝ) (hs : 0 < s) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ y : ℝ, (N : ℝ) ^ γ ≤ y →
        |primeCount ⌊y⌋₊ - liuLogarithmicIntegral κ y| ≤
          C * y / Real.log (N : ℝ) ^ s := by
  obtain ⟨C, hC, M, hPNT⟩ := primeCount_li_pnt s hs
  have hγ2 : 0 < γ / 2 := by positivity
  let q : ℝ := (γ / 2) ^ s
  let K : ℝ := 1 / Real.log 2 + |2 / Real.log 2 - κ|
  have hq : 0 < q := Real.rpow_pos_of_pos hγ2 _
  have hK : 0 < K := by dsimp [K]; positivity
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      max 2 (M : ℝ) ≤ (N : ℝ) ^ (γ / 2) :=
    ((tendsto_rpow_atTop hγ2).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hgrowth.and (eventually_log_rpow_le_rpow s γ hγ))
  refine ⟨C / q + K, by positivity, max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN y hy
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨hr, hpay⟩ := hN₁ N ((le_max_right _ _).trans hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogpow : 0 < Real.log (N : ℝ) ^ s := Real.rpow_pos_of_pos hlog _
  have hr2 : (2 : ℝ) ≤ (N : ℝ) ^ (γ / 2) := (le_max_left _ _).trans hr
  have hrM : (M : ℝ) ≤ (N : ℝ) ^ (γ / 2) := (le_max_right _ _).trans hr
  have hsq : (N : ℝ) ^ (γ / 2) * (N : ℝ) ^ (γ / 2) = (N : ℝ) ^ γ := by
    rw [← Real.rpow_add hNR]
    congr 1
    ring
  have hr_y : (N : ℝ) ^ (γ / 2) + 1 ≤ y := by
    nlinarith [sq_nonneg ((N : ℝ) ^ (γ / 2) - 1)]
  have hfloor : (N : ℝ) ^ (γ / 2) ≤ (⌊y⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one y]
  have hy0 : 0 ≤ y := (Real.rpow_nonneg hNR.le γ).trans hy
  have hfloor_y : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hfloor2 : (2 : ℝ) ≤ (⌊y⌋₊ : ℝ) := hr2.trans hfloor
  have hfloorM : M ≤ ⌊y⌋₊ := by exact_mod_cast hrM.trans hfloor
  have hlogfloor : 0 < Real.log (⌊y⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogscale : γ / 2 * Real.log (N : ℝ) ≤ Real.log (⌊y⌋₊ : ℝ) := by
    rw [← Real.log_rpow hNR]
    exact Real.log_le_log (Real.rpow_pos_of_pos hNR _) hfloor
  have hden : q * Real.log (N : ℝ) ^ s ≤ Real.log (⌊y⌋₊ : ℝ) ^ s := by
    simpa only [Real.mul_rpow hγ2.le hlog.le] using
      Real.rpow_le_rpow (mul_nonneg hγ2.le hlog.le) hlogscale hs.le
  have hp : |primeCount ⌊y⌋₊ -
      liuLogarithmicIntegral (2 / Real.log 2) (⌊y⌋₊ : ℝ)| ≤
        (C / q) * y / Real.log (N : ℝ) ^ s := by
    calc
      _ ≤ C * (⌊y⌋₊ : ℝ) / Real.log (⌊y⌋₊ : ℝ) ^ s := hPNT _ hfloorM
      _ ≤ C * y / Real.log (⌊y⌋₊ : ℝ) ^ s :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor_y hC.le)
          (Real.rpow_nonneg hlogfloor.le _)
      _ ≤ C * y / (q * Real.log (N : ℝ) ^ s) :=
        div_le_div_of_nonneg_left (mul_nonneg hC.le hy0) (mul_pos hq hlogpow) hden
      _ = _ := by ring
  have hshort : |liuLogarithmicIntegral (2 / Real.log 2) (⌊y⌋₊ : ℝ) -
      liuLogarithmicIntegral (2 / Real.log 2) y| ≤ 1 / Real.log 2 := by
    rw [abs_sub_comm]
    exact abs_li_sub_le_short _ hfloor2 hfloor_y (Nat.lt_floor_add_one y).le
  have hnorm : |liuLogarithmicIntegral (2 / Real.log 2) y -
      liuLogarithmicIntegral κ y| = |2 / Real.log 2 - κ| := by
    rw [abs_sub_comm, goldbachG11PiLiLi_normalization, abs_sub_comm]
  have hcorr : K ≤ K * y / Real.log (N : ℝ) ^ s := by
    apply (le_div_iff₀ hlogpow).mpr
    exact mul_le_mul_of_nonneg_left (hpay.trans hy) hK.le
  calc
    _ ≤ |primeCount ⌊y⌋₊ -
          liuLogarithmicIntegral (2 / Real.log 2) (⌊y⌋₊ : ℝ)| +
        |liuLogarithmicIntegral (2 / Real.log 2) (⌊y⌋₊ : ℝ) -
          liuLogarithmicIntegral κ y| := abs_sub_le _ _ _
    _ ≤ (C / q) * y / Real.log (N : ℝ) ^ s + K := by
      apply add_le_add hp
      calc
        _ ≤ |liuLogarithmicIntegral (2 / Real.log 2) (⌊y⌋₊ : ℝ) -
              liuLogarithmicIntegral (2 / Real.log 2) y| +
            |liuLogarithmicIntegral (2 / Real.log 2) y -
              liuLogarithmicIntegral κ y| := abs_sub_le _ _ _
        _ ≤ K := by rw [hnorm]; exact add_le_add hshort le_rfl
    _ ≤ (C / q) * y / Real.log (N : ℝ) ^ s +
        K * y / Real.log (N : ℝ) ^ s := add_le_add le_rfl hcorr
    _ = _ := by ring

noncomputable def goldbachG11PiLiEndpointError (κ : ℝ) (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  (primeCount ⌊goldbachG11PiLiHi N m⌋₊ - primeCount ⌊goldbachG11PiLiLo N ε m⌋₊) -
    (liuLogarithmicIntegral κ (goldbachG11PiLiHi N m) -
      liuLogarithmicIntegral κ (goldbachG11PiLiLo N ε m))

theorem goldbachG11PiLiEndpointError_eq_zero {κ ε : ℝ} {N m : ℕ}
    (h : goldbachG11PiLiLo N ε m = goldbachG11PiLiHi N m) :
    goldbachG11PiLiEndpointError κ N ε m = 0 := by
  simp only [goldbachG11PiLiEndpointError, h, sub_self]

theorem goldbachG11PiLiLo_one (N m : ℕ) :
    goldbachG11PiLiLo N 1 m = goldbachG11PiLiHi N m := by
  unfold goldbachG11PiLiLo goldbachG11PiLiHi
  rw [one_mul]
  apply min_eq_left
  exact (min_le_right (m.minFac : ℝ) ((N : ℝ) / m)).trans
    (le_max_right ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) / m))

/-- The two actual geometric endpoints retain the reciprocal-product scale. -/
theorem goldbachG11PiLi_endpoint_pnt (κ s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ ε : ℝ, ∀ m ∈ goldbachG11EffectiveProductSupport N ε,
        |goldbachG11PiLiEndpointError κ N ε m| ≤
          C * ((N : ℝ) / m) / Real.log (N : ℝ) ^ s := by
  obtain ⟨C, hC, N₀, hN₀, hp⟩ := goldbachG11PiLi_real_pnt κ s (4 / 53) hs (by norm_num)
  refine ⟨2 * C, by positivity, N₀, hN₀, ?_⟩
  intro N hN ε m hm
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hlo, hlohi, hhi⟩ := goldbachG11PiLiEndpoints_bounds hN2 hm
  have hden : 0 ≤ Real.log (N : ℝ) ^ s :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hupper : |primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
      liuLogarithmicIntegral κ (goldbachG11PiLiHi N m)| ≤
        C * ((N : ℝ) / m) / Real.log (N : ℝ) ^ s :=
    (hp N hN _ (hlo.trans hlohi)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hC.le) hden)
  have hlower : |primeCount ⌊goldbachG11PiLiLo N ε m⌋₊ -
      liuLogarithmicIntegral κ (goldbachG11PiLiLo N ε m)| ≤
        C * ((N : ℝ) / m) / Real.log (N : ℝ) ^ s :=
    (hp N hN _ hlo).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hlohi.trans hhi) hC.le) hden)
  calc
    _ = |(primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
          liuLogarithmicIntegral κ (goldbachG11PiLiHi N m)) -
        (primeCount ⌊goldbachG11PiLiLo N ε m⌋₊ -
          liuLogarithmicIntegral κ (goldbachG11PiLiLo N ε m))| := by
      unfold goldbachG11PiLiEndpointError
      congr 1
      ring
    _ ≤ |primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
          liuLogarithmicIntegral κ (goldbachG11PiLiHi N m)| +
        |primeCount ⌊goldbachG11PiLiLo N ε m⌋₊ -
          liuLogarithmicIntegral κ (goldbachG11PiLiLo N ε m)| := abs_sub _ _
    _ ≤ C * ((N : ℝ) / m) / Real.log (N : ℝ) ^ s +
        C * ((N : ℝ) / m) / Real.log (N : ℝ) ^ s := add_le_add hupper hlower
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig