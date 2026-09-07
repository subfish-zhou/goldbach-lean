import MathlibNt.SieveTheory.LiLiuGoldbachG11PiLiEndpoints
import MathlibNt.SieveTheory.LiuPanCofactorMass

open scoped BigOperators Topology
open Finset Filter
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanPrincipal

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG11PiLiCenterMass (κ : ℝ) (N : ℕ) (ε : ℝ) (D : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ Icc 1 D,
    |∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => Nat.Coprime m d),
      goldbachG11EffectiveProductCoefficient N ε m *
        (goldbachG11PiLiEndpointError κ N ε m / (d.totient : ℝ))|

theorem goldbachG11PiLiCenterMass_zero (κ : ℝ) (N : ℕ) (ε : ℝ) :
    goldbachG11PiLiCenterMass κ N ε 0 = 0 := by
  simp [goldbachG11PiLiCenterMass]

theorem goldbachG11PiLiCenterMass_eps_one (κ : ℝ) (N D : ℕ) :
    goldbachG11PiLiCenterMass κ N 1 D = 0 := by
  classical
  have hzero (m : ℕ) : goldbachG11PiLiEndpointError κ N 1 m = 0 :=
    goldbachG11PiLiEndpointError_eq_zero (goldbachG11PiLiLo_one N m)
  simp [goldbachG11PiLiCenterMass, hzero]

theorem goldbachG11PiLi_reciprocal_product_mass (N d : ℕ) (ε : ℝ) :
    (∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => Nat.Coprime m d),
      (m : ℝ)⁻¹) ≤ 1 + Real.log (N : ℝ) := by
  classical
  calc
    _ ≤ ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
        obtain ⟨hm0, hmN, _⟩ := goldbachG11ProductSupport_data hs
        exact Finset.mem_Icc.mpr ⟨hm0, hmN.le⟩
      · intro m _ _
        positivity
    _ ≤ _ := conductorHarmonicFactor_le N

/-- Only the centering difference is triangularized; this is not an AP distribution bound. -/
theorem goldbachG11PiLi_center_mass_bound (κ U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ ε : ℝ, ∀ D : ℕ, D ≤ N →
        goldbachG11PiLiCenterMass κ N ε D ≤ C * N / Real.log (N : ℝ) ^ U := by
  classical
  obtain ⟨A, hA, M, hM, hp⟩ := goldbachG11PiLi_endpoint_pnt κ (U + 4) (by linarith)
  have hlogevent : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  obtain ⟨M', hM'⟩ := eventually_atTop.mp hlogevent
  refine ⟨8 * A, by positivity, max M M', hM.trans (le_max_left _ _), ?_⟩
  intro N hN ε D hDN
  have hNM : M ≤ N := (le_max_left _ _).trans hN
  have hlog1 : 1 ≤ Real.log (N : ℝ) := hM' N ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := by linarith
  let T : ℝ := A * N / Real.log (N : ℝ) ^ (U + 4)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpoint (d m : ℕ) (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
      |goldbachG11EffectiveProductCoefficient N ε m *
        (goldbachG11PiLiEndpointError κ N ε m / (d.totient : ℝ))| ≤
          T * (m : ℝ)⁻¹ * (d.totient : ℝ)⁻¹ := by
    obtain ⟨ha0, ha1⟩ := goldbachG11EffectiveProductCoefficient_bounds N m ε
    rw [abs_mul, abs_of_nonneg ha0, abs_div,
      abs_of_nonneg (show 0 ≤ (d.totient : ℝ) from Nat.cast_nonneg _)]
    calc
      _ ≤ 1 * (A * ((N : ℝ) / m) / Real.log (N : ℝ) ^ (U + 4) /
          (d.totient : ℝ)) := by
        apply mul_le_mul ha1
        · exact div_le_div_of_nonneg_right (hp N hNM ε m hm) (Nat.cast_nonneg _)
        · positivity
        · norm_num
      _ = _ := by dsimp [T]; simp only [div_eq_mul_inv]; ring
  have hinner (d : ℕ) :
      |∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => Nat.Coprime m d),
        goldbachG11EffectiveProductCoefficient N ε m *
          (goldbachG11PiLiEndpointError κ N ε m / (d.totient : ℝ))| ≤
            T * (1 + Real.log (N : ℝ)) * (d.totient : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter
            (fun m => Nat.Coprime m d),
          |goldbachG11EffectiveProductCoefficient N ε m *
            (goldbachG11PiLiEndpointError κ N ε m / (d.totient : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter
            (fun m => Nat.Coprime m d), T * (m : ℝ)⁻¹ * (d.totient : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro m hm
        exact hpoint d m (Finset.mem_filter.mp hm).1
      _ = (T * (d.totient : ℝ)⁻¹) *
          ∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter
            (fun m => Nat.Coprime m d), (m : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ ≤ (T * (d.totient : ℝ)⁻¹) * (1 + Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (goldbachG11PiLi_reciprocal_product_mass N d ε)
          (mul_nonneg hT (by positivity))
      _ = _ := by ring
  have hfinite : goldbachG11PiLiCenterMass κ N ε D ≤
      T * (1 + Real.log (N : ℝ)) ^ 3 := by
    calc
      _ ≤ ∑ d ∈ Icc 1 D, T * (1 + Real.log (N : ℝ)) * (d.totient : ℝ)⁻¹ :=
        Finset.sum_le_sum (fun d _ => hinner d)
      _ = (T * (1 + Real.log (N : ℝ))) *
          ∑ d ∈ Icc 1 D, (d.totient : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ (T * (1 + Real.log (N : ℝ))) * (1 + Real.log (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hDN)
          (mul_nonneg hT (by linarith))
      _ = _ := by ring
  have hlogcube : (1 + Real.log (N : ℝ)) ^ 3 ≤ 8 * Real.log (N : ℝ) ^ 4 := by
    calc
      _ ≤ (2 * Real.log (N : ℝ)) ^ 3 := by gcongr; linarith
      _ = 8 * Real.log (N : ℝ) ^ 3 := by ring
      _ ≤ 8 * Real.log (N : ℝ) ^ 4 := by
        have hpow : 0 ≤ Real.log (N : ℝ) ^ 3 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hlog1 hpow]
  calc
    _ ≤ T * (1 + Real.log (N : ℝ)) ^ 3 := hfinite
    _ ≤ T * (8 * Real.log (N : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hlogcube hT
    _ = (8 * A) * N / Real.log (N : ℝ) ^ U := by
      dsimp [T]
      rw [Real.rpow_add hlog, Real.rpow_ofNat]
      field_simp [ne_of_gt hlog]

theorem goldbachG11PiLi_center_change (κ U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ ε : ℝ, ∀ D : ℕ, D ≤ N →
        (∑ d ∈ Icc 1 D,
          |∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => Nat.Coprime m d),
            goldbachG11EffectiveProductCoefficient N ε m *
              (((primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
                  primeCount ⌊goldbachG11PiLiLo N ε m⌋₊) -
                (liuLogarithmicIntegral κ (goldbachG11PiLiHi N m) -
                  liuLogarithmicIntegral κ (goldbachG11PiLiLo N ε m))) /
                (d.totient : ℝ))|) ≤ C * N / Real.log (N : ℝ) ^ U :=
  goldbachG11PiLi_center_mass_bound κ U hU

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig