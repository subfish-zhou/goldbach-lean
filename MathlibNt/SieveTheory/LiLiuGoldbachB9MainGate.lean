import MathlibNt.SieveTheory.LiuWeightMainSum
import MathlibNt.SieveTheory.LiLiuGoldbachS4CarrierGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachB10MainGateBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators
open Filter Finset
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The genuine full-prefix Li weight, with no lower-endpoint subtraction. -/
noncomputable def goldbachB9PlusLiWeight (N m : ℕ) : ℝ :=
  liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (m : ℝ))

/-- The full-prefix mass on the actual closed C10 product support. -/
noncomputable def goldbachB9PlusMainMass (N : ℕ) : ℝ :=
  ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)), goldbachB9PlusLiWeight N m

theorem goldbachB9PlusMainMass_eq_pair_sum (N : ℕ) :
    goldbachB9PlusMainMass N =
      ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / goldbachC10Prod rs) := by
  unfold goldbachB9PlusMainMass goldbachC10ProductSupport goldbachB9PlusLiWeight
  exact Finset.sum_image (fun _ hx _ hy h => goldbachC10Prod_injOn hx hy h)

private theorem B9MainGate_mem_S4Pairs {N : ℕ} {b c : ℝ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N b c) :
    rs ∈ goldbachS4Pairs N b := by
  obtain ⟨hr, hs, hcop, hbr, hrc, hcs, hsize⟩ := mem_goldbachC10Pairs_iff.mp hrs
  exact mem_goldbachS4Pairs_iff.mpr
    ⟨hr, hs, hcop, hbr, by exact_mod_cast hrc.trans hcs, hsize⟩

/-- The closed `gamma = 1/3` endpoint uses only the generic S4 product geometry. -/
theorem goldbachB9ProductSupport_bounds {N m : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    0 < m ∧ (m : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) ∧
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) / m := by
  have hmp := goldbachC10ProductSupport_pos hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hmp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmu : (m : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
    obtain ⟨rs, hrs, hprod⟩ := mem_goldbachC10ProductSupport_iff.mp hm
    simpa only [goldbachC8Prod, ← hprod, goldbachC10Prod] using
      goldbachC8Prod_le_two_thirds hN (B9MainGate_mem_S4Pairs hrs)
  refine ⟨hmp, hmu, (le_div_iff₀ hmpos).mpr ?_⟩
  calc
    (N : ℝ) ^ (1 / 3 : ℝ) * m ≤
        (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hmu (Real.rpow_nonneg hNpos.le _)
    _ = N := by rw [← Real.rpow_add hNpos]; norm_num

/-- One threshold works for every member of the actual support; the fixed weight
constant is `T = 2`. Positivity comes from the genuine Li lower bound. -/
theorem goldbachB9PlusLiWeight_bounds_eventually :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        2 ≤ (N : ℝ) / m ∧ 0 ≤ goldbachB9PlusLiWeight N m ∧
          |goldbachB9PlusLiWeight N m| ≤ 2 * (N : ℝ) / m := by
  obtain ⟨C, _hC, hr⟩ := eventually_abs_liuLogarithmicIntegralRemainder_le (2 / Real.log 2)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hr
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (max 2 (max x₀ (Real.exp (max C 1))))))
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN m hm
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hroot := (goldbachB9ProductSupport_bounds (by omega) hm).2.2
  have hlarge := (hM N ((le_max_right _ _).trans hN)).trans hroot
  have hx2 : 2 ≤ (N : ℝ) / m := (le_max_left _ _).trans hlarge
  have hx0 : 0 ≤ (N : ℝ) / m := by positivity
  have hlog : max C 1 ≤ Real.log ((N : ℝ) / m) := by
    have he : Real.exp (max C 1) ≤ (N : ℝ) / m :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hl1 : 1 ≤ Real.log ((N : ℝ) / m) := (le_max_right _ _).trans hlog
  have hl : 0 < Real.log ((N : ℝ) / m) := by linarith
  have hCsq : C ≤ Real.log ((N : ℝ) / m) ^ 2 := by
    have hCl := (le_max_left _ _).trans hlog
    nlinarith
  have herr := hx₀ ((N : ℝ) / m)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hlarge)) hx2
  have herr_le :
      C * ((N : ℝ) / m) / Real.log ((N : ℝ) / m) ^ 2 ≤ (N : ℝ) / m := by
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hCsq hx0]
  have hproxy : (N : ℝ) / m / Real.log ((N : ℝ) / m) ≤ (N : ℝ) / m :=
    div_le_self hx0 hl1
  have hnonneg : 0 ≤ goldbachB9PlusLiWeight N m :=
    (div_nonneg hx0 hl.le).trans (div_log_le_liuLogarithmicIntegral hx2)
  have hdiff := (le_abs_self
    (liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / m))).trans
      (herr.trans herr_le)
  unfold liuLogarithmicIntegralRemainder at hdiff
  refine ⟨hx2, hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg]
  unfold goldbachB9PlusLiWeight
  calc
    _ ≤ 2 * ((N : ℝ) / m) := by linarith
    _ = 2 * (N : ℝ) / m := by ring

theorem goldbachB9PlusMainMass_nonneg_eventually :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → 0 ≤ goldbachB9PlusMainMass N := by
  obtain ⟨N₀, hN₀, hw⟩ := goldbachB9PlusLiWeight_bounds_eventually
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  exact Finset.sum_nonneg (fun m hm => (hw N hN m hm).2.1)

/-- The real non-coprime gate is paid, not identified with zero.
The generic budget receives `T * N = 2 * N`. -/
theorem goldbachB9PlusLiWeight_sum_gateLoss_le_logCube :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, Q ≤ N →
      ∑ d ∈ Finset.Icc 1 Q,
        gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
          (goldbachB9PlusLiWeight N) d ≤
        (4 * 2 * (N : ℝ) / (N : ℝ) ^ (4 / 53 : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 3 := by
  obtain ⟨N₀, hN₀, hw⟩ := goldbachB9PlusLiWeight_bounds_eventually
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN Q hQ
  have hN4 : 4 ≤ N := hN₀.trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simpa only [mul_assoc] using
    (sum_gateLoss_le_logCube (T := 2 * (N : ℝ)) hQ (by omega)
      (Real.rpow_pos_of_pos hNpos _) (by positivity)
      (fun m hm => (hw N hN m hm).2.2))

private theorem B9MainGate_log_payment_eventually (U : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      1 ≤ Real.log (N : ℝ) ∧
        64 * Real.log (N : ℝ) ^ (U + 3) ≤ (N : ℝ) ^ (4 / 53 : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (U + 3) (by norm_num : (0 : ℝ) < 4 / 53)).bound
      (by norm_num : (0 : ℝ) < 1 / 64)
  have hsmall' : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (U + 3) ≤ (1 / 64 : ℝ) * x ^ (4 / 53 : ℝ) := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx0 : 0 ≤ x := by linarith
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlogx _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)] using hx
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hnat : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (N : ℝ) ∧
        64 * Real.log (N : ℝ) ^ (U + 3) ≤ (N : ℝ) ^ (4 / 53 : ℝ) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall', hlog] with N hs hl
    exact ⟨hl, by linarith⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hnat
  exact ⟨max 4 M, le_max_left _ _, fun N hN => hM N ((le_max_right _ _).trans hN)⟩

/-- Every real log exponent is absorbed, with fixed payment constant `C = 1`
and a threshold chosen before the modulus cutoff `Q`. -/
theorem goldbachB9PlusLiWeight_sum_gateLoss_log_saving_one (U : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, Q ≤ N →
      ∑ d ∈ Finset.Icc 1 Q,
        gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
          (goldbachB9PlusLiWeight N) d ≤ (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨N₁, hN₁, hcube⟩ := goldbachB9PlusLiWeight_sum_gateLoss_le_logCube
  obtain ⟨N₂, _hN₂, hpay⟩ := B9MainGate_log_payment_eventually U
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), ?_⟩
  intro N hN Q hQ
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN4 : 4 ≤ N := hN₁.trans hN₁'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < (N : ℝ) ^ (4 / 53 : ℝ) := Real.rpow_pos_of_pos hNpos _
  obtain ⟨hl1, hp⟩ := hpay N ((le_max_right _ _).trans hN)
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hUpos : 0 < Real.log (N : ℝ) ^ U := Real.rpow_pos_of_pos hl U
  have hlogcube : (1 + Real.log (N : ℝ)) ^ 3 ≤ 8 * Real.log (N : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * Real.log (N : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 3
      _ = _ := by ring
  have haux : 64 * Real.log (N : ℝ) ^ 3 ≤
      (N : ℝ) ^ (4 / 53 : ℝ) / Real.log (N : ℝ) ^ U := by
    apply (le_div_iff₀ hUpos).mpr
    calc
      64 * Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ U =
          64 * (Real.log (N : ℝ) ^ (3 : ℝ) * Real.log (N : ℝ) ^ U) := by
        rw [← Real.rpow_natCast]
        norm_num only [Nat.cast_ofNat]
        ring
      _ = 64 * Real.log (N : ℝ) ^ (U + 3) := by
        rw [← Real.rpow_add hl, add_comm (3 : ℝ) U]
      _ ≤ (N : ℝ) ^ (4 / 53 : ℝ) := hp
  calc
    _ ≤ (4 * 2 * (N : ℝ) / (N : ℝ) ^ (4 / 53 : ℝ)) *
        (1 + Real.log (N : ℝ)) ^ 3 := hcube N hN₁' Q hQ
    _ ≤ (4 * 2 * (N : ℝ) / (N : ℝ) ^ (4 / 53 : ℝ)) *
        (8 * Real.log (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hlogcube (by positivity)
    _ = ((N : ℝ) / (N : ℝ) ^ (4 / 53 : ℝ)) *
        (64 * Real.log (N : ℝ) ^ 3) := by ring
    _ ≤ ((N : ℝ) / (N : ℝ) ^ (4 / 53 : ℝ)) *
        ((N : ℝ) ^ (4 / 53 : ℝ) / Real.log (N : ℝ) ^ U) :=
      mul_le_mul_of_nonneg_left haux (by positivity)
    _ = (N : ℝ) / Real.log (N : ℝ) ^ U := by field_simp

theorem goldbachB9PlusLiWeight_sum_gateLoss_log_saving (U : ℝ) (_hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, Q ≤ N →
        ∑ d ∈ Finset.Icc 1 Q,
          gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
            (goldbachB9PlusLiWeight N) d ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  refine ⟨1, by norm_num, ?_⟩
  simpa only [one_mul] using goldbachB9PlusLiWeight_sum_gateLoss_log_saving_one U

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig