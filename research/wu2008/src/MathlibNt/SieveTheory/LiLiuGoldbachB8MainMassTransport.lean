import MathlibNt.SieveTheory.LiLiuGoldbachB8FibreSieve
import MathlibNt.SieveTheory.LiuWeightMainSum

open scoped BigOperators
open Filter Finset
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual finite prime-pair kernel; no integral limit is asserted. -/
noncomputable def goldbachB8PairLogKernel (N : ℕ) : ℝ :=
  ∑ rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ)),
    1 / ((goldbachC8Prod rs : ℝ) *
      (1 - Real.log (goldbachC8Prod rs : ℝ) / Real.log (N : ℝ)))

theorem goldbachB8PlusMainMass_eq_pair_sum (N : ℕ) :
    goldbachB8PlusMainMass N =
      ∑ rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ)),
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / goldbachC8Prod rs) := by
  unfold goldbachB8PlusMainMass goldbachC8ProductSupport
  exact Finset.sum_image (fun _ hx _ hy h => goldbachC8Prod_injOn hx hy h)

private theorem B8MainMassTransport_li_upper (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ m ∈ goldbachC8ProductSupport N,
      liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / m) ≤
        (1 + η) * ((N : ℝ) / m) / Real.log ((N : ℝ) / m) := by
  obtain ⟨C, _hC, hr⟩ := eventually_abs_liuLogarithmicIntegralRemainder_le (2 / Real.log 2)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hr
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (max x₀ (Real.exp (C / η)))))
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN m hm
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmp : (0 : ℝ) < m := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (goldbachC8ProductSupport_one_lt_and_coprime hm).1)
  have hmu := (goldbachC8ProductSupport_bounds (by omega) hm).2
  have hroot : (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) / m := by
    apply (le_div_iff₀ hmp).mpr
    calc
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hmu (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hx2 := goldbachC8ProductSupport_two_le_quotient hm
  have hl : 0 < Real.log ((N : ℝ) / m) := Real.log_pos (by linarith)
  have hlarge := (hM N ((le_max_right _ _).trans hN)).trans hroot
  have herr := hx₀ ((N : ℝ) / m) ((le_max_left _ _).trans hlarge) hx2
  have hlog : C / η ≤ Real.log ((N : ℝ) / m) := by
    have he := Real.log_le_log (Real.exp_pos (C / η)) ((le_max_right _ _).trans hlarge)
    simpa only [Real.log_exp] using he
  have hC : C ≤ η * Real.log ((N : ℝ) / m) := by
    have hh := (div_le_iff₀ hη).mp hlog
    nlinarith
  have he : C * ((N : ℝ) / m) / Real.log ((N : ℝ) / m)^2 ≤
      η * ((N : ℝ) / m) / Real.log ((N : ℝ) / m) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hl) hl).mpr
    have hh := mul_le_mul_of_nonneg_right hC (show 0 ≤ (N : ℝ) / m by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh hl.le
    nlinarith
  have hdiff := (le_abs_self (liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / m))).trans herr
  unfold liuLogarithmicIntegralRemainder at hdiff
  calc
    _ ≤ (N : ℝ) / m / Real.log ((N : ℝ) / m) +
        C * ((N : ℝ) / m) / Real.log ((N : ℝ) / m)^2 := by linarith
    _ ≤ (N : ℝ) / m / Real.log ((N : ℝ) / m) +
        η * ((N : ℝ) / m) / Real.log ((N : ℝ) / m) := by linarith
    _ = _ := by ring

/-- Uniform relative Li payment on the real C8 support, followed by exact
product-to-pair reindexing. The moving triangular prime-sum limit remains separate. -/
theorem goldbachB8PlusMainMass_le_pair_kernel (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB8PlusMainMass N ≤
        (1 + η) * ((N : ℝ) / Real.log (N : ℝ)) * goldbachB8PairLogKernel N := by
  obtain ⟨N₀, hN₀, hh⟩ := B8MainMassTransport_li_upper η hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := hN₀.trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [goldbachB8PlusMainMass_eq_pair_sum, goldbachB8PairLogKernel, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rs hrs
  have hm : goldbachC8Prod rs ∈ goldbachC8ProductSupport N := Finset.mem_image.mpr ⟨rs, hrs, rfl⟩
  have hmp : (0 : ℝ) < goldbachC8Prod rs := by exact_mod_cast goldbachC8Prod_pos hrs
  have hx2 := goldbachC8ProductSupport_two_le_quotient hm
  have hl : 0 < Real.log ((N : ℝ) / goldbachC8Prod rs) := Real.log_pos (by linarith)
  have hid : 1 - Real.log (goldbachC8Prod rs : ℝ) / Real.log (N : ℝ) =
      Real.log ((N : ℝ) / goldbachC8Prod rs) / Real.log (N : ℝ) := by
    rw [Real.log_div hNp.ne' hmp.ne']
    field_simp
  calc
    _ ≤ (1 + η) * ((N : ℝ) / goldbachC8Prod rs) /
        Real.log ((N : ℝ) / goldbachC8Prod rs) := hh N hN _ hm
    _ = _ := by rw [hid]; field_simp [hln.ne', hmp.ne', hl.ne']

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig