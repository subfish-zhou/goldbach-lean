import MathlibNt.SieveTheory.LiLiuGoldbachB9MainGate

open scoped BigOperators
open Filter Finset
open MathlibNt.SieveTheory.LiuWeight
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual closed C10 kernel for S5, not the former C8 triangle. -/
noncomputable def goldbachB9PairLogKernel (N : ℕ) : ℝ :=
  ∑ rs ∈ goldbachC10Pairs N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)),
    1 / ((goldbachC10Prod rs : ℝ) *
      (1 - Real.log (goldbachC10Prod rs : ℝ) / Real.log (N : ℝ)))

private theorem B9MainMassTransport_li_upper (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ m ∈ goldbachC10ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)),
        2 ≤ (N : ℝ) / m ∧
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / m) ≤
          (1 + η) * ((N : ℝ) / m) / Real.log ((N : ℝ) / m) := by
  obtain ⟨C, _hC, hr⟩ := eventually_abs_liuLogarithmicIntegralRemainder_le (2 / Real.log 2)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hr
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (max 2 (max x₀ (Real.exp (C / η))))))
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN m hm
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hroot := (goldbachB9ProductSupport_bounds (by omega) hm).2.2
  have hlarge := (hM N ((le_max_right _ _).trans hN)).trans hroot
  have hx2 : 2 ≤ (N : ℝ) / m := (le_max_left _ _).trans hlarge
  have hl : 0 < Real.log ((N : ℝ) / m) := Real.log_pos (by linarith)
  have herr := hx₀ ((N : ℝ) / m)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hlarge)) hx2
  have hlog : C / η ≤ Real.log ((N : ℝ) / m) := by
    have he := Real.log_le_log (Real.exp_pos (C / η))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
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
  have hdiff := (le_abs_self (liuLogarithmicIntegralRemainder (2 / Real.log 2)
    ((N : ℝ) / m))).trans herr
  unfold liuLogarithmicIntegralRemainder at hdiff
  refine ⟨hx2, ?_⟩
  calc
    _ ≤ (N : ℝ) / m / Real.log ((N : ℝ) / m) +
        C * ((N : ℝ) / m) / Real.log ((N : ℝ) / m)^2 := by linarith
    _ ≤ (N : ℝ) / m / Real.log ((N : ℝ) / m) +
        η * ((N : ℝ) / m) / Real.log ((N : ℝ) / m) := by linarith
    _ = _ := by ring

/-- Relative full-prefix Li bound summed on the actual pair support.
The prime-sum integral limit and low-first-prime improved coefficient are separate. -/
theorem goldbachB9PlusMainMass_le_pair_kernel (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB9PlusMainMass N ≤
        (1 + η) * ((N : ℝ) / Real.log (N : ℝ)) * goldbachB9PairLogKernel N := by
  obtain ⟨N₀, hN₀, hh⟩ := B9MainMassTransport_li_upper η hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := hN₀.trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [goldbachB9PlusMainMass_eq_pair_sum, goldbachB9PairLogKernel, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rs hrs
  have hm : goldbachC10Prod rs ∈ goldbachC10ProductSupport N
      ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)) := Finset.mem_image.mpr ⟨rs, hrs, rfl⟩
  have hmp : (0 : ℝ) < goldbachC10Prod rs := by exact_mod_cast goldbachC10ProductSupport_pos hm
  have hx2 := (hh N hN _ hm).1
  have hl : 0 < Real.log ((N : ℝ) / goldbachC10Prod rs) := Real.log_pos (by linarith)
  have hid : 1 - Real.log (goldbachC10Prod rs : ℝ) / Real.log (N : ℝ) =
      Real.log ((N : ℝ) / goldbachC10Prod rs) / Real.log (N : ℝ) := by
    rw [Real.log_div hNp.ne' hmp.ne']
    field_simp
  calc
    _ ≤ (1 + η) * ((N : ℝ) / goldbachC10Prod rs) /
        Real.log ((N : ℝ) / goldbachC10Prod rs) := (hh N hN _ hm).2
    _ = _ := by rw [hid]; field_simp [hln.ne', hmp.ne', hl.ne']

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig