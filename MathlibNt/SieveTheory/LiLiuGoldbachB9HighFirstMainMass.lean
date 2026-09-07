import MathlibNt.SieveTheory.LiLiuGoldbachS5HighFirstFinite
import MathlibNt.SieveTheory.LiLiuGoldbachB9MainGate

open scoped BigOperators
open Finset Filter
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachB9HighFirstSupport (N : ℕ) : Finset ℕ :=
  goldbachC10ProductSupport N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))

/-- The genuine high zero-prefix mass: Li0(N/m), without subtracting Li0(0). -/
noncomputable def goldbachX9High (N : ℕ) : ℝ :=
  ∑ m ∈ goldbachB9HighFirstSupport N, goldbachB9PlusLiWeight N m

noncomputable def goldbachK9High (N : ℕ) : ℝ :=
  ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)),
    1 / ((goldbachC10Prod rs : ℝ) *
      (1 - Real.log (goldbachC10Prod rs : ℝ) / Real.log (N : ℝ)))

theorem goldbachB9HighFirstSupport_subset (N : ℕ) (hN : 2 ≤ N) :
    goldbachB9HighFirstSupport N ⊆
      goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  classical
  unfold goldbachB9HighFirstSupport goldbachC10ProductSupport
  rw [goldbachC10HighFirstPairs_eq_filter N hN, ← goldbachC9Pairs_eq_C10Pairs]
  exact image_subset_image (filter_subset _ _)

theorem goldbachX9High_eq_pair_sum (N : ℕ) :
    goldbachX9High N =
      ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)),
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / goldbachC10Prod rs) := by
  unfold goldbachX9High goldbachB9HighFirstSupport goldbachC10ProductSupport
    goldbachB9PlusLiWeight
  exact sum_image (fun _ hx _ hy h => goldbachC10Prod_injOn hx hy h)

theorem goldbachK9High_eq_support_sum (N : ℕ) :
    goldbachK9High N =
      ∑ m ∈ goldbachB9HighFirstSupport N,
        1 / ((m : ℝ) * (1 - Real.log (m : ℝ) / Real.log (N : ℝ))) := by
  unfold goldbachK9High goldbachB9HighFirstSupport goldbachC10ProductSupport
  symm
  exact sum_image (fun _ hx _ hy h => goldbachC10Prod_injOn hx hy h)

theorem goldbachB9HighFirstLiWeight_bounds_eventually :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ m ∈ goldbachB9HighFirstSupport N,
        2 ≤ (N : ℝ) / m ∧ 0 ≤ goldbachB9PlusLiWeight N m ∧
          |goldbachB9PlusLiWeight N m| ≤ 2 * (N : ℝ) / m := by
  obtain ⟨N₀, hN₀, hw⟩ := goldbachB9PlusLiWeight_bounds_eventually
  exact ⟨N₀, hN₀, fun N hN m hm =>
    hw N hN m (goldbachB9HighFirstSupport_subset N (by omega) hm)⟩

theorem goldbachX9High_nonneg_eventually :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → 0 ≤ goldbachX9High N := by
  obtain ⟨N₀, hN₀, hw⟩ := goldbachB9HighFirstLiWeight_bounds_eventually
  exact ⟨N₀, hN₀, fun N hN => sum_nonneg (fun m hm => (hw N hN m hm).2.1)⟩

/-- Positivity is established before comparing the two absolute gate losses. -/
theorem goldbachB9HighFirst_gate_le_full (N : ℕ) (hN : 2 ≤ N)
    (hw : ∀ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)), 0 ≤ goldbachB9PlusLiWeight N m) (d : ℕ) :
    gateLoss N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
      (goldbachB9PlusLiWeight N) d ≤
    gateLoss N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
      (goldbachB9PlusLiWeight N) d := by
  classical
  have hsub := goldbachB9HighFirstSupport_subset N hN
  have hlo : 0 ≤ ∑ m ∈ goldbachB9HighFirstSupport N with ¬Nat.Coprime m d,
      goldbachB9PlusLiWeight N m :=
    sum_nonneg (fun m hm => hw m (hsub (mem_filter.mp hm).1))
  have hhi : 0 ≤ ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) with ¬Nat.Coprime m d, goldbachB9PlusLiWeight N m :=
    sum_nonneg (fun m hm => hw m (mem_filter.mp hm).1)
  unfold gateLoss
  dsimp only [goldbachB9HighFirstSupport] at hlo hsub
  rw [abs_of_nonneg (mul_nonneg (by positivity) hlo),
    abs_of_nonneg (mul_nonneg (by positivity) hhi)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hsub)
    (fun m hm _ => hw m (mem_filter.mp hm).1)

theorem goldbachB9HighFirst_gate_log_saving (U : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, Q ≤ N →
      ∑ d ∈ Icc 1 Q, gateLoss N ((N : ℝ) ^ (1 / 10 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) (goldbachB9PlusLiWeight N) d ≤
          (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨Ng, hNg, hg⟩ := goldbachB9PlusLiWeight_sum_gateLoss_log_saving_one U
  obtain ⟨Nw, _hNw, hw⟩ := goldbachB9PlusLiWeight_bounds_eventually
  refine ⟨max Ng Nw, hNg.trans (le_max_left _ _), ?_⟩
  intro N hN Q hQ
  have hgN : Ng ≤ N := (le_max_left _ _).trans hN
  have hwN : Nw ≤ N := (le_max_right _ _).trans hN
  exact (sum_le_sum (fun d _ => goldbachB9HighFirst_gate_le_full N (by omega)
    (fun m hm => (hw N hwN m hm).2.1) d)).trans (hg N hgN Q hQ)

private theorem highFirst_log_geometry {N m : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachB9HighFirstSupport N) :
    0 < (m : ℝ) ∧ 0 < Real.log ((N : ℝ) / m) ∧
      0 < 1 - Real.log (m : ℝ) / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hmp, _, hroot⟩ :=
    goldbachB9ProductSupport_bounds hN (goldbachB9HighFirstSupport_subset N hN hm)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hmp
  have hroot1 : (1 : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_lt_rpow hN1 (by norm_num)
  have hl := Real.log_pos (hroot1.trans_le hroot)
  have heq : 1 - Real.log (m : ℝ) / Real.log (N : ℝ) =
      Real.log ((N : ℝ) / m) / Real.log (N : ℝ) := by
    rw [Real.log_div hNpos.ne' hmpos.ne', sub_div,
      div_self (Real.log_pos hN1).ne']
  exact ⟨hmpos, hl, heq ▸ div_pos hl (Real.log_pos hN1)⟩

theorem goldbachK9High_nonneg (N : ℕ) (hN : 2 ≤ N) : 0 ≤ goldbachK9High N := by
  rw [goldbachK9High_eq_support_sum]
  apply sum_nonneg
  intro m hm
  obtain ⟨hmpos, _, hden⟩ := highFirst_log_geometry hN hm
  exact (div_pos zero_lt_one (mul_pos hmpos hden)).le

theorem goldbachB9HighFirst_proxy_eq (N : ℕ) (hN : 2 ≤ N) :
    (∑ m ∈ goldbachB9HighFirstSupport N,
      ((N : ℝ) / m) / Real.log ((N : ℝ) / m)) =
        (N : ℝ) / Real.log (N : ℝ) * goldbachK9High N := by
  rw [goldbachK9High_eq_support_sum, mul_sum]
  apply sum_congr rfl
  intro m hm
  obtain ⟨hmpos, hl, hd⟩ := highFirst_log_geometry hN hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have heq : 1 - Real.log (m : ℝ) / Real.log (N : ℝ) =
      Real.log ((N : ℝ) / m) / Real.log (N : ℝ) := by
    rw [Real.log_div hNpos.ne' hmpos.ne', sub_div, div_self hlogN.ne']
  rw [heq]
  field_simp

private theorem highFirst_Li_relative (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ x : ℝ in atTop,
      liuLogarithmicIntegral (2 / Real.log 2) x ≤ (1 + τ) * (x / Real.log x) := by
  obtain ⟨C, _hC, hr⟩ := eventually_abs_liuLogarithmicIntegralRemainder_le (2 / Real.log 2)
  filter_upwards [hr, eventually_ge_atTop (max 2 (Real.exp (C / τ)))] with x hx hlarge
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hlarge
  have hxpos : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hCl : C ≤ τ * Real.log x := by
    have he : Real.exp (C / τ) ≤ x := (le_max_right _ _).trans hlarge
    have hh : C / τ ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
    simpa [mul_comm] using (div_le_iff₀ hτ).mp hh
  have herr : C * x / Real.log x ^ 2 ≤ τ * (x / Real.log x) := by
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    calc
      C * x ≤ (τ * Real.log x) * x := mul_le_mul_of_nonneg_right hCl hxpos.le
      _ = _ := by field_simp
  have hb := (le_abs_self (liuLogarithmicIntegralRemainder (2 / Real.log 2) x)).trans
    ((hx hx2).trans herr)
  unfold liuLogarithmicIntegralRemainder at hb
  nlinarith

theorem goldbachX9High_le_kernel_eventually (τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachX9High N ≤
        (1 + τ) * ((N : ℝ) / Real.log (N : ℝ)) * goldbachK9High N := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (highFirst_Li_relative τ hτ)
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop x₀))
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  calc
    goldbachX9High N ≤ ∑ m ∈ goldbachB9HighFirstSupport N,
        (1 + τ) * (((N : ℝ) / m) / Real.log ((N : ℝ) / m)) := by
      apply sum_le_sum
      intro m hm
      exact hx₀ _ ((hM N ((le_max_right _ _).trans hN)).trans
        (goldbachB9ProductSupport_bounds hN2
          (goldbachB9HighFirstSupport_subset N hN2 hm)).2.2)
    _ = _ := by rw [← mul_sum, goldbachB9HighFirst_proxy_eq N hN2]; ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig