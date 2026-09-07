import MathlibNt.SieveTheory.LiLiuGoldbachB10LiKernel

open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachB10MainLogProductSum (N : ℕ) (b c : ℝ) : ℝ :=
  ∑ m ∈ goldbachC10ProductSupport N b c,
    1 / ((m : ℝ) * (1 - Real.log (m : ℝ) / Real.log (N : ℝ)))

private theorem B10MainMass_product_bounds {N m : ℕ} {b γ : ℝ}
    (hN : 2 ≤ N) (hγ : γ < (1 : ℝ) / 3)
    (hm : m ∈ goldbachC10ProductSupport N b ((N : ℝ) ^ γ)) :
    0 < m ∧ (m : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
  rcases mem_goldbachC10ProductSupport_iff.mp hm with ⟨rs, hrs, rfl⟩
  have hp := mem_goldbachC10Pairs_iff.mp hrs
  have hc := goldbachC10Prod_le_rpow_half_and_lt_two_thirds hN hγ hrs
  exact ⟨Nat.mul_pos hp.1.pos hp.2.1.pos, hc.1.trans hc.2.le⟩

private theorem B10MainMass_log_den_pos {N m : ℕ}
    (hN : 2 ≤ N) (hm : 0 < m) (hbound : (m : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3)) :
    0 < 1 - Real.log (m : ℝ) / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmlt : (m : ℝ) < N := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt hN1 (show (2 : ℝ) / 3 < 1 by norm_num)
    exact hbound.trans_lt (by simpa only [Real.rpow_one] using hh)
  exact sub_pos.mpr ((div_lt_one (Real.log_pos hN1)).mpr (Real.log_lt_log hmpos hmlt))

theorem goldbachB10MainLogProductSum_nonneg {N : ℕ} {b γ : ℝ}
    (hN : 2 ≤ N) (hγ : γ < (1 : ℝ) / 3) :
    0 ≤ goldbachB10MainLogProductSum N b ((N : ℝ) ^ γ) := by
  apply Finset.sum_nonneg
  intro m hm
  have hh := B10MainMass_product_bounds hN hγ hm
  have hd := B10MainMass_log_den_pos hN hh.1 hh.2
  positivity

private theorem B10MainMass_log_kernel_identity {N m : ℕ}
    (hN : 2 ≤ N) (hm : 0 < m) (hbound : (m : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3)) :
    ((N : ℝ) / m) / Real.log ((N : ℝ) / m) =
      ((N : ℝ) / Real.log (N : ℝ)) *
        (1 / ((m : ℝ) * (1 - Real.log (m : ℝ) / Real.log (N : ℝ)))) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog := Real.log_pos hN1
  have hd := B10MainMass_log_den_pos hN hm hbound
  have hdiff : 0 < Real.log (N : ℝ) - Real.log (m : ℝ) := by
    have hh := (div_lt_one hlog).mp (sub_pos.mp hd)
    linarith
  rw [Real.log_div hNpos.ne' hmpos.ne']
  field_simp [hlog.ne', hd.ne', hdiff.ne', hmpos.ne']

theorem goldbachB10ContinuousMainMass_le_logProductSum
    (ε γ η : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ b : ℝ,
      goldbachB10ContinuousMainMass N ε b ((N : ℝ) ^ γ) ≤
        (1 - ε + η) * ((N : ℝ) / Real.log (N : ℝ)) *
          goldbachB10MainLogProductSum N b ((N : ℝ) ^ γ) := by
  obtain ⟨N₀, hN₀, hw⟩ := goldbachB10ContinuousMainWeight_relative_upper ε η hε hεlt hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN b
  have hN2 := hN₀.trans hN
  unfold goldbachB10ContinuousMainMass goldbachB10MainLogProductSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hh := B10MainMass_product_bounds hN2 hγ hm
  have h := hw N hN m hh.1 hh.2
  calc
    _ ≤ (1 - ε + η) * (((N : ℝ) / m) / Real.log ((N : ℝ) / m)) := by
      simpa only [mul_div_assoc] using h
    _ = _ := by rw [B10MainMass_log_kernel_identity hN2 hh.1 hh.2]; ring

theorem goldbachB10MainMass_le_logProductSum
    (ε γ η τ : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3)
    (hη : 0 < η) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ, (1 : ℝ) / 18 < β →
      goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≤
        ((1 - ε + η) * goldbachB10MainLogProductSum N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) + τ) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨Nc, hNc, hc⟩ := goldbachB10ContinuousMainMass_le_logProductSum ε γ η hε hεlt hγ hη
  obtain ⟨Nf, _hNf, hf⟩ := goldbachB10MainMass_floor_payment_mainScale ε γ τ hε hεlt hγ hτ
  refine ⟨max Nc Nf, hNc.trans (le_max_left _ _), ?_⟩
  intro N hN β hβ
  have hcont := hc N ((le_max_left _ _).trans hN) ((N : ℝ) ^ β)
  have hfloor := (hf N ((le_max_right _ _).trans hN) β hβ).2
  rw [mul_div_assoc] at hfloor
  calc
    _ ≤ goldbachB10ContinuousMainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) +
        τ * ((N : ℝ) / Real.log (N : ℝ)) := by linarith only [hfloor]
    _ ≤ (1 - ε + η) * ((N : ℝ) / Real.log (N : ℝ)) *
        goldbachB10MainLogProductSum N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) +
        τ * ((N : ℝ) / Real.log (N : ℝ)) := add_le_add hcont le_rfl
    _ = _ := by ring

/-- Reindexing preserves the actual prime-pair carrier, including repeated factors and closed endpoints. -/
theorem goldbachB10MainLogProductSum_eq_pair_sum (N : ℕ) (b c : ℝ) :
    goldbachB10MainLogProductSum N b c =
      ∑ rs ∈ goldbachC10Pairs N b c,
        1 / ((rs.1 : ℝ) * (rs.2 : ℝ) *
          (1 - Real.log (rs.1 : ℝ) / Real.log (N : ℝ) -
            Real.log (rs.2 : ℝ) / Real.log (N : ℝ))) := by
  classical
  unfold goldbachB10MainLogProductSum goldbachC10ProductSupport
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro rs hrs
    have hp := mem_goldbachC10Pairs_iff.mp hrs
    have hr : (rs.1 : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
    have hs : (rs.2 : ℝ) ≠ 0 := by exact_mod_cast hp.2.1.ne_zero
    simp only [goldbachC10Prod, Nat.cast_mul]
    rw [Real.log_mul hr hs, add_div]
    congr 1
    ring
  · intro rs hrs tu htu hEq
    exact goldbachC10Prod_injOn hrs htu hEq

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig