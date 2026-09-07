import MathlibNt.SieveTheory.LiLiuGoldbachG11SwitchedMother

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Bounds for an actually inhabited first-prime fibre, not for the entire mother support. -/
theorem goldbachG11_active_product_bounds {N r : ℕ} {ε : ℝ}
    {u : GoldbachG11SwitchedBody} (hN : 2 ≤ N)
    (hu : u ∈ goldbachG11SwitchedBodies N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)))
    (hr : r ∈ goldbachG11FirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) u) :
    ε * (N : ℝ)^(29 / 33 : ℝ) < (goldbachG11SwitchedBodyProd u : ℝ) ∧
      (goldbachG11SwitchedBodyProd u : ℝ) < (N : ℝ)^(49 / 53 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB : (0 : ℝ) < goldbachG11SwitchedBodyProd u := by
    exact_mod_cast goldbachG11SwitchedBodyProd_pos hu
  obtain ⟨_, _, hzr, hrq, hlo, hhi, _⟩ := mem_goldbachG11FirstPrimeFiber_iff.mp hr
  rcases u with ⟨t, s, q, k⟩
  obtain ⟨_, _, _, _, _, hqs, hst, htb, _⟩ := mem_goldbachG11SwitchedBodies_iff.mp hu
  have hrb : (r : ℝ) ≤ (N : ℝ)^(4 / 33 : ℝ) :=
    (show (r : ℝ) ≤ t by exact_mod_cast hrq.trans (hqs.trans hst)).trans htb
  have hloR : ε * (N : ℝ) < (r : ℝ) * (goldbachG11SwitchedBodyProd ⟨t, s, q, k⟩ : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (r : ℝ) * (goldbachG11SwitchedBodyProd ⟨t, s, q, k⟩ : ℝ) < N := by
    exact_mod_cast hhi
  have hlow := hloR.trans_le (mul_le_mul_of_nonneg_right hrb hB.le)
  have hupp := (mul_le_mul_of_nonneg_right hzr hB.le).trans_lt hhiR
  have hl : ε * (N : ℝ) / (N : ℝ)^(4 / 33 : ℝ) <
      (goldbachG11SwitchedBodyProd ⟨t, s, q, k⟩ : ℝ) :=
    (div_lt_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr (by simpa only [mul_comm] using hlow)
  have hh : (goldbachG11SwitchedBodyProd ⟨t, s, q, k⟩ : ℝ) <
      (N : ℝ) / (N : ℝ)^(4 / 53 : ℝ) :=
    (lt_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr (by simpa only [mul_comm] using hupp)
  have e1 : (N : ℝ) / (N : ℝ)^(4 / 33 : ℝ) = (N : ℝ)^(29 / 33 : ℝ) := by
    rw [show (29 / 33 : ℝ) = 1 - 4 / 33 by norm_num, Real.rpow_sub hNp, Real.rpow_one]
  have e2 : (N : ℝ) / (N : ℝ)^(4 / 53 : ℝ) = (N : ℝ)^(49 / 53 : ℝ) := by
    rw [show (49 / 53 : ℝ) = 1 - 4 / 53 by norm_num, Real.rpow_sub hNp, Real.rpow_one]
  rw [mul_div_assoc, e1] at hl
  rw [e2] at hh
  exact ⟨hl, hh⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig