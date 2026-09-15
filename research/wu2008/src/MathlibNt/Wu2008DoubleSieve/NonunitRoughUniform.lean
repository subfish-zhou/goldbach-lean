import MathlibNt.Wu2008DoubleSieve.NonunitRoughUniformCore

open Finset Real Filter LiLiuPrereqBuchstab

namespace Wu2008DoubleSieve.NonunitRoughUniform

/-- The fixed-cap relative theorem is used only away from the transition. -/
theorem exists_large_upper (M : ℕ) (hM : 2 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : ℝ, 1 < Z ∧ ∀ x ≥ Z, ∀ y : ℝ, 1 < y → y ≤ x →
      (3 : ℝ) / 2 ≤ log x / log y → log x / log y ≤ M →
      (count x y : ℝ) ≤ (buchstab (log x / log y) + ε) * x / log y := by
  obtain ⟨Z, hZ, hbound⟩ := roughCount_uniform_buchstab_fixed M hM
    (u₀ := (3 : ℝ) / 2) (by norm_num) hε
  refine ⟨Z, hZ, ?_⟩
  intro x hx y hy hxy hu0 huM
  let u := log x / log y
  let B := u * buchstab u * x / log x
  have hux : 1 ≤ u := log_ratio_ge_one hy hxy
  have hx1 : 1 < x := hy.trans_le hxy
  have hly := log_pos hy
  have hlx := log_pos hx1
  obtain ⟨hB, herr⟩ := hbound x hx u ⟨hu0, huM⟩
  rw [rpow_inv_log_ratio hy hxy] at herr
  change 0 < B at hB
  change |(roughCount x y : ℝ) / B - 1| < ε at herr
  have hr : (roughCount x y : ℝ) < (1 + ε) * B := by
    apply (div_lt_iff₀ hB).mp
    have hh := lt_of_le_of_lt (le_abs_self ((roughCount x y : ℝ) / B - 1)) herr
    linarith
  have hBid : B = buchstab u * x / log y := by
    dsimp [B, u]
    field_simp
  have hBmax : B ≤ x / log y := by
    rw [hBid]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (by linarith : 0 ≤ x) (buchstab_le_one hux)) hly.le
  have hc : (count x y : ℝ) ≤ (roughCount x y : ℝ) :=
    (Nat.cast_le (α := ℝ)).mpr (count_le_roughCount x y)
  calc
    (count x y : ℝ) ≤ (roughCount x y : ℝ) := hc
    _ ≤ B + ε * B := by nlinarith [hr]
    _ ≤ B + ε * (x / log y) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hBmax hε.le)
    _ = (buchstab (log x / log y) + ε) * x / log y := by rw [hBid]; ring

/-- The global size assumptions bound the logarithmic coordinate without a gap at one. -/
theorem log_ratio_le_inv {η R x y : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hy : 1 < y) (hxy : y ≤ x) (hxR : x ≤ R) (hRy : R ^ η ≤ y) :
    log x / log y ≤ 1 / η := by
  have hlogx : log x ≤ log R := log_le_log (by linarith) hxR
  have hlogy := log_le_log (rpow_pos_of_pos hR η) hRy
  rw [log_rpow hR] at hlogy
  apply (div_le_div_iff₀ (log_pos hy) hη).mpr
  nlinarith

/-- Uniform one-sided Buchstab bound for the literal nonunit rough count.
The threshold precedes all `N`, `x`, and `y`; `x = y` is included. -/
theorem uniform_upper {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ x y : ℝ,
      x ≤ (N : ℝ) → (N : ℝ) ^ η ≤ y →
      (x < y → ((roughNumbers x y).erase 1).card = 0) ∧
      (y ≤ x → (((roughNumbers x y).erase 1).card : ℝ) ≤
        (buchstab (log x / log y) + τ) * x / log y) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max (2 : ℝ) (1 / η))
  have hM2 : 2 ≤ M := by exact_mod_cast (le_trans (le_max_left _ _) hM)
  have hMeta : 1 / η ≤ (M : ℝ) := le_trans (le_max_right _ _) hM
  obtain ⟨Zp, hZp, hp⟩ := exists_primePi_upper hτ
  obtain ⟨Zb, hZb, hb⟩ := exists_large_upper M hM2 hτ
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (max Zp Zb))
  refine ⟨max 4 T₀, le_max_left _ _, ?_⟩
  intro N hN x y hxN hyN
  have hNT : T₀ ≤ N := le_trans (le_max_right _ _) hN
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hZy : max Zp Zb ≤ y := (hT₀ N hNT).trans hyN
  have hpY : Zp ≤ y := (le_max_left _ _).trans hZy
  have hbY : Zb ≤ y := (le_max_right _ _).trans hZy
  have hy : 1 < y := hZp.trans_le hpY
  constructor
  · intro hxy
    exact count_eq_zero hy.le hxy
  · intro hxy
    change (count x y : ℝ) ≤ _
    by_cases hu : log x / log y ≤ (3 : ℝ) / 2
    · exact small_upper hτ hy hxy hu (hp x (hpY.trans hxy))
    · apply hb x (hbY.trans hxy) y hy hxy (le_of_not_ge hu)
      exact (log_ratio_le_inv hη hNpos hy hxy hxN hyN).trans hMeta

end Wu2008DoubleSieve.NonunitRoughUniform
