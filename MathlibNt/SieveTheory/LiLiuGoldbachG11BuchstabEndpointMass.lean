import MathlibNt.SieveTheory.LiLiuGoldbachG11CofactorWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductGeometry
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform

set_option autoImplicit false

open LiLiuPrereqBuchstab Set Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG11BuchstabMass (y q : ℝ) : ℝ :=
  y * buchstab (Real.log y / Real.log q) / Real.log q

theorem goldbachG11_buchstab_cutoff_identity {y q : ℝ}
    (hy : 1 < y) (hq : 1 < q) :
    q = y ^ (1 / (Real.log y / Real.log q)) := by
  have hly := Real.log_pos hy
  have hlq := Real.log_pos hq
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hy)]
  have he : Real.log y * (1 / (Real.log y / Real.log q)) = Real.log q := by
    field_simp
  rw [he, Real.exp_log (zero_lt_one.trans hq)]

theorem goldbachG11_buchstab_source_mass_identity {y q : ℝ}
    (hy : 1 < y) (hq : 1 < q) :
    (Real.log y / Real.log q) * buchstab (Real.log y / Real.log q) *
        y / Real.log y = goldbachG11BuchstabMass y q := by
  have hly := (Real.log_pos hy).ne'
  have hlq := (Real.log_pos hq).ne'
  unfold goldbachG11BuchstabMass
  field_simp

theorem goldbachG11_buchstab_mass_pos_le {y q : ℝ}
    (hy : 1 < y) (hq : 1 < q) (hu : 1 ≤ Real.log y / Real.log q) :
    0 < goldbachG11BuchstabMass y q ∧
      goldbachG11BuchstabMass y q ≤ y / Real.log q := by
  have hy0 := zero_lt_one.trans hy
  have hlq := Real.log_pos hq
  exact ⟨div_pos (mul_pos hy0 (buchstab_pos hu)) hlq,
    div_le_div_of_nonneg_right
      (mul_le_of_le_one_right hy0.le (buchstab_le_one hu)) hlq.le⟩

theorem goldbachG11_buchstab_relative_to_absolute {y q δ : ℝ}
    (hy : 1 < y) (hq : 1 < q) (hu : 1 ≤ Real.log y / Real.log q)
    (hδ : 0 < δ)
    (herr : |(roughCount y q : ℝ) / goldbachG11BuchstabMass y q - 1| < δ) :
    |(roughCount y q : ℝ) - goldbachG11BuchstabMass y q| ≤
      δ * y / Real.log q := by
  obtain ⟨hM, hMle⟩ := goldbachG11_buchstab_mass_pos_le hy hq hu
  have hid : (roughCount y q : ℝ) - goldbachG11BuchstabMass y q =
      ((roughCount y q : ℝ) / goldbachG11BuchstabMass y q - 1) *
        goldbachG11BuchstabMass y q := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hM]
  calc
    _ ≤ δ * goldbachG11BuchstabMass y q :=
      mul_le_mul_of_nonneg_right herr.le hM.le
    _ ≤ δ * (y / Real.log q) := mul_le_mul_of_nonneg_left hMle hδ.le
    _ = δ * y / Real.log q := (mul_div_assoc _ _ _).symm

theorem goldbachG11_canonical_cofactor_lower_bound
    {N : ℕ} {v : GoldbachG11Label} (hN : 2 ≤ N)
    (hv : v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ))) :
    (N : ℝ)^(17 / 33 : ℝ) ≤ (N : ℝ) / goldbachG11LabelProd v := by
  have hdR : (0 : ℝ) < goldbachG11LabelProd v := by
    exact_mod_cast goldbachG11LabelProd_pos hv
  rcases v with ⟨t, s, r, q⟩
  have hmem : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ))
        ((N : ℝ)^(4 / 33 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (t : ℝ) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG11Labels, Finset.mem_sigma] using hv
  obtain ⟨ht, hs, hr, hq⟩ := hmem
  have hp := (goldbachG11_canonical_product_bounds hN ht hs hr hq).1
  have hNp : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  apply (le_div_iff₀ hdR).mpr
  calc
    _ ≤ (N : ℝ)^(17 / 33 : ℝ) * (N : ℝ)^(16 / 33 : ℝ) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hNp.le _)
    _ = N := by rw [← Real.rpow_add hNp]; norm_num


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig