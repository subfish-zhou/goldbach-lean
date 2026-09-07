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

/-- One source threshold, chosen before every canonical label, serves both endpoints.
Each endpoint uses half the requested final window tolerance. -/
theorem goldbachG11_buchstab_endpoints
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
        let x := (N : ℝ) / goldbachG11LabelProd v
        let l := ε * x
        let q : ℝ := v.2.2.2
        1 < l ∧ l ≤ x ∧ 0 < Real.log q ∧
          0 < goldbachG11BuchstabMass x q ∧
          |(roughCount x q : ℝ) - goldbachG11BuchstabMass x q| ≤ (η / 2) * x / Real.log q ∧
          0 < goldbachG11BuchstabMass l q ∧
          |(roughCount l q : ℝ) - goldbachG11BuchstabMass l q| ≤ (η / 2) * l / Real.log q := by
  have hhalf : 0 < η / 2 := half_pos hη
  obtain ⟨X, hX1, hsource⟩ :=
    roughCount_uniform_buchstab (u₀ := 4) (by norm_num) hhalf
  obtain ⟨G, hG4, hgeometry⟩ := goldbachG11_positivePrefix_logQuotient_bounds ε hε hε1
  have hgrowth := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 17 / 33)).eventually
    (eventually_ge_atTop (X / ε))
  obtain ⟨A, hA⟩ := eventually_atTop.mp hgrowth
  obtain ⟨K, hK⟩ := exists_nat_gt (max A (4 : ℝ))
  refine ⟨max G K, hG4.trans (le_max_left _ _), ?_⟩
  intro N hN v hv
  have hNG : G ≤ N := (le_max_left _ _).trans hN
  have hNK : K ≤ N := (le_max_right _ _).trans hN
  have hN4 := hG4.trans hNG
  have hNA : A ≤ (N : ℝ) :=
    ((le_max_left _ _).trans hK.le).trans (by exact_mod_cast hNK)
  have hscale : X / ε ≤ (N : ℝ)^(17 / 33 : ℝ) := hA _ hNA
  have hN2 : 2 ≤ N := (by decide : 2 ≤ 4).trans hN4
  have hprod := goldbachG11_canonical_cofactor_lower_bound hN2 hv
  have hprefix : ε * (N : ℝ)^(17 / 33 : ℝ) ≤
      ε * ((N : ℝ) / goldbachG11LabelProd v) :=
    mul_le_mul_of_nonneg_left hprod hε.le
  have hXl : X ≤ ε * ((N : ℝ) / goldbachG11LabelProd v) := by
    have hXscale : X ≤ ε * (N : ℝ)^(17 / 33 : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hε).mp hscale
    exact hXscale.trans hprefix
  have hx0 : 0 ≤ (N : ℝ) / goldbachG11LabelProd v :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hlx := mul_le_of_le_one_left hx0 hε1
  have hl1 := hX1.trans_le hXl
  have hul := hgeometry N hNG v hv
  rw [mul_div_assoc] at hul
  rcases v with ⟨t, s, r, q⟩
  have hqprime := (mem_goldbachG11Labels_iff.mp hv).2.1
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hqprime.one_lt
  have hmem : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ))
        ((N : ℝ)^(4 / 33 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (t : ℝ) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG11Labels, Finset.mem_sigma] using hv
  obtain ⟨ht, hs, hr, hq⟩ := hmem
  have hux := goldbachG11_canonical_logQuotient_bounds hN2 ht hs hr hq
  have consume : ∀ y : ℝ, X ≤ y → Real.log y / Real.log (q : ℝ) ∈ Icc (4 : ℝ) 100 →
      0 < goldbachG11BuchstabMass y q ∧
        |(roughCount y q : ℝ) - goldbachG11BuchstabMass y q| ≤
          (η / 2) * y / Real.log (q : ℝ) := by
    intro y hy hu
    have hy1 := hX1.trans_le hy
    have hs := hsource y hy (Real.log y / Real.log (q : ℝ)) hu
    rw [← goldbachG11_buchstab_cutoff_identity hy1 hq1,
      goldbachG11_buchstab_source_mass_identity hy1 hq1] at hs
    exact ⟨hs.1, goldbachG11_buchstab_relative_to_absolute hy1 hq1
      ((by norm_num : (1 : ℝ) ≤ 4).trans hu.1) hhalf hs.2⟩
  have hx := consume _ (hXl.trans hlx)
    ⟨(by norm_num : (4 : ℝ) ≤ 17 / 4).trans hux.1, hux.2.trans (by norm_num)⟩
  have hl := consume _ hXl ⟨hul.1, hul.2.trans (by norm_num)⟩
  exact ⟨hl1, hlx, Real.log_pos hq1, hx.1, hx.2, hl.1, hl.2⟩

/-- Absolute, not relative, window error: at epsilon one both the window and
the difference of the two masses vanish. No output-prime counting is asserted. -/
theorem goldbachG11CofactorWindow_buchstab_mass
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ goldbachG11Labels N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)),
        let x := (N : ℝ) / goldbachG11LabelProd v
        let l := ε * x
        let q : ℝ := v.2.2.2
        |((goldbachG11CofactorWindow N ε v).card : ℝ) -
          (goldbachG11BuchstabMass x q - goldbachG11BuchstabMass l q)| ≤
            η * x / Real.log q := by
  obtain ⟨N₀, hN₀, hend⟩ := goldbachG11_buchstab_endpoints ε hε hε1 η hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN v hv
  obtain ⟨_, hlx, hlq, _, hx, _, hl⟩ := hend N hN v hv
  dsimp only
  rw [goldbachG11CofactorWindow_card_real N ⟨hε.le, hε1⟩ v]
  have hid : ∀ a b c d : ℝ, a - b - (c - d) = (a - c) - (b - d) := by
    intros
    ring
  rw [hid]
  calc
    _ ≤ |(roughCount ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 : ℝ) -
          goldbachG11BuchstabMass ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2| +
        |(roughCount (ε * ((N : ℝ) / goldbachG11LabelProd v)) v.2.2.2 : ℝ) -
          goldbachG11BuchstabMass (ε * ((N : ℝ) / goldbachG11LabelProd v)) v.2.2.2| :=
      abs_sub _ _
    _ ≤ (η / 2) * ((N : ℝ) / goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ) +
        (η / 2) * (ε * ((N : ℝ) / goldbachG11LabelProd v)) / Real.log (v.2.2.2 : ℝ) :=
      add_le_add hx hl
    _ ≤ (η / 2) * ((N : ℝ) / goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ) +
        (η / 2) * ((N : ℝ) / goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlx (half_pos hη).le) hlq.le)
    _ = _ := by ring

theorem goldbachG11CofactorWindow_one (N : ℕ) (v : GoldbachG11Label) :
    goldbachG11CofactorWindow N 1 v = ∅ := by
  simp [goldbachG11CofactorWindow]

theorem goldbachG11BuchstabMass_one_window (x q : ℝ) :
    goldbachG11BuchstabMass x q - goldbachG11BuchstabMass (1 * x) q = 0 := by
  simp

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig