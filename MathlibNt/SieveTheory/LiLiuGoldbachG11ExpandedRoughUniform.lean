import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorGridCount

open Filter Set LiLiuPrereqBuchstab
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- One frozen uniform Buchstab source, with a moving output size. All q and
all y in the expanded coarse window share one threshold. No numerical bound
on omega is hypothesized. -/
theorem goldbachG11_expanded_rough_uniform (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ q y : ℝ,
      (N : ℝ)^(4/53 : ℝ) ≤ q → q ≤ (N : ℝ)^(4/33 : ℝ) →
      (N : ℝ)^(1/2 : ℝ) ≤ y → y ≤ (N : ℝ)^2 →
      1 < y ∧ 1 < q ∧ Real.log y/Real.log q ∈ Icc (4 : ℝ) 100 ∧
      |(roughCount y q : ℝ)-goldbachG11BuchstabMass y q| ≤ η*y/Real.log q := by
  obtain ⟨X,hX,hsource⟩ := roughCount_uniform_buchstab (u₀ := 4) (by norm_num) hη
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).eventually
    (eventually_ge_atTop X))
  refine ⟨max 4 ⌈M⌉₊,le_max_left _ _,?_⟩
  intro N hN q y hql hqu hyl hyu
  obtain ⟨hn4,hnM⟩ := max_le_iff.mp hN
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < N := by linarith
  have hln := Real.log_pos hn1
  have hq1 : 1 < q := (Real.one_lt_rpow hn1 (by norm_num : (0 : ℝ) < 4/53)).trans_le hql
  have hy1 : 1 < y := (Real.one_lt_rpow hn1 (by norm_num : (0 : ℝ) < 1/2)).trans_le hyl
  have hlq := Real.log_pos hq1
  have hqlo := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hql
  have hqhi := Real.log_le_log (by linarith : 0 < q) hqu
  have hylo := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hyl
  have hyhi := Real.log_le_log (by linarith : 0 < y) hyu
  rw [Real.log_rpow hn0] at hqlo hqhi hylo
  rw [Real.log_pow] at hyhi
  norm_num only [Nat.cast_ofNat] at hyhi
  have hu : Real.log y/Real.log q ∈ Icc (4 : ℝ) 100 := by
    constructor
    · apply (le_div_iff₀ hlq).2; nlinarith
    · apply (div_le_iff₀ hlq).2; nlinarith
  have hx : X ≤ y := (hM N ((Nat.le_ceil M).trans (by exact_mod_cast hnM))).trans hyl
  have hs := hsource y hx (Real.log y/Real.log q) hu
  rw [← goldbachG11_buchstab_cutoff_identity hy1 hq1,
    goldbachG11_buchstab_source_mass_identity hy1 hq1] at hs
  exact ⟨hy1,hq1,hu,goldbachG11_buchstab_relative_to_absolute hy1 hq1 (by linarith [hu.1]) hη hs.2⟩

/-- The coarse collar uses the already proved omega<=1, not the sharper
ordered-domain constant outside its domain. -/
theorem goldbachG11_expanded_rough_coarse (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ q y : ℝ,
      (N : ℝ)^(4/53 : ℝ) ≤ q → q ≤ (N : ℝ)^(4/33 : ℝ) →
      (N : ℝ)^(1/2 : ℝ) ≤ y → y ≤ (N : ℝ)^2 →
      (roughCount y q : ℝ) ≤ (1+η)*y/Real.log q := by
  obtain ⟨M,hM,hm⟩ := goldbachG11_expanded_rough_uniform η hη
  refine ⟨M,hM,?_⟩
  intro N hN q y hql hqu hyl hyu
  obtain ⟨hy,hq,hu,he⟩ := hm N hN q y hql hqu hyl hyu
  have hb := (goldbachG11_buchstab_mass_pos_le hy hq (by linarith [hu.1])).2
  have hh := (abs_le.mp he).2
  have heq : (1+η)*y/Real.log q = y/Real.log q+η*y/Real.log q := by ring
  rw [heq]
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig