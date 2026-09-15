import R2GammaHighPairMass

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset Filter MotherPair HighBoxRecovery
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Topology

theorem pair_density {S U δ η : ℝ} (hcap : CapAdmissible S U)
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heta : 0 < η) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      ∀ x ∈ capLabels S U N δ (windows j N),
        ordinaryRosserMainSum true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x)) (classicalCutoff S N δ x) ≤
        (1+η)^2*(4*wuSingularSeries (gamma5ClassicalProduct x*N)/log (gamma5ClassicalLevel N δ x)) := by
  let ρ : ℝ := 2*exp eulerMascheroniConstant*η/3
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hζ := (classical_exponents_pos hcap 0 hd (by linarith : δ < 1/2)).2
  obtain ⟨ZD, hden⟩ := ordinaryRosser_upper_density_canonical_bounded_local hρ
  obtain ⟨ZE, hEuler⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative (2/classicalZeta S U 0 δ) η (by positivity) heta)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 2 (max ZD ZE) ≤ (N : ℝ)^classicalZeta S U 0 δ :=
    ((tendsto_rpow_atTop hζ).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  apply eventually_atTop.mp
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with N hlargeN hN
  intro he j x hx
  have hg := pair_geometry hcap j hN hd hh hx
  let L := gamma5ClassicalLevel N δ x
  let z := classicalCutoff S N δ x
  let r := log L/log z
  have hlL : 0 < log L := log_pos hg.level_gt_one
  have hlz : 0 < log z := log_pos hg.cutoff_gt_one
  have hr0 : 0 < r := div_pos hlL hlz
  have hr3 : r ≤ 3 := hg.ratio_upper
  have hzlarge : max 2 (max ZD ZE) ≤ z := hlargeN.trans hg.cutoff_lower
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hzlarge
  have hzD : ZD ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hzlarge)
  have hzE : ZE ≤ z := (le_max_right _ _).trans ((le_max_right _ _).trans hzlarge)
  have hdensity := hden N (gamma5ClassicalProduct x) he z L r hzD hz2
    (by linarith [hg.level_gt_one]) rfl
    (by have := hg.ratio_lower; change 2 ≤ r at this; linarith) (by linarith)
  have hMN : 0 < gamma5ClassicalProduct x*N := Nat.mul_pos hg.product_pos (by omega)
  have hC : 0 < wuSingularSeries (gamma5ClassicalProduct x*N) := wuSingularSeries_pos _ hMN
  have hnorm := hEuler z hzE (gamma5ClassicalProduct x*N) hMN (he.mul_left _)
    (classical_polynomial_envelope hζ hg)
  have hbase : 0 < 2*exp (-eulerMascheroniConstant)*wuSingularSeries (gamma5ClassicalProduct x*N)/log z := by
    positivity
  have hprod : localSieveProduct (gamma5ClassicalProduct x*N) z ≤
      (1+η)*(2*r*wuSingularSeries (gamma5ClassicalProduct x*N)/(exp eulerMascheroniConstant*log L)) := by
    have hratio : localSieveProduct (gamma5ClassicalProduct x*N) z/
        (2*exp (-eulerMascheroniConstant)*wuSingularSeries (gamma5ClassicalProduct x*N)/log z) ≤ 1+η := by
      linarith [(le_abs_self (_ : ℝ)).trans hnorm]
    have h := (div_le_iff₀ hbase).mp hratio
    have heq : 2*exp (-eulerMascheroniConstant)*wuSingularSeries (gamma5ClassicalProduct x*N)/log z =
        2*r*wuSingularSeries (gamma5ClassicalProduct x*N)/(exp eulerMascheroniConstant*log L) := by
      rw [exp_neg]
      dsimp [r]
      field_simp
    rwa [heq] at h
  have hF : 0 ≤ jr1965F r+ρ := by
    rw [jr1965F_eq_of_le_three hr3]
    positivity
  exact hdensity.trans ((mul_le_mul_of_nonneg_left hprod hF).trans
    (canonical_upper_normalization_budget hr0 hr3 hC.le hlL heta.le))

theorem pair_finite_upper {S U : ℝ} (hcap : CapAdmissible S U)
    {N : ℕ} {δ : ℝ} (j : Fin 3) (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    {x : Gamma5ClassicalLabel} (hx : x ∈ capLabels S U N δ (windows j N)) :
    (sourceSieveCount N (gamma5ClassicalProduct x) (x.1*N) (wuLocalCutoff N δ x.1 S) : ℝ) ≤
      (logarithmicIntegral N/(Nat.totient (gamma5ClassicalProduct x) : ℝ))*
        ordinaryRosserMainSum true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x)) (classicalCutoff S N δ x) +
        ordinaryRosserRemainder true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x)) (classicalCutoff S N δ x) := by
  have hg := pair_geometry hcap j hN hd hh hx
  obtain ⟨_, hp, hq, _, _, hzp, hpq, _⟩ := mem_filter.mp hx
  have hsame := gamma5Classical_source_count_eq (N := N) (d := x.1) hp hq hzp
    (hzp.trans (by exact_mod_cast hpq.le))
  change sourceSieveCount N (gamma5ClassicalProduct x) (x.1*N) _ =
    sourceSieveCount N (gamma5ClassicalProduct x) (gamma5ClassicalProduct x*N) _ at hsame
  rw [hsame]
  have hfloor : gamma5ClassicalLevel N δ x <
      (wuVariableRosserLevel N δ (gamma5ClassicalProduct x) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (gamma5ClassicalLevel N δ x)
  have hD : 1 < wuVariableRosserLevel N δ (gamma5ClassicalProduct x) := by
    exact_mod_cast hg.level_gt_one.trans hfloor
  apply (gamma5Classical_source_count_antitone N (gamma5ClassicalProduct x)
    (gamma5ClassicalProduct x*N) (min_le_left _ _)).trans
  exact ordinaryRosser_upper_finite hD (hg.cutoff_le_level.trans hfloor.le)

theorem pair_remainder_paid {S U δ : ℝ} (hcap : CapAdmissible S U)
    (hd : 0 < δ) (hh : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ X : Finset Gamma5ClassicalLabel, X ⊆ capLabels S U N δ (windows j N) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
        |gamma5ClassicalRemainder N δ (windows j N) X z| ≤ C*N/log (N : ℝ)^(3 : ℝ) := by
  have hα := (classical_exponents_pos hcap 0 hd (by linarith : δ < 1/2)).1
  let β := min highEta (classicalAlpha S 0 δ)
  have hβ : 0 < β := lt_min (by norm_num [highEta]) hα
  obtain ⟨C, hC, T, hBV⟩ := convolution_bombieri_vinogradov 3 hβ hd (show (0 : ℝ) < 3 by norm_num)
  refine ⟨C, hC, max 4 T, le_max_left _ _, ?_⟩
  intro N hN j X hX z
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := gamma5ClassicalLargePrimes N (classicalAlpha S 0 δ)
  have hlabels : capLabels S U N δ (windows j N) ⊆ boxConvolutionSupport (windows j N) ×ˢ (P ×ˢ P) := by
    intro x hx
    have hg := pair_geometry hcap j hN2 hd hh hx
    obtain ⟨ha, hp, hq, hpN, hqN, _, hpq, _⟩ := mem_filter.mp hx
    obtain ⟨hm, hpqrange⟩ := mem_product.mp ha
    obtain ⟨hprange, hqrange⟩ := mem_product.mp hpqrange
    exact mem_product.mpr ⟨hm, mem_product.mpr
      ⟨mem_filter.mpr ⟨hprange, hp, hpN, hg.prime_lower⟩,
        mem_filter.mpr ⟨hqrange, hq, hqN, hg.prime_lower.trans (by exact_mod_cast hpq.le)⟩⟩⟩
  have hP : ∀ p ∈ P, p.Prime ∧ p.Coprime N ∧ (N : ℝ)^β ≤ p := by
    intro p hp
    have h := (mem_filter.mp hp).2
    exact ⟨h.1, h.2.1, (rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)).trans h.2.2⟩
  have hW : ∀ i p, p ∈ windows j N i → p.Prime ∧ p.Coprime N ∧ (N : ℝ)^β ≤ p := by
    intro i p hp
    have h := prime_geometry j hN2 hd hh hp
    exact ⟨h.1, h.2.1, (rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)).trans h.2.2.1⟩
  apply (gamma5Classical_masked_remainder_le N δ _ P X (hX.trans hlabels) z).trans
  apply hBV N (by omega) 3 le_rfl
  intro i
  exact Fin.cases hP (fun i => Fin.cases hP hW i) i

theorem pair_remainder_small {S U δ ε : ℝ} (hcap : CapAdmissible S U)
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ X : Finset Gamma5ClassicalLabel, X ⊆ capLabels S U N δ (windows j N) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
        |gamma5ClassicalRemainder N δ (windows j N) X z| ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C, _, T, hT4, hAP⟩ := pair_remainder_paid hcap hd hh
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C/(ε*wuSingularSeries 1))))
  refine ⟨max T M, hT4.trans (le_max_left _ _), ?_⟩
  intro N hN j X hX z
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hbudget : C ≤ ε*wuSingularSeries N*log (N : ℝ) := by
    have h := (div_le_iff₀ (mul_pos heps hC1)).mp (hM N (by omega))
    have hw := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hseries heps.le) hlog.le
    dsimp only [Function.comp_apply] at h
    linarith only [h, hw]
  apply (hAP N (by omega) j X hX z).trans
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, rpow_natCast]
  unfold truncatedSixthMassScale
  apply (div_le_iff₀ (pow_pos hlog 3)).mpr
  have hw := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℝ) N)
  convert hw using 1
  field_simp

theorem pair_mask_upper {S U δ η ε : ℝ} (hcap : CapAdmissible S U)
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heta : 0 < η) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ j : Fin 3, ∀ X : Finset Gamma5ClassicalLabel, X ⊆ capLabels S U N δ (windows j N) →
        fixedCount S N δ (windows j N) X ≤
          (1+η)^2*gamma5ClassicalMainMass N δ (windows j N) X + ε*truncatedSixthMassScale N := by
  obtain ⟨TD, hden⟩ := pair_density hcap hd hh heta
  obtain ⟨TR, hTR4, hrem⟩ := pair_remainder_small hcap hd hh heps
  refine ⟨max TD TR, hTR4.trans (le_max_right _ _), ?_⟩
  intro N hN he j X hX
  have hN2 : 2 ≤ N := by omega
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num) (by exact_mod_cast hN2)
  have hpoint : ∀ x ∈ X,
      (sourceSieveCount N (gamma5ClassicalProduct x) (x.1*N) (wuLocalCutoff N δ x.1 S) : ℝ) ≤
        (logarithmicIntegral N/(Nat.totient (gamma5ClassicalProduct x) : ℝ))*
          ((1+η)^2*(4*wuSingularSeries (gamma5ClassicalProduct x*N)/log (gamma5ClassicalLevel N δ x))) +
          ordinaryRosserRemainder true N (gamma5ClassicalProduct x)
            (wuVariableRosserLevel N δ (gamma5ClassicalProduct x)) (classicalCutoff S N δ x) := by
    intro x hx
    apply (pair_finite_upper hcap j hN2 hd hh (hX hx)).trans
    exact add_le_add (mul_le_mul_of_nonneg_left (hden N (by omega) he j x (hX hx))
      (div_nonneg hli (Nat.cast_nonneg _))) le_rfl
  have hfinite : fixedCount S N δ (windows j N) X ≤
      (1+η)^2*gamma5ClassicalMainMass N δ (windows j N) X +
      gamma5ClassicalRemainder N δ (windows j N) X (classicalCutoff S N δ) := by
    unfold fixedCount gamma5ClassicalMainMass gamma5ClassicalRemainder
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hpoint x hx) (Nat.cast_nonneg (convolutionCoeff (windows j N) x.1))
    convert h using 1
    dsimp only [gamma5ClassicalLevel]
    ring
  exact hfinite.trans (add_le_add le_rfl ((le_abs_self _).trans
    (hrem N (by omega) j X hX (classicalCutoff S N δ))))

#check @pair_density
#check @pair_finite_upper
#check @pair_remainder_paid
#check @pair_remainder_small
#check @pair_mask_upper
#print axioms pair_density
#print axioms pair_finite_upper
#print axioms pair_remainder_paid
#print axioms pair_remainder_small
#print axioms pair_mask_upper
end WuPaper.R2GammaHigh
