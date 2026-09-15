import Wu18938Campaign.M1.Confirmed.PairGeometry

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real Filter
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology

theorem remainder_relative {S U : ℝ} (hcap : CapAdmissible S U) (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel, X ⊆ capLabels S U N δ (convolutionWuWindows N Δ V) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
      |gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X z| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C,hC,T1,hBV⟩ := convolution_bombieri_vinogradov (m + 2)
    (show 0 < η / 10 by positivity) hδ (by positivity : (0 : ℝ) < (5 * m + 3 : ℕ))
  obtain ⟨c,hc,T2,_,hTheta⟩ := roughBox_theta_lower m hη hδ
  obtain ⟨T3,hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * c))))
  refine ⟨max 4 (max T1 (max T2 T3)),le_max_left _ _,?_⟩
  intro N hN i Δ V hb X hX z
  let P := gamma5ClassicalLargePrimes N (η / 10)
  have hP : ∀ q ∈ P, q.Prime ∧ q.Coprime N ∧ (N : ℝ) ^ (η / 10) ≤ q :=
    fun q hq => (mem_filter.mp hq).2
  have hW : ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ q.Coprime N ∧ (N : ℝ) ^ (η / 10) ≤ q := by
    intro j q hq
    exact ⟨(hb.window_large j q hq).1,(mem_convolutionWuWindows.mp hq).2.1,
      (rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
        (by linarith : η / 10 ≤ η)).trans (hb.window_large j q hq).2⟩
  have hlabels : X ⊆ boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ (P ×ˢ P) := by
    intro x hx
    have hg := geometry hb (by omega) hη hδ hcap (hX hx)
    obtain ⟨ha,hp,hq,hpN,hqN,_,hpq,_⟩ := mem_filter.mp (hX hx)
    obtain ⟨hd,hpqrange⟩ := mem_product.mp ha
    obtain ⟨hprange,hqrange⟩ := mem_product.mp hpqrange
    exact mem_product.mpr ⟨hd,mem_product.mpr
      ⟨mem_filter.mpr ⟨hprange,hp,hpN,hg.prime_lower⟩,
        mem_filter.mpr ⟨hqrange,hq,hqN,hg.prime_lower.trans (by exact_mod_cast hpq.le)⟩⟩⟩
  have hbound := (gamma5Classical_masked_remainder_le N δ _ P X hlabels z).trans
    (hBV N (by omega) (i + 1 + 1) (by have := hb.depth; omega) _
      (fun j => Fin.cases hP (fun j => Fin.cases hP hW j) j))
  rw [rpow_natCast] at hbound
  have hlog := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
  have htheta := hTheta N (by omega) i Δ V hb
  have hbudget : C / log (N : ℝ) ≤ ε * c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos he hc)).mp (hlogT N (by omega))
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ C * N / log (N : ℝ) ^ (5 * m + 3) := hbound
    _ = (C / log (N : ℝ)) * ((N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) := by
      rw [show 5 * m + 3 = (5 * m + 2) + 1 by omega,pow_succ]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε * (c * (N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta he.le

theorem density {S U : ℝ} (hcap : CapAdmissible S U) (m : ℕ) {η δ τ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ x ∈ capLabels S U N δ (convolutionWuWindows N Δ V),
      ordinaryRosserMainSum true N (gamma5ClassicalProduct x)
        (wuVariableRosserLevel N δ (gamma5ClassicalProduct x)) (classicalCutoff S N δ x) ≤
        (1 + τ) ^ 2 * (4 * wuSingularSeries (gamma5ClassicalProduct x * N) /
          log (gamma5ClassicalLevel N δ x)) := by
  let ρ : ℝ := 2 * exp eulerMascheroniConstant * τ / 3
  let ζ : ℝ := η * min (1 / S) ((1 - 2 * U) / 2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hζ : 0 < ζ := by
    have hS : 0 < S := by linarith [hcap.three_le_S]
    have hU : 0 < (1 - 2 * U) / 2 := by linarith [hcap.cap_lt_half]
    dsimp [ζ]
    positivity
  obtain ⟨ZD,hden⟩ := ordinaryRosser_upper_density_canonical_bounded_local hρ
  obtain ⟨ZE,hEuler⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative (2 / ζ) τ (by positivity) hτ)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hζ).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 2 (max ZD ZE))))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN heven i Δ V hb x hx
  have hg := geometry hb (by omega) hη hδ hcap hx
  let L := gamma5ClassicalLevel N δ x
  let z := classicalCutoff S N δ x
  let r := log L / log z
  have hlL : 0 < log L := log_pos hg.level_gt_one
  have hlz : 0 < log z := log_pos hg.cutoff_gt_one
  have hr0 : 0 < r := div_pos hlL hlz
  have hr3 : r ≤ 3 := hg.ratio_upper
  have hzlarge : max 2 (max ZD ZE) ≤ z := (hT N (by omega)).trans hg.cutoff_lower
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hzlarge
  have hzD : ZD ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hzlarge)
  have hzE : ZE ≤ z := (le_max_right _ _).trans ((le_max_right _ _).trans hzlarge)
  have hdensity := hden N (gamma5ClassicalProduct x) heven z L r hzD hz2
    (by linarith [hg.level_gt_one]) rfl
    (by have := hg.ratio_lower; change 2 ≤ r at this; linarith) (by linarith)
  have hMN : 0 < gamma5ClassicalProduct x * N := Nat.mul_pos hg.product_pos (by omega)
  have hC : 0 < wuSingularSeries (gamma5ClassicalProduct x * N) := wuSingularSeries_pos _ hMN
  have hnorm := hEuler z hzE (gamma5ClassicalProduct x * N) hMN (heven.mul_left _)
    (polynomial_envelope hb (by omega) hη hδ hcap hx)
  have hbase : 0 < 2 * exp (-eulerMascheroniConstant) *
      wuSingularSeries (gamma5ClassicalProduct x * N) / log z := by positivity
  have hprod : localSieveProduct (gamma5ClassicalProduct x * N) z ≤
      (1 + τ) * (2 * r * wuSingularSeries (gamma5ClassicalProduct x * N) /
        (exp eulerMascheroniConstant * log L)) := by
    have hratio :
        localSieveProduct (gamma5ClassicalProduct x * N) z /
          (2 * exp (-eulerMascheroniConstant) * wuSingularSeries (gamma5ClassicalProduct x * N) / log z)
          ≤ 1 + τ := by linarith [(le_abs_self (_ : ℝ)).trans hnorm]
    have h := (div_le_iff₀ hbase).mp hratio
    have heq : 2 * exp (-eulerMascheroniConstant) * wuSingularSeries (gamma5ClassicalProduct x * N) / log z =
        2 * r * wuSingularSeries (gamma5ClassicalProduct x * N) / (exp eulerMascheroniConstant * log L) := by
      rw [exp_neg]
      dsimp [r]
      field_simp
    rwa [heq] at h
  have hF : 0 ≤ jr1965F r + ρ := by rw [jr1965F_eq_of_le_three hr3]; positivity
  exact hdensity.trans ((mul_le_mul_of_nonneg_left hprod hF).trans
    (canonical_upper_normalization_budget hr0 hr3 hC.le hlL hτ.le))

theorem mask_upper {S U : ℝ} (hcap : CapAdmissible S U) (m : ℕ) {η δ τ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel, X ⊆ capLabels S U N δ (convolutionWuWindows N Δ V) →
      fixedCount S N δ (convolutionWuWindows N Δ V) X ≤
        (1 + τ) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := density hcap m hη hδ hτ
  obtain ⟨T1,_,h1⟩ := remainder_relative hcap m hη hδ he
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb X hX
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hpoint : ∀ x ∈ X,
      (sourceSieveCount N (gamma5ClassicalProduct x) (x.1 * N) (wuLocalCutoff N δ x.1 S) : ℝ) ≤
      (logarithmicIntegral N / (Nat.totient (gamma5ClassicalProduct x) : ℝ)) *
        ((1 + τ) ^ 2 * (4 * wuSingularSeries (gamma5ClassicalProduct x * N) /
          log (gamma5ClassicalLevel N δ x))) +
      ordinaryRosserRemainder true N (gamma5ClassicalProduct x)
        (wuVariableRosserLevel N δ (gamma5ClassicalProduct x)) (classicalCutoff S N δ x) := by
    intro x hx
    have hg := geometry hb (by omega) hη hδ hcap (hX hx)
    obtain ⟨_,hp,hq,_,_,hzp,hpq,_⟩ := mem_filter.mp (hX hx)
    have hsame := gamma5Classical_source_count_eq (N := N) (d := x.1) hp hq hzp
      (hzp.trans (by exact_mod_cast hpq.le))
    change sourceSieveCount N (gamma5ClassicalProduct x) (x.1 * N) _ =
      sourceSieveCount N (gamma5ClassicalProduct x) (gamma5ClassicalProduct x * N) _ at hsame
    rw [hsame]
    have hfloor : gamma5ClassicalLevel N δ x <
        (wuVariableRosserLevel N δ (gamma5ClassicalProduct x) : ℝ) :=
      by exact_mod_cast Nat.lt_floor_add_one (gamma5ClassicalLevel N δ x)
    have hD : 1 < wuVariableRosserLevel N δ (gamma5ClassicalProduct x) :=
      by exact_mod_cast hg.level_gt_one.trans hfloor
    apply ((gamma5Classical_source_count_antitone N (gamma5ClassicalProduct x)
      (gamma5ClassicalProduct x * N) (min_le_left _ _)).trans
        (ordinaryRosser_upper_finite hD (hg.cutoff_le_level.trans hfloor.le))).trans
    exact add_le_add (mul_le_mul_of_nonneg_left (h0 N (by omega) heven i Δ V hb x (hX hx))
      (div_nonneg hli (Nat.cast_nonneg _))) le_rfl
  have hfinite : fixedCount S N δ (convolutionWuWindows N Δ V) X ≤
      (1 + τ) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
      gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X (classicalCutoff S N δ) := by
    unfold fixedCount gamma5ClassicalMainMass gamma5ClassicalRemainder
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (hpoint x hx)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) x.1))
    convert hh using 1
    dsimp only [gamma5ClassicalLevel]
    ring
  exact hfinite.trans (add_le_add le_rfl
    ((le_abs_self _).trans (h1 N (by omega) i Δ V hb X hX (classicalCutoff S N δ))))

end Wu18938Campaign.M1.Confirmed.Pair
