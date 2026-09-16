import Wu18938Campaign.M1.Confirmed.PairProfile
import WR2Gamma5FullMass
import MathlibNt.Wu2008DoubleSieve.MotherPairGainSmooth

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullFive

open Wu2008DoubleSieve MotherPair Finset Real Filter Set MeasureTheory
open scoped Classical Topology Interval

structure Rectangle (p : SecondFunctionalParameters) where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  sample : ℝ
  lowerP_lt_A : 1 / p.S < A
  A_lt_B : A < B
  B_lt_C : B < C
  C_lt_D : C < D
  D_lt_cap : D < 1 / p.kappa2
  twiceD_lt_one : 2 * D < 1
  sample_lower : 1 < sample
  sample_upper : sample < 3
  ratio_lt_sample : p.S * (1 - A - C) < sample

theorem ratio_margin {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (r : Rectangle p) :
    ∃ e : ℝ, 0 < e ∧ ∀ t u : ℝ, r.A - e ≤ t → r.C - e ≤ u →
      p.S * (1 - t - u) ≤ r.sample := by
  have hS : 0 < p.S := by linarith [hp.three_le_S]
  let e := (r.sample - p.S * (1 - r.A - r.C)) / (2 * p.S)
  have he : 0 < e := div_pos (sub_pos.mpr r.ratio_lt_sample) (by positivity)
  have heq : e * (2 * p.S) = r.sample - p.S * (1 - r.A - r.C) :=
    div_mul_cancel₀ _ (by positivity)
  refine ⟨e,he,?_⟩
  intro t u ht hu
  nlinarith [mul_le_mul_of_nonneg_left ht hS.le,mul_le_mul_of_nonneg_left hu hS.le]

theorem rectangle_admitted (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (r : Rectangle p) (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      1 < gamma5GainScale N δ V ∧ ∀ P Q : ℝ,
      (gamma5GainScale N δ V) ^ r.A ≤ P → P ≤ (gamma5GainScale N δ V) ^ r.B →
      (gamma5GainScale N δ V) ^ r.C ≤ Q → Q ≤ (gamma5GainScale N δ V) ^ r.D →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p .gammaFive N δ (convolutionWuWindows N Δ V) ∧
      ∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        Hratio p .gammaFive
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ r.sample := by
  obtain ⟨e,he,hratio⟩ := ratio_margin hp r
  let ε := min e (min (r.A - 1 / p.S) (r.C - r.B))
  have hε : 0 < ε := lt_min he
    (lt_min (sub_pos.mpr r.lowerP_lt_A) (sub_pos.mpr r.B_lt_C))
  have hεe : ε ≤ e := min_le_left _ _
  have hεA : ε ≤ r.A - 1 / p.S := (min_le_right _ _).trans (min_le_left _ _)
  have hεgap : ε ≤ r.C - r.B := (min_le_right _ _).trans (min_le_right _ _)
  have hD : r.D ≤ 1 := by linarith [r.twiceD_lt_one]
  have hB : r.B ≤ 1 := by linarith [r.B_lt_C,r.C_lt_D]
  obtain ⟨T,hT4,hT⟩ := Pair.gain_mesh m hη hδ hε
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb
  obtain ⟨hΔ,hR,hmesh⟩ := hT N hN i Δ V hb
  refine ⟨hR,?_⟩
  intro P Q hPA hPB hQC hQD
  have point (x : Gamma5ClassicalLabel)
      (hx : x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) :
      x ∈ termLabels p .gammaFive N δ (convolutionWuWindows N Δ V) ∧
      Hratio p .gammaFive
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ r.sample := by
    obtain ⟨hd,hpq⟩ := mem_product.mp hx
    obtain ⟨ha,hb'⟩ := mem_product.mp hpq
    have hac := Pair.micro_source hb (by omega) hη hδ hR hΔ hB hPA hPB hd ha
    have hbc := Pair.micro_source hb (by omega) hη hδ hR hΔ hD hQC hQD hd hb'
    have ha' := mem_primeWindow.mp ha
    have hb'' := mem_primeWindow.mp hb'
    have hgeo := hb.support_geometry (by omega) hη hδ hd
    have hRd := hgeo.2.2.1
    have hpa : 1 / p.S ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 := by
      linarith [hac.1]
    have hqa : 1 / p.S ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 := by
      linarith [hbc.1,r.A_lt_B,r.B_lt_C]
    have hpw := mem_primeWindow.mp (gamma5Gain_coordinate_window hRd ha'.1 ha'.2.1 hpa hac.2)
    have hqw := mem_primeWindow.mp (gamma5Gain_coordinate_window hRd hb''.1 hb''.2.1 hqa hbc.2)
    have hcut (E : ℝ) (hE : E ≤ 1) : ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ E ≤ N :=
      (by simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hRd.le hE :
        ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ E ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1).trans hgeo.2.2.2
    have hpN : x.2.1 < N + 1 := by
      have hh : x.2.1 ≤ N := by exact_mod_cast hpw.2.2.2.le.trans (hcut r.B hB)
      omega
    have hqN : x.2.2 < N + 1 := by
      have hh : x.2.2 ≤ N := by exact_mod_cast hqw.2.2.2.le.trans (hcut r.D hD)
      omega
    have hpq' : x.2.1 < x.2.2 := by
      by_contra hn
      have hn' : (x.2.2 : ℝ) ≤ x.2.1 := by exact_mod_cast (not_lt.mp hn)
      have hl := div_le_div_of_nonneg_right
        (log_le_log (by exact_mod_cast hb''.1.pos) hn') (log_pos hRd).le
      change gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 ≤
        gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 at hl
      linarith [hac.2,hbc.1]
    constructor
    · apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨hd,mem_product.mpr ⟨mem_range.mpr hpN,mem_range.mpr hqN⟩⟩,
        ha'.1,hb''.1,ha'.2.1,hb''.2.1,hpw.2.2.1,?_,hqw.2.2.1,?_,hpq'⟩
      · exact hpw.2.2.2.trans_le
          (rpow_le_rpow_of_exponent_le hRd.le
            (r.B_lt_C.le.trans (r.C_lt_D.le.trans r.D_lt_cap.le)))
      · exact hqw.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hRd.le r.D_lt_cap.le)
    · exact hratio _ _ (by linarith [hac.1]) (by linarith [hbc.1])
  exact ⟨fun x hx => (point x hx).1,fun x hx => (point x hx).2⟩

theorem smooth_indicator {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (r : Rectangle p) :
    (∫ v : ℝ × ℝ, (Ico r.A r.B ×ˢ Ico r.C r.D).indicator (gainSmooth p) v) =
      rectIntegral r.A r.B r.C r.D := by
  have hi : IntegrableOn (gainSmooth p) (Ico r.A r.B ×ˢ Ico r.C r.D) :=
    ((gain_smooth_continuous hp).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  rw [integral_indicator (measurableSet_Ico.prod measurableSet_Ico)]
  rw [show (∫ v in Ico r.A r.B ×ˢ Ico r.C r.D, gainSmooth p v) =
      ∫ t in Ico r.A r.B, ∫ u in Ico r.C r.D, gainSmooth p (t,u) from setIntegral_prod _ hi]
  simp_rw [integral_Ico_eq_integral_Ioc]
  simp_rw [← intervalIntegral.integral_of_le r.C_lt_D.le]
  rw [← intervalIntegral.integral_of_le r.A_lt_B.le]
  unfold rectIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc r.A r.B := by simpa only [uIcc_of_le r.A_lt_B.le] using ht
  dsimp only
  rw [max_eq_left (ht'.2.trans r.B_lt_C.le),min_eq_right r.C_lt_D.le]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc r.C r.D := by simpa only [uIcc_of_le r.C_lt_D.le] using hu
  have he := (parameter_order hp).2.2.2.1
  exact gain_smooth_eq
    ⟨r.lowerP_lt_A.le.trans ht'.1,
      ht'.2.trans (r.B_lt_C.le.trans (r.C_lt_D.le.trans (r.D_lt_cap.le.trans he.le)))⟩
    ⟨r.lowerP_lt_A.le.trans (r.A_lt_B.le.trans (r.B_lt_C.le.trans hu'.1)),
      hu'.2.trans (r.D_lt_cap.le.trans he.le)⟩

end Wu18938Campaign.M1.Confirmed.FullFive
