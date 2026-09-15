import MathlibNt.Wu2008DoubleSieve.BoxMassTheta
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSourceCutoffs

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real Filter
open MathlibNt.SieveTheory.SingularSeries
open scoped Classical Topology

structure RoughBox (m : ℕ) (η δ : ℝ) (N i : ℕ) (Δ : ℝ)
    (V : Fin i → ℝ) : Prop where
  depth : i ≤ m
  ratio_lower : 1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ
  ratio_upper : Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ)
  lower : ∀ j, (N : ℝ) ^ η ≤ V j / Δ
  upper : ∀ j, V j ≤ N
  support_large : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (N : ℝ) ^ (3 / 10 : ℝ) ≤ (d : ℝ)
  remaining : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (N : ℝ) ^ η ≤ (N : ℝ) ^ (1 / 2 - δ) / d

namespace RoughBox

variable {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V)

include hb

theorem ratio_one : 1 ≤ Δ := by
  have h := rpow_nonneg (log_natCast_nonneg N) (-4)
  linarith [hb.ratio_lower]

theorem window_large (j : Fin i) (q : ℕ)
    (hq : q ∈ convolutionWuWindows N Δ V j) :
    q.Prime ∧ (N : ℝ) ^ η ≤ (q : ℝ) :=
  ⟨(mem_convolutionWuWindows.mp hq).1,
    (hb.lower j).trans (mem_convolutionWuWindows.mp hq).2.2.1⟩

theorem endpoint_lower (j : Fin i) : (N : ℝ) ^ η ≤ V j := by
  have hΔ : 0 < Δ := lt_of_lt_of_le zero_lt_one hb.ratio_one
  have h := (le_div_iff₀ hΔ).mp (hb.lower j)
  have hn := rpow_nonneg (Nat.cast_nonneg N) η
  nlinarith [hb.ratio_one]

theorem support_pos (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d :=
  boxConvolutionSupport_pos (fun j q hq => (hb.window_large j q hq).1.pos) hd

theorem support_geometry (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ d ≤ N ∧ 1 < (N : ℝ) ^ (1 / 2 - δ) / d ∧
      (N : ℝ) ^ (1 / 2 - δ) / d ≤ N := by
  have hd0 := hb.support_pos hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hQ : (N : ℝ) ^ (1 / 2 - δ) ≤ N := by
    simpa using rpow_le_rpow_of_exponent_le hNr.le
      (show 1 / 2 - δ ≤ (1 : ℝ) by linarith)
  have hrem := (one_lt_rpow hNr hη).trans_le (hb.remaining d hd)
  have hdQ : (d : ℝ) < (N : ℝ) ^ (1 / 2 - δ) := by
    simpa using (lt_div_iff₀ hdr).mp hrem
  refine ⟨hd0, ?_, hrem, ?_⟩
  · exact_mod_cast hdQ.le.trans hQ
  · apply (div_le_iff₀ hdr).mpr
    exact hQ.trans (le_mul_of_one_le_right (by positivity) hd1)

theorem theta_reciprocal_lower (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ) :
    2 * liuUniversalProduct * (N : ℝ) / log N ^ 2 *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
  boxTheta_lower_of_support _ hN (fun _ hd => hb.support_pos hd)
    (fun d hd => (hb.support_geometry (by omega) hη hδ hd).2.2)

theorem cutoff_antitone (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    wuLocalCutoff N δ d v ≤ wuLocalCutoff N δ d u :=
  rpow_le_rpow_of_exponent_le (hb.support_geometry hN hη hδ hd).2.2.1.le
    (one_div_le_one_div_of_le hu huv)

theorem mother_window_large (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {q : ℕ}
    (hq : q ∈ primeWindow N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.s)) :
    q.Prime ∧ (N : ℝ) ^ (η / 10) ≤ (q : ℝ) := by
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one
    (hp.one_le_s.trans (hp.s_le_kappa3.trans
      (hp.kappa3_lt_kappa2.le.trans (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hpow := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg N) η)
    (hb.remaining d hd) (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hstep : (N : ℝ) ^ (η / 10) ≤
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / 10 : ℝ) := by
    simpa only [← rpow_mul (Nat.cast_nonneg N), div_eq_mul_inv, one_mul] using hpow
  exact ⟨(mem_primeWindow.mp hq).1, hstep.trans
    ((rpow_le_rpow_of_exponent_le (hb.support_geometry hN hη hδ hd).2.2.1.le
      (one_div_le_one_div_of_le hS hp.S_le_ten)).trans (mem_primeWindow.mp hq).2.2.1)⟩

end RoughBox

theorem roughBox_theta_lower (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
        c * N / log (N : ℝ) ^ (5 * m + 2) ≤
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hm⟩ := wu_boxConvolution_mass_bounds m hη
  refine ⟨2 * liuUniversalProduct * (1 / 12 : ℝ) ^ m, by
    have := liuUniversalProduct_pos
    positivity, max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hmass := (hm N ((le_max_right _ _).trans hN) i hb.depth Δ
    hb.ratio_lower hb.ratio_upper V hb.endpoint_lower hb.upper).1
  calc
    _ = (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) *
        ((1 / 12 : ℝ) ^ m / log N ^ (5 * m)) := by rw [pow_add]; ring
    _ ≤ (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
      mul_le_mul_of_nonneg_left hmass (by
        have := liuUniversalProduct_pos
        positivity)
    _ ≤ _ := hb.theta_reciprocal_lower hN4 hη hδ

theorem roughBox_power_mass_relative (m : ℕ) {η δ ε C ρ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
        (C * ((N : ℝ) / (N : ℝ) ^ ρ)) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hU := liuUniversalProduct_pos
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 2
      (show 0 < C / (2 * ε * liuUniversalProduct) by positivity) hρ)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hpay := hT N ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcoef : C * ((N : ℝ) / (N : ℝ) ^ ρ) ≤
      ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) := by
    calc
      _ ≤ C * ((N : ℝ) /
          ((C / (2 * ε * liuUniversalProduct)) * log (N : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) hpay) hC.le
      _ = _ := by field_simp
  have hmass : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d))
  calc
    _ ≤ (ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2)) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
      mul_le_mul_of_nonneg_right hcoef hmass
    _ = ε * ((2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb.theta_reciprocal_lower hN4 hη hδ) hε.le

end Wu18938Campaign.M1.Confirmed
