import Wu18938Campaign.M1.Confirmed.Omega2Blocks
import Wu18938Campaign.M1.Confirmed.PayloadNormalization
import Wu18938Campaign.M1.Confirmed.ClassicalInputs
import MathlibNt.Wu2008DoubleSieve.Omega2PrimeIntegral

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter HighSourcePayload
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology Interval

theorem window_geometry {m i N d : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    (N : ℝ) ^ (η / 10) ≤ wuLocalCutoff N δ d t ∧
      wuLocalCutoff N δ d s ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / 2 : ℝ) :=
  ⟨roughBox_cutoff_lower hb hN hη hδ hd (by linarith) ht,
    rpow_le_rpow_of_exponent_le (hb.support_geometry hN hη hδ hd).2.2.1.le
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs)⟩

theorem theta_nonneg {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ) :
    0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hli : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans (box_trueLi_lower hN)
  exact mul_nonneg (by positivity) (sum_nonneg (fun _ hd => roughBox_theta_weight hb hN hη hδ hd))

theorem prime_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      |reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
          (fun d p => f (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))) -
        (∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u))) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨Q0,_,hprime⟩ := omega2_source_prime_integral_uniform
    (show (0 : ℝ) ≤ 11 by norm_num) (half_pos he)
  obtain ⟨T1,hdelete⟩ := primeCoefficient_all_to_coprime_uniform
    (show 0 < η / 10 by positivity) (show (0 : ℝ) ≤ 11 by norm_num) (half_pos he)
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop Q0))
  refine ⟨max 4 (max T1 T2),le_max_left _ _,?_⟩
  intro N hN i Δ V hb f hf hfb s t hs hst ht ht5
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let I := ∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u))
  let g := fun d p : ℕ => f (t * (1 - log p / log (Q / d)))
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      |(∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) - I| ≤ ε := by
    have hgeom := hb.support_geometry (by omega) hη hδ hd
    have hwin := window_geometry hb (by omega) hη hδ hd hs hst (by linarith)
    have hmain := hprime (Q / d) ((h2 N (by omega)).trans (hb.remaining d hd))
      f hf hfb s t hs hst ht ht5
    have hdel := hdelete N (by omega) (Q / d) (wuLocalCutoff N δ d t)
      (wuLocalCutoff N δ d s) (g d) hgeom.2.2.1 hwin.1 hwin.2 (by
        intro p hp
        have hh := mem_primeWindow.mp hp
        exact hfb _ (omega2_window_parameter_mem hgeom.2.2.1
          (by exact_mod_cast hh.1.one_lt) hs hst ht ht5 hh.2.2.1 hh.2.2.2))
    rw [abs_sub_comm] at hdel
    exact (abs_sub_le _ _ _).trans ((add_le_add hdel hmain).trans_eq (by ring))
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower (by omega)))
  let w := fun d => (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
    ((Nat.totient d : ℝ) * log (Q / d))
  have hw := fun d hd => roughBox_theta_weight hb (by omega) hη hδ (d := d) hd
  change |4 * logarithmicIntegral N *
      (∑ d ∈ boxConvolutionSupport W, w d *
        ∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) -
      I * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)
  rw [mul_left_comm I,← mul_sub,abs_mul,abs_of_nonneg hli,mul_left_comm ε]
  apply mul_le_mul_of_nonneg_left _ hli
  rw [mul_comm I,sum_mul,← sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d *
        ((∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) - I)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W, w d * ε := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul,abs_of_nonneg (hw d hd)]
      exact mul_le_mul_of_nonneg_left (hpoint d hd) (hw d hd)
    _ = _ := by rw [← sum_mul,mul_comm]

theorem repeated_relative (m : ℕ) {η δ α ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hα : 0 < α) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      reboxingRepeatedTheta N ((N : ℝ) ^ (1 / 2 - δ)) α (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 4 (4 / (α * ε)))))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN i Δ V hb
  have hlarge := hT N (by omega)
  simp only [Function.comp_apply] at hlarge
  have hfinite := reboxingRepeatedTheta_le (by omega : 4 ≤ N) hα
    ((le_max_left _ _).trans hlarge) (fun d hd => by
      have hh := hb.support_geometry (by omega) hη hδ (d := d) hd
      exact ⟨hh.1,hh.2.1,hh.2.2.1⟩)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcoef : 4 / (α * (N : ℝ) ^ α) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_le_iff₀ (mul_pos hα he)).mp ((le_max_right _ _).trans hlarge)
    nlinarith only [hh]
  exact hfinite.trans (mul_le_mul_of_nonneg_right hcoef (theta_nonneg hb (by omega) hη hδ))

end Wu18938Campaign.M1.Confirmed.Rebox
