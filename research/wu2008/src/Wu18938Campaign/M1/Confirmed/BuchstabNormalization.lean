import Wu18938Campaign.M1.Confirmed.BuchstabBlocks
import Wu18938Campaign.M1.Confirmed.Omega2Mass
import MathlibNt.Wu2008DoubleSieve.ReboxingUpperNormalization

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology

def shiftedPrime {i : ℕ} (f : ℝ → ℝ) (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow N
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t 0)
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r),
        f (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1) /
          (((p : ℝ) - 2) * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))

def shiftedBoundary {i : ℕ} (f : ℝ → ℝ) (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow N
          (((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / t))
          (wuLocalCutoff N δ d t),
        |f (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1) /
          (((p : ℝ) - 2) * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))|

theorem upperMain_to_prime (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, 0 ≤ f v) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      upperMain f N δ Δ V t r ≤ shiftedPrime f N δ Δ V t r := by
  obtain ⟨T0,hT04,h0⟩ := scale m hη hδ
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < η / 20 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb f hf hf0 s t hs hst ht r hr
  obtain ⟨hΔ,hL,hqlo,hq,_,hmesh⟩ := h0 N (by omega) i Δ V hb
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let b := fun d : ℕ => wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))
  let F := fun d p : ℕ => f (log (Q / d) / log p - 1) /
    (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hΔ0 : 0 < Δ := by linarith
  have hq0 : 0 < q := by dsimp [q,Q]; linarith
  have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hNpos η).trans_le (hb.endpoint_lower l)
  have hD := fun d hd => reboxing_support_level_bounds (rpow_nonneg hNpos.le (1 / 2 - δ))
    hΔ0 hV (N := N) (d := d) hd
  have hlarge := h1 N (by omega)
  simp only [Function.comp_apply] at hlarge
  have hlow : (N : ℝ) ^ (η / 20) ≤ q ^ (1 / t) := by
    calc
      _ = ((N : ℝ) ^ (η / 2)) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul hNpos.le]
        congr 1
        ring
      _ ≤ q ^ (1 / 10 : ℝ) := rpow_le_rpow (by positivity) hqlo (by norm_num)
      _ ≤ _ := rpow_le_rpow_of_exponent_le hq.le (one_div_le_one_div_of_le (by linarith) ht)
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower (by omega)))
  have hblock : upperMain f N δ Δ V t r ≤
      4 * logarithmicIntegral N * ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) *
          ∑ p ∈ primeWindow N (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j + 1)), b d * F d p := by
    unfold upperMain
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
    have htop := (hm (show (j : ℝ) + 1 ≤ r by exact_mod_cast mem_range.mp hj)).trans hr
    have hdom := reboxing_parameter_domain hq hΔ hs hst ht
      (show (1 : ℝ) ≤ j + 1 by linarith [Nat.cast_nonneg (α := ℝ) j]) htop hmesh
    simp only [convolutionWuWindows_cons,reboxingAlpha_previous hΔ0,
      add_sub_cancel_right,boxTheta_cons]
    rw [mul_left_comm (f _)]
    apply mul_le_mul_of_nonneg_left _ hli
    simp only [mul_sum]
    apply sum_le_sum
    intro d hd
    apply sum_le_sum
    intro p hp
    have hh := mem_primeWindow.mp hp
    have hprev : q ^ (1 / t) ≤ reboxingAlpha q Δ t ((j : ℝ) + 1 - 1) := by
      simp only [add_sub_cancel_right]
      simpa only [reboxingAlpha_zero] using hm (show (0 : ℝ) ≤ j by positivity)
    have ha1 := (one_lt_rpow hq (one_div_pos.mpr (by linarith : 0 < t))).trans_le hprev
    have hpwin : reboxingAlpha q Δ t ((j : ℝ) + 1 - 1) ≤ p := by
      simpa only [add_sub_cancel_right] using hh.2.2.1
    have hu := reboxing_parameter_bounds hq hΔ (hD d hd).1 (hD d hd).2 ha1 hpwin hh.2.2.2
    have hux : log (Q / d) / log p - 1 ∈ Set.Icc (1 : ℝ) 10 :=
      ⟨hdom.1.trans hu.1,hu.2.trans hdom.2.2.2⟩
    have hp4 := hlarge.trans (hlow.trans (hprev.trans hpwin))
    have hp2 : 2 < p := by exact_mod_cast (show (2 : ℝ) < p by linarith)
    have hupper : (p : ℝ) ≤ (Q / d) ^ (1 / 2 : ℝ) :=
      hh.2.2.2.le.trans (htop.trans
        ((reboxing_support_cutoff_bounds (rpow_nonneg hNpos.le (1 / 2 - δ)) hΔ0 hV
          (show 0 < s by linarith) hd).1.trans
            (window_geometry hb (by omega) hη hδ hd hs hst ht).2))
    have hc := wu_inserted_theta_upper_coefficient (show 0 < N by omega) (hb.support_pos hd)
      hh.1 hp2 hh.2.1 (hb.support_geometry (by omega) hη hδ hd).2.2.1 hupper
      (hf0 _ ⟨hdom.1,hdom.2.1⟩) (hf ⟨hdom.1,hdom.2.1⟩ hux hu.1)
    simpa only [b,F,Q,W,mul_left_comm] using
      mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (convolutionCoeff W d))
  apply hblock.trans_eq
  rw [← reboxingAlpha_convolution_sum_partition hq0 hΔ N r W (fun d p => b d * F d p)]
  unfold shiftedPrime
  congr 1
  simp only [b,F,W,q,Q,mul_sum]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro p _
  ring

theorem shifted_boundary_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, (∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11) →
      ∀ t : ℝ, 2 ≤ t → t ≤ 10 →
      shiftedBoundary f N δ Δ V t ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let α := η / 20
  let K := 2 + (m : ℝ)
  let B := 2 * K / α + 2
  have hα : 0 < α := by dsimp [α]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T0,h0⟩ := reboxing_short_prime_mass hα hK
  obtain ⟨T1,hT14,h1⟩ := scale m hη hδ
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  obtain ⟨T3,h3⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop (by decide : 5 ≠ 0)).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (44 * B / ε)))
  refine ⟨max T1 (max T0 (max T2 T3)),hT14.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb f hfb t ht ht10
  obtain ⟨hΔ,hL,hqlo,hq,_,hmesh⟩ := h1 N (by omega) i Δ V hb
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let Y := q ^ (1 / t)
  let Z := fun d : ℕ => (Q / d) ^ (1 / t)
  let g := fun d p : ℕ => f (log (Q / d) / log p - 1)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqpos : 0 < q := by dsimp [q,Q]; linarith
  have hΔpos : 0 < Δ := by linarith
  have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hNpos η).trans_le (hb.endpoint_lower l)
  have hD := fun d hd => reboxing_support_level_bounds (rpow_nonneg hNpos.le (1 / 2 - δ))
    hΔpos hV (N := N) (d := d) hd
  have hr : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
      q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
    constructor
    · simp only [Nat.cast_zero,reboxingAlpha_zero,le_refl]
    · simpa [reboxingAlpha] using mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hqpos (1 / t))
  have hend := terminal_geometry hb (by omega) hη hL hqlo ht le_rfl ht10 hr
  simp only [Nat.cast_zero,reboxingAlpha_zero] at hend
  have hheight := h2 N (by omega)
  simp only [Function.comp_apply] at hheight
  have hprime (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      (∑ p ∈ primeWindow N Y (Z d),
        |g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))|) ≤
        44 * B / log (N : ℝ) ^ (5 : ℕ) := by
    have hsp := hb.support_geometry (by omega) hη hδ hd
    have hmass := h0 N (by omega) Y (Z d) hend.1 (hend.2 d hd).1 (hend.2 d hd).2
    have hZ := (window_geometry hb (by omega) hη hδ hd ht le_rfl ht10).2
    calc
      _ ≤ 4 * 11 * ∑ p ∈ primeWindow N Y (Z d), (1 : ℝ) / p := by
        apply reboxing_prime_absolute_term_sum_le (g d) hsp.2.2.1
          (hheight.trans hend.1) hZ (by norm_num)
        intro p hp
        have hh := mem_primeWindow.mp hp
        exact hfb _ (reboxingLowerNormalization_parameter_mem hq hΔ ht le_rfl ht10
          (hD d hd).1 (hD d hd).2 hmesh hh.2.2.1 hh.2.2.2)
      _ ≤ 4 * 11 * (B / log (N : ℝ) ^ (5 : ℕ)) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = _ := by ring
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower (by omega)))
  have hfinite : shiftedBoundary f N δ Δ V t ≤
      (44 * B / log (N : ℝ) ^ (5 : ℕ)) * boxTheta N Q W := by
    unfold shiftedBoundary boxTheta
    rw [mul_left_comm (44 * B / log (N : ℝ) ^ (5 : ℕ))]
    apply mul_le_mul_of_nonneg_left _ hli
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    simpa only [g,Y,Z,q,Q,W,wuLocalCutoff,mul_comm] using
      mul_le_mul_of_nonneg_left (hprime d hd) (roughBox_theta_weight hb (by omega) hη hδ hd)
  have hpay : 44 * B / log (N : ℝ) ^ (5 : ℕ) ≤ ε := by
    have hL0 : 0 < log (N : ℝ) := by linarith
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_le_iff₀ he).mp (h3 N (by omega))
    simp only [Function.comp_apply] at hh
    nlinarith only [hh]
  exact hfinite.trans (mul_le_mul_of_nonneg_right hpay (theta_nonneg hb (by omega) hη hδ))

end Wu18938Campaign.M1.Confirmed.Rebox
