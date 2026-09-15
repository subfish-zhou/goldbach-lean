import Wu18938Campaign.M1.Confirmed.RoughBox
import MathlibNt.Wu2008DoubleSieve.ReboxingParameterWidth

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter
open scoped Classical Topology

theorem mesh_log {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hL : 1 ≤ log (N : ℝ)) :
    1 < Δ ∧ log Δ ≤ 2 / log (N : ℝ) ^ (4 : ℕ) ∧ Δ ≤ 3 := by
  have hL0 : 0 < log (N : ℝ) := by linarith
  have hp : log (N : ℝ) ^ (-4 : ℝ) = 1 / log (N : ℝ) ^ (4 : ℕ) := by
    rw [rpow_neg hL0.le]
    norm_num
  have hlo := hb.ratio_lower
  have hhi := hb.ratio_upper
  rw [hp] at hlo hhi
  have hΔ : 1 < Δ := by
    have : 0 < 1 / log (N : ℝ) ^ (4 : ℕ) := by positivity
    linarith
  have hl := log_le_sub_one_of_pos (show 0 < Δ by linarith)
  have hp1 : 1 ≤ log (N : ℝ) ^ (4 : ℕ) := one_le_pow₀ hL
  have hinv : 1 / log (N : ℝ) ^ (4 : ℕ) ≤ 1 := by
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  rw [mul_one_div] at hhi
  have htwo : 2 / log (N : ℝ) ^ (4 : ℕ) ≤ 2 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  exact ⟨hΔ,by linarith,by linarith⟩

theorem scale (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      1 < Δ ∧ 1 ≤ log (N : ℝ) ∧
      (N : ℝ) ^ (η / 2) ≤ (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j) ∧
      1 < (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j) ∧
      (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j) ≤ N ∧
      10 * (i : ℝ) * log Δ ≤ log ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) := by
  obtain ⟨c,hc,T0,hT04,hθ⟩ := roughBox_theta_lower m hη hδ
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (half_pos hη)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop ((3 : ℝ) ^ m)))
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 1 (40 * (m : ℝ) / η))))
  simp only [Function.comp_apply] at h1 h2
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hL := (le_max_left _ _).trans (h2 N (by omega))
  have hM := (le_max_right _ _).trans (h2 N (by omega))
  have hm := mesh_log hb hL
  have hV : ∀ j, 0 < V j := fun j => (rpow_pos_of_pos hN0 η).trans_le (hb.endpoint_lower j)
  have hne : (boxConvolutionSupport (convolutionWuWindows N Δ V)).Nonempty := by
    by_contra hn
    have he : boxConvolutionSupport (convolutionWuWindows N Δ V) = ∅ :=
      not_nonempty_iff_eq_empty.mp hn
    have ht := hθ N (by omega) i Δ V hb
    simp only [boxTheta,he,sum_empty,mul_zero] at ht
    have hpos : 0 < c * (N : ℝ) / log (N : ℝ) ^ (5 * m + 2) := by positivity
    linarith
  obtain ⟨d,hd⟩ := hne
  have hg := reboxing_support_level_bounds (rpow_nonneg hN0.le (1 / 2 - δ))
    (by linarith [hm.1]) hV hd
  have hΔpow : Δ ^ i ≤ (3 : ℝ) ^ m :=
    (pow_le_pow_left₀ (by linarith [hm.1]) hm.2.2 i).trans
      (pow_le_pow_right₀ (by norm_num) hb.depth)
  have hq0 : 0 < (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j) :=
    div_pos (rpow_pos_of_pos hN0 _) (prod_pos (fun j _ => hV j))
  have hpow : (N : ℝ) ^ η = (N : ℝ) ^ (η / 2) * (N : ℝ) ^ (η / 2) := by
    rw [← rpow_add hN0]
    congr 1
    ring
  have hqlo : (N : ℝ) ^ (η / 2) ≤ (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j) := by
    have h := (hb.remaining d hd).trans hg.2
    have hp := hΔpow.trans (h1 N (by omega))
    have hupper := mul_le_mul_of_nonneg_left hp hq0.le
    rw [hpow] at h
    nlinarith [rpow_pos_of_pos hN0 (η / 2)]
  have hq := (one_lt_rpow hNr (half_pos hη)).trans_le hqlo
  have hlog : (η / 2) * log (N : ℝ) ≤
      log ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) := by
    simpa only [log_rpow hN0] using log_le_log (rpow_pos_of_pos hN0 _) hqlo
  have hi : (i : ℝ) ≤ m := by exact_mod_cast hb.depth
  have hlogΔ : log Δ ≤ 2 := by
    have hp1 : 1 ≤ log (N : ℝ) ^ (4 : ℕ) := one_le_pow₀ hL
    exact hm.2.1.trans ((div_le_iff₀ (by positivity)).mpr (by linarith))
  refine ⟨hm.1,hL,hqlo,hq,hg.1.trans (hb.support_geometry (by omega) hη hδ hd).2.2.2,?_⟩
  have hml := (div_le_iff₀ hη).mp hM
  have hbound := mul_le_mul (show 10 * (i : ℝ) ≤ 10 * m by linarith) hlogΔ
    (log_pos hm.1).le (by positivity)
  nlinarith

theorem parameter_width {m i N : ℕ} {η δ Δ t j : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η)
    (hL : 1 ≤ log (N : ℝ))
    (hqlo : (N : ℝ) ^ (η / 2) ≤ (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l))
    (ht : 0 < t) (ht10 : t ≤ 10) (hj : 1 ≤ j) :
    let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
    0 ≤ reboxingS2 q Δ t i j - reboxingS1 q Δ t j ∧
      reboxingS2 q Δ t i j - reboxingS1 q Δ t j ≤
        ((400 + 40 * (m : ℝ)) / η) / log (N : ℝ) ^ (5 : ℕ) := by
  dsimp only
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hm := mesh_log hb hL
  have hq := (one_lt_rpow hNr (half_pos hη)).trans_le hqlo
  have hlog : (η / 2) * log (N : ℝ) ≤
      log ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) := by
    simpa only [log_rpow hN0] using log_le_log (rpow_pos_of_pos hN0 _) hqlo
  have hw := reboxing_parameter_width (i := i) hq hm.1 ht ht10 hj
  have hi : (i : ℝ) ≤ m := by exact_mod_cast hb.depth
  refine ⟨hw.1,hw.2.trans ?_⟩
  calc
    _ ≤ ((100 + 10 * (m : ℝ)) * (2 / log (N : ℝ) ^ (4 : ℕ))) /
        ((η / 2) * log (N : ℝ)) := by
      apply div_le_div₀
      · positivity
      · exact mul_le_mul (by linarith) hm.2.1 (log_pos hm.1).le (by positivity)
      · positivity
      · exact hlog
    _ = _ := by rw [show (5 : ℕ) = 4 + 1 by norm_num,pow_succ]; field_simp; ring

end Wu18938Campaign.M1.Confirmed.Rebox
