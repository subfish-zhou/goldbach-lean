import MathlibNt.Wu2008DoubleSieve.Gamma5GainCell
import MathlibNt.Wu2008DoubleSieve.ReboxingParameter

/-!
# Fixed legal rectangles and uniform whole-old-box coordinate drift
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

structure Gamma5GainRectangle where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  s : ℝ
  lower : gamma5MassA < A
  first : A < B
  ordered : B < C
  second : C < D
  upper : D < gamma5ClassicalB
  legal : D + 2 * B < 1
  rightEnd : gamma5GainV A C < s
  parameter : s < 3

theorem gamma5Gain_rectangle_bounds (r : Gamma5GainRectangle) :
    0 < r.A ∧ 0 < r.C ∧ r.B < 1 ∧ r.D < 1 ∧
      2 * r.D < 1 ∧ 1 < r.s ∧
      gamma5MassA ≤ r.A ∧ r.B ≤ gamma5ClassicalB ∧
      gamma5MassA ≤ r.C ∧ r.D ≤ gamma5ClassicalB := by
  have ha : 0 < gamma5MassA := by norm_num [gamma5MassA, gamma5ClassicalS]
  have hb : 2 * gamma5ClassicalB < 1 := by norm_num [gamma5ClassicalB]
  have hc := r.lower.trans (r.first.trans r.ordered)
  have hs := (gamma5Gain_triangle_bounds (v := (r.A, r.C))
    ⟨r.lower.le, (r.first.trans r.ordered).le, (r.second.trans r.upper).le⟩).2.2.1
  exact ⟨ha.trans r.lower, ha.trans hc, by linarith [r.ordered, r.second, r.upper],
    by linarith [r.upper], by linarith [r.upper], hs.trans r.rightEnd,
    r.lower.le, (r.ordered.trans (r.second.trans r.upper)).le, hc.le, r.upper.le⟩

noncomputable def gamma5GainScale {i : ℕ} (N : ℕ) (δ : ℝ) (V : Fin i → ℝ) : ℝ :=
  (N : ℝ) ^ (1 / 2 - δ) / ∏ j, V j

theorem gamma5Gain_mesh_eventually (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      1 < Δ ∧ 1 < gamma5GainScale N δ V ∧
        ((k : ℝ) + 1) * log Δ / log (gamma5GainScale N δ V) < ε := by
  have ha : 0 < δ ^ (k + 1) := pow_pos hδ _
  have hlog := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun N : ℕ => (2 * ((k : ℝ) + 1) / δ ^ (k + 1)) / log N)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hdecay.eventually (gt_mem_nhds hε)] with N hN hL herr
  intro i Δ V hb
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos hN1
  have hΔ : 1 < Δ := by
    have := rpow_pos_of_pos hLp (-4 : ℝ)
    linarith [hb.2.1]
  have hneg : log (N : ℝ) ^ (-4 : ℝ) ≤ 1 :=
    rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have hld : log Δ ≤ 2 := by
    have := log_le_sub_one_of_pos (by linarith : 0 < Δ)
    linarith [hb.2.2.1]
  have hR := reboxing_box_level_ge_lower hN hδ hδhi hb
  have hR1 : 1 < gamma5GainScale N δ V := (one_lt_rpow hN1 ha).trans_le hR
  have hlR : δ ^ (k + 1) * log (N : ℝ) ≤ log (gamma5GainScale N δ V) := by
    have h := log_le_log (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _) hR
    simpa only [log_rpow (by linarith : (0 : ℝ) < N)] using h
  refine ⟨hΔ, hR1, lt_of_le_of_lt ?_ herr⟩
  calc
    _ ≤ (((k : ℝ) + 1) * 2) / (δ ^ (k + 1) * log N) := by
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hld (by positivity)) (mul_pos ha hLp) hlR
    _ = _ := by ring

theorem gamma5Gain_coordinate_drift {i k N p : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V) {d : ℕ}
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hp : 1 ≤ p) (hpR : (p : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / d) :
    0 ≤ gamma5MassCoordinate (gamma5GainScale N δ V) p -
        gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / d) p ∧
      gamma5MassCoordinate (gamma5GainScale N δ V) p -
        gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / d) p ≤
        (i : ℝ) * log Δ / log (gamma5GainScale N δ V) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hΔ : 1 < Δ := by
    have := rpow_pos_of_pos (log_pos hN1) (-4 : ℝ)
    linarith [hb.2.1]
  have hV : ∀ j, 0 < V j := fun j =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 j)
  have hR0 : 1 < gamma5GainScale N δ V :=
    (one_lt_rpow hN1 (pow_pos hδ _)).trans_le (reboxing_box_level_ge_lower hN hδ hδhi hb)
  have hr := reboxing_support_level_bounds (rpow_nonneg (Nat.cast_nonneg N) _)
    (by linarith : 0 < Δ) hV hd
  have hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / d := hR0.trans_le hr.1
  have hlo := log_le_log (by linarith : 0 < gamma5GainScale N δ V) hr.1
  have hhi := log_le_log (by linarith : 0 < (N : ℝ) ^ (1 / 2 - δ) / d) hr.2
  rw [log_mul (by linarith : gamma5GainScale N δ V ≠ 0)
    (pow_pos (by linarith : 0 < Δ) i).ne', log_pow] at hhi
  have hLp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpL := log_le_log hp0 hpR
  have hL0 := log_pos hR0
  have hL := log_pos hR
  have ht : 0 ≤ log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    div_nonneg hLp hL.le
  have ht1 : log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d) ≤ 1 :=
    (div_le_one hL).mpr hpL
  have he : gamma5MassCoordinate (gamma5GainScale N δ V) p -
      gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / d) p =
      (log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        ((log ((N : ℝ) ^ (1 / 2 - δ) / d) - log (gamma5GainScale N δ V)) /
          log (gamma5GainScale N δ V)) := by
    unfold gamma5MassCoordinate
    field_simp
    ring
  rw [he]
  constructor
  · exact mul_nonneg ht (div_nonneg (sub_nonneg.mpr hlo) hL0.le)
  · calc
      _ ≤ 1 * ((i : ℝ) * log Δ / log (gamma5GainScale N δ V)) :=
        mul_le_mul ht1 (div_le_div_of_nonneg_right (by linarith) hL0.le)
          (div_nonneg (sub_nonneg.mpr hlo) hL0.le) (by norm_num)
      _ = _ := one_mul _

end Wu2008DoubleSieve
