import MathlibNt.Wu2008DoubleSieve.ReboxingGeometric
import MathlibNt.Wu2008DoubleSieve.PhiBuchstab

/-!
# Actual support and replacement parameters

Wu04 source lines 1003--1012 and 1046--1065. Both support inequalities
are obtained from the literal convolution tuples, not postulated.
The negative index in `s₂` is interpreted in the real numbers.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem reboxing_support_product_bounds {i N d : ℕ} {Δ : ℝ} {V : Fin i → ℝ}
    (hΔ : 0 < Δ) (hV : ∀ j, 0 ≤ V j)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ (∏ j, V j) / Δ ^ i ≤ (d : ℝ) ∧ (d : ℝ) ≤ ∏ j, V j := by
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hd
  have hv' := Fintype.mem_piFinset.mp hv
  refine ⟨prod_pos (fun j _ => (mem_convolutionWuWindows.mp (hv' j)).1.pos), ?_, ?_⟩
  · rw [Nat.cast_prod]
    have hp : (∏ j, V j / Δ) ≤ ∏ j, (v j : ℝ) :=
      prod_le_prod (fun j _ => div_nonneg (hV j) hΔ.le)
        (fun j _ => (mem_convolutionWuWindows.mp (hv' j)).2.2.1)
    simpa [prod_div_distrib] using hp
  · rw [Nat.cast_prod]
    exact prod_le_prod (fun j _ => Nat.cast_nonneg _)
      (fun j _ => (mem_convolutionWuWindows.mp (hv' j)).2.2.2.le)

theorem reboxing_support_level_bounds {i N d : ℕ} {Q Δ : ℝ} {V : Fin i → ℝ}
    (hQ : 0 ≤ Q) (hΔ : 0 < Δ) (hV : ∀ j, 0 < V j)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    Q / (∏ j, V j) ≤ Q / d ∧
      Q / d ≤ (Q / (∏ j, V j)) * Δ ^ i := by
  obtain ⟨hd0, hlo, hhi⟩ := reboxing_support_product_bounds hΔ (fun j => (hV j).le) hd
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hprod : 0 < ∏ j, V j := prod_pos (fun j _ => hV j)
  constructor
  · exact div_le_div_of_nonneg_left hQ hd0' hhi
  · calc
      _ ≤ Q / ((∏ j, V j) / Δ ^ i) :=
        div_le_div_of_nonneg_left hQ (div_pos hprod (pow_pos hΔ _)) hlo
      _ = _ := by field_simp

/-- The actual moving cutoffs lie above the common box cutoffs, and
their full excess is bounded by the actual power `Δ^(i/s)`. -/
theorem reboxing_support_cutoff_bounds {i N d : ℕ} {Q Δ s : ℝ} {V : Fin i → ℝ}
    (hQ : 0 ≤ Q) (hΔ : 0 < Δ) (hV : ∀ j, 0 < V j) (hs : 0 < s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    (Q / (∏ j, V j)) ^ (1 / s) ≤ (Q / d) ^ (1 / s) ∧
      (Q / d) ^ (1 / s) ≤ (Q / (∏ j, V j)) ^ (1 / s) * Δ ^ ((i : ℝ) / s) := by
  have hh := reboxing_support_level_bounds hQ hΔ hV hd
  have hq : 0 ≤ Q / (∏ j, V j) := div_nonneg hQ (prod_nonneg (fun j _ => (hV j).le))
  constructor
  · exact rpow_le_rpow hq hh.1 (by positivity)
  · calc
      _ ≤ ((Q / (∏ j, V j)) * Δ ^ i) ^ (1 / s) :=
        rpow_le_rpow (div_nonneg hQ (Nat.cast_nonneg _)) hh.2 (by positivity)
      _ = _ := by
        rw [mul_rpow hq (pow_nonneg hΔ.le _), ← rpow_natCast, ← rpow_mul hΔ.le]
        congr 1
        ring

noncomputable def reboxingS1 (q Δ t j : ℝ) : ℝ :=
  log (q / reboxingAlpha q Δ t j) / log (reboxingAlpha q Δ t j)

noncomputable def reboxingS2 (q Δ t i j : ℝ) : ℝ :=
  log (q / reboxingAlpha q Δ t (j - i - 1)) /
    log (reboxingAlpha q Δ t (j - 1))

theorem reboxingAlpha_log {q Δ t j : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) :
    log (reboxingAlpha q Δ t j) = log q / t + j * log Δ := by
  rw [reboxingAlpha, log_mul (rpow_pos_of_pos hq _).ne' (rpow_pos_of_pos hΔ _).ne',
    log_rpow hq, log_rpow hΔ]
  ring

theorem reboxingS1_formula {q Δ t j : ℝ} (hq : 0 < q) (hΔ : 0 < Δ)
    (ha : 1 < reboxingAlpha q Δ t j) :
    reboxingS1 q Δ t j = log q / log (reboxingAlpha q Δ t j) - 1 := by
  rw [reboxingS1, log_div hq.ne' (reboxingAlpha_pos hq hΔ).ne', sub_div,
    div_self (log_pos ha).ne']

/-- This identity retains the negative-index contribution `i*log Δ`. -/
theorem reboxingS2_formula {q Δ t i j : ℝ} (hq : 0 < q) (hΔ : 0 < Δ)
    (ha : 1 < reboxingAlpha q Δ t (j - 1)) :
    reboxingS2 q Δ t i j =
      (log q + i * log Δ) / log (reboxingAlpha q Δ t (j - 1)) - 1 := by
  rw [reboxingS2, log_div hq.ne' (reboxingAlpha_pos hq hΔ).ne']
  have he : log (reboxingAlpha q Δ t (j - i - 1)) =
      log (reboxingAlpha q Δ t (j - 1)) - i * log Δ := by
    rw [reboxingAlpha_log hq hΔ, reboxingAlpha_log hq hΔ]
    ring
  rw [he]
  field_simp [(log_pos ha).ne']
  ring

/-- Pointwise replacement bounds on an actual geometric window. -/
theorem reboxing_parameter_bounds {q D Δ t j : ℝ} {i : ℕ}
    (hq : 1 < q) (hΔ : 1 < Δ)
    (hDlo : q ≤ D) (hDhi : D ≤ q * Δ ^ i)
    (hlo : 1 < reboxingAlpha q Δ t (j - 1))
    {p : ℝ} (hp : reboxingAlpha q Δ t (j - 1) ≤ p)
    (hp' : p < reboxingAlpha q Δ t j) :
    reboxingS1 q Δ t j ≤ log D / log p - 1 ∧
      log D / log p - 1 ≤ reboxingS2 q Δ t i j := by
  have hq0 : 0 < q := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hD0 : 0 < D := hq0.trans_le hDlo
  have hp1 : 1 < p := hlo.trans_le hp
  have ha1 : 1 < reboxingAlpha q Δ t j := hp1.trans hp'
  have hLp : 0 < log p := log_pos hp1
  have hLa : 0 < log (reboxingAlpha q Δ t (j - 1)) := log_pos hlo
  have hLD : 0 ≤ log D := (log_pos (hq.trans_le hDlo)).le
  have hLqD := log_le_log hq0 hDlo
  have hLpA := log_le_log (by linarith : 0 < p) hp'.le
  have hLAp := log_le_log (reboxingAlpha_pos hq0 hΔ0) hp
  have hLDhi : log D ≤ log q + (i : ℝ) * log Δ := by
    have hh := log_le_log hD0 hDhi
    simpa [log_mul hq0.ne' (pow_pos hΔ0 i).ne', log_pow] using hh
  rw [reboxingS1_formula hq0 hΔ0 ha1, reboxingS2_formula hq0 hΔ0 hlo]
  constructor
  · have h1 := div_le_div_of_nonneg_left (log_pos hq).le hLp hLpA
    have h2 := div_le_div_of_nonneg_right hLqD hLp.le
    linarith
  · have h1 := div_le_div_of_nonneg_left hLD hLa hLAp
    have h2 := div_le_div_of_nonneg_right hLDhi hLa.le
    linarith

/-- Scalar domain estimate; the only mesh condition is a logarithmic
inequality, subsequently produced uniformly from the legal source boxes. -/
theorem reboxing_parameter_domain {q Δ s t j : ℝ} {i : ℕ}
    (hq : 1 < q) (hΔ : 1 < Δ) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hj : 1 ≤ j) (hα : reboxingAlpha q Δ t j ≤ q ^ (1 / s))
    (hmesh : 10 * (i : ℝ) * log Δ ≤ log q) :
    1 ≤ reboxingS1 q Δ t j ∧ reboxingS1 q Δ t j ≤ 10 ∧
      1 ≤ reboxingS2 q Δ t i j ∧ reboxingS2 q Δ t i j ≤ 10 := by
  have hq0 : 0 < q := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hbase : 1 < reboxingAlpha q Δ t 0 := by
    rw [reboxingAlpha_zero]
    exact one_lt_rpow hq (by positivity)
  have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
  have hprev : 1 < reboxingAlpha q Δ t (j - 1) :=
    hbase.trans_le (hm (by linarith))
  have hcur : 1 < reboxingAlpha q Δ t j :=
    hbase.trans_le (hm (by linarith))
  have hLcur := log_pos hcur
  have hLprev := log_pos hprev
  have hl : log (reboxingAlpha q Δ t j) ≤ log q / s := by
    have hh := log_le_log (reboxingAlpha_pos hq0 hΔ0) hα
    simpa [log_rpow hq0, div_eq_mul_inv, mul_comm] using hh
  have hlo : 1 ≤ reboxingS1 q Δ t j := by
    rw [reboxingS1_formula hq0 hΔ0 hcur]
    have hh : 2 ≤ log q / log (reboxingAlpha q Δ t j) := by
      apply (le_div_iff₀ hLcur).2
      have := (le_div_iff₀ hs0).1 hl
      nlinarith
    linarith
  have hcomp : reboxingS1 q Δ t j ≤ reboxingS2 q Δ t i j := by
    rw [reboxingS1_formula hq0 hΔ0 hcur, reboxingS2_formula hq0 hΔ0 hprev]
    have hlog := log_le_log (reboxingAlpha_pos hq0 hΔ0) (hm (by linarith : j - 1 ≤ j))
    have h1 := div_le_div_of_nonneg_left (log_pos hq).le hLprev hlog
    have h2 : log q / log (reboxingAlpha q Δ t (j - 1)) ≤
        (log q + (i : ℝ) * log Δ) / log (reboxingAlpha q Δ t (j - 1)) :=
      div_le_div_of_nonneg_right (by nlinarith [log_pos hΔ]) hLprev.le
    linarith
  have hhi : reboxingS2 q Δ t i j ≤ 10 := by
    rw [reboxingS2_formula hq0 hΔ0 hprev]
    have hden : log q / 10 ≤ log (reboxingAlpha q Δ t (j - 1)) := by
      rw [reboxingAlpha_log hq0 hΔ0]
      have hh := div_le_div_of_nonneg_left (log_pos hq).le ht0 ht
      nlinarith [log_pos hΔ]
    have hh : (log q + (i : ℝ) * log Δ) /
        log (reboxingAlpha q Δ t (j - 1)) ≤ 11 := by
      apply (div_le_iff₀ hLprev).2
      nlinarith
    linarith
  exact ⟨hlo, hcomp.trans hhi, hlo.trans hcomp, hhi⟩

/-- A single threshold, chosen after fixed `k,δ`, controls all mesh
parameters and all source-box endpoints. It has no coefficient dependence. -/
theorem reboxing_parameter_mesh_eventually (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        1 < Δ ∧ 1 < (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j) ∧
          10 * (i : ℝ) * log Δ ≤
            log ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) := by
  have ha : 0 < δ ^ (k + 1) := pow_pos hδ _
  have hlim : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_ge_atTop (max 1 (20 * (k : ℝ) / δ ^ (k + 1)))))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hL := hT N ((le_max_right _ _).trans hN)
  have hL1 : 1 ≤ log (N : ℝ) := (le_max_left _ _).trans hL
  have hL0 : 0 < log (N : ℝ) := by linarith
  have hΔ : 1 < Δ := by
    have hp := rpow_pos_of_pos hL0 (-4 : ℝ)
    linarith [hb.2.1]
  have hΔ3 : Δ ≤ 3 := by
    have hp := rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num : (-4 : ℝ) ≤ 0)
    linarith [hb.2.2.1]
  have hlogΔ : log Δ ≤ 2 := by
    have hh := log_le_sub_one_of_pos (by linarith : 0 < Δ)
    linarith
  have hqlo := reboxing_box_level_ge_lower (show 2 ≤ N by omega) hδ hδhi hb
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hq1 := (one_lt_rpow hN1 ha).trans_le hqlo
  have hlogq := log_le_log (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _) hqlo
  rw [log_rpow (by linarith : (0 : ℝ) < N)] at hlogq
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hb.1
  have hlarge := (div_le_iff₀ ha).1 ((le_max_right _ _).trans hL)
  refine ⟨hΔ, hq1, ?_⟩
  nlinarith [show (0 : ℝ) ≤ i by positivity]

end Wu2008DoubleSieve
