import MathlibNt.Wu2008DoubleSieve.Gamma16MassReorder
import MathlibNt.Wu2008DoubleSieve.Gamma16Kernel

/-! # Exact four-prime logarithmic coordinates, including all closed faces -/

namespace Wu2008DoubleSieve

open Finset Set Real

theorem gamma16_log_coordinate_mem {R A B : ℝ} (hR : 1 < R) {p : ℕ}
    (hp : p.Prime) (hlo : R ^ A ≤ (p : ℝ)) (hhi : (p : ℝ) ≤ R ^ B) :
    log p / log R ∈ Icc A B := by
  have hR0 : 0 < R := by linarith
  have hl := log_le_log (rpow_pos_of_pos hR0 _) hlo
  have hu := log_le_log (by exact_mod_cast hp.pos : (0 : ℝ) < p) hhi
  rw [log_rpow hR0] at hl hu
  exact ⟨(le_div_iff₀ (log_pos hR)).mpr hl, (div_le_iff₀ (log_pos hR)).mpr hu⟩

theorem gamma16_mass_coordinate_bounds {R : ℝ} (hR : 1 < R) {p : Gamma16MassTuple}
    (hp : p ∈ gamma16MassPrimes R) :
    log p.2.1 / log R ∈ Icc gamma16Alpha gamma16Beta ∧
    log p.2.2.1 / log R ∈ Icc gamma16Alpha gamma16Beta ∧
    log p.2.2.2 / log R ∈ Icc gamma16Alpha gamma16Beta ∧
    log p.1 / log R ∈ Icc gamma16Alpha gamma16Beta := by
  obtain ⟨h4, h1, h2, h3, hlo, h12, h23, h34, hhi⟩ :=
    gamma16_mass_prime_bounds (by linarith) hp
  have h12' : (p.2.1 : ℝ) ≤ p.2.2.1 := by exact_mod_cast h12.le
  have h23' : (p.2.2.1 : ℝ) ≤ p.2.2.2 := by exact_mod_cast h23.le
  have h34' : (p.2.2.2 : ℝ) ≤ p.1 := by exact_mod_cast h34
  exact ⟨gamma16_log_coordinate_mem hR h1 hlo (h12'.trans (h23'.trans (h34'.trans hhi))),
    gamma16_log_coordinate_mem hR h2 (hlo.trans h12') (h23'.trans (h34'.trans hhi)),
    gamma16_log_coordinate_mem hR h3 (hlo.trans (h12'.trans h23')) (h34'.trans hhi),
    gamma16_log_coordinate_mem hR h4 (hlo.trans (h12'.trans (h23'.trans h34'))) hhi⟩

theorem gamma16_source_argument {i k N d : ℕ} {δ Δ t u v w : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (ht : t ∈ Icc gamma16Alpha gamma16Beta)
    (hu : u ∈ Icc gamma16Alpha gamma16Beta)
    (hv : v ∈ Icc gamma16Alpha gamma16Beta)
    (hw : w ∈ Icc gamma16Alpha gamma16Beta) :
    1 + 5 * δ / (1 / 2 - δ) ≤ (omega3XPhi N d δ - t - u - v - w) / v ∧
      (omega3XPhi N d δ - t - u - v - w) / v ≤
        1 / (gamma16Alpha * wuLocalExponent k δ) := by
  have hφ := omega3XPhi_source_bounds hN hδ hδhi hb hd
  have hlam := wuLocalExponent_pos k hδ hδhi
  have ha : 0 < gamma16Alpha := by norm_num [gamma16Alpha]
  have hv0 : 0 < v := ha.trans_le hv.1
  have hc : 0 < 1 / 2 - δ := by linarith
  have hg : 0 < δ / (1 / 2 - δ) := div_pos hδ hc
  have hφ0 : 0 ≤ omega3XPhi N d δ := by
    have : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    linarith [hφ.2.2.1]
  constructor
  · apply (le_div_iff₀ hv0).mpr
    have hm := mul_le_mul_of_nonneg_left hv.2 (show 0 ≤ 5 * (δ / (1 / 2 - δ)) by positivity)
    have he : 5 * δ / (1 / 2 - δ) = 5 * (δ / (1 / 2 - δ)) := by ring
    rw [he]
    have he2 : 2 * δ / (1 / 2 - δ) = 2 * (δ / (1 / 2 - δ)) := by ring
    rw [he2] at hφ
    norm_num [gamma16Beta] at hm ht hu hv hw
    nlinarith [hφ.2.2.1]
  · calc
      _ ≤ omega3XPhi N d δ / v :=
        div_le_div_of_nonneg_right (by linarith [ht.1, hu.1, hv.1, hw.1]) hv0.le
      _ ≤ omega3XPhi N d δ / gamma16Alpha := div_le_div_of_nonneg_left hφ0 ha hv.1
      _ ≤ (1 / wuLocalExponent k δ) / gamma16Alpha :=
        div_le_div_of_nonneg_right hφ.2.2.2 ha.le
      _ = _ := by ring

theorem gamma16_mass_log_identity {N d : ℕ} {δ : ℝ} {p : Gamma16MassTuple}
    (hN : 0 < N) (hd : 0 < d)
    (hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / d)
    (hp : p ∈ gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)) :
    log (gamma16MassScale N d p) / log p.2.2.2 =
      (omega3XPhi N d δ -
        log p.2.1 / log ((N : ℝ) ^ (1 / 2 - δ) / d) -
        log p.2.2.1 / log ((N : ℝ) ^ (1 / 2 - δ) / d) -
        log p.2.2.2 / log ((N : ℝ) ^ (1 / 2 - δ) / d) -
        log p.1 / log ((N : ℝ) ^ (1 / 2 - δ) / d)) /
      (log p.2.2.2 / log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
  have h := gamma16_mass_prime_bounds (by linarith) hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h10 : (0 : ℝ) < p.2.1 := by exact_mod_cast h.2.1.pos
  have h20 : (0 : ℝ) < p.2.2.1 := by exact_mod_cast h.2.2.1.pos
  have h30 : (0 : ℝ) < p.2.2.2 := by exact_mod_cast h.2.2.2.1.pos
  have h40 : (0 : ℝ) < p.1 := by exact_mod_cast h.1.pos
  have hlR := (log_pos hR).ne'
  have hl3 := (log_pos (by exact_mod_cast h.2.2.2.1.one_lt : (1 : ℝ) < p.2.2.2)).ne'
  rw [gamma16MassScale, log_div hN0.ne' (by positivity),
    log_mul (by positivity) h40.ne', log_mul (by positivity) h30.ne',
    log_mul (by positivity) h20.ne', log_mul hd0.ne' h10.ne',
    omega3XPhi, log_div hN0.ne' hd0.ne']
  generalize log ((N : ℝ) ^ (1 / 2 - δ) / d) = L at hlR ⊢
  field_simp [hlR, hl3]
  ring

end Wu2008DoubleSieve
