import MathlibNt.Wu2008DoubleSieve.Gamma16MassCoordinates
import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabUniform

/-! # A single fixed Buchstab cap for every actual four-prime mass fibre -/

namespace Wu2008DoubleSieve

open Finset Set Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem gamma16_mass_geometry {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {p : Gamma16MassTuple}
    (hp : p ∈ gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)) :
    0 < d ∧ 0 < gamma16MassScale N d p ∧ (2 : ℝ) ≤ p.2.2.2 ∧
      (p.2.2.2 : ℝ) < gamma16MassScale N d p ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p.2.1 ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p.2.2.1 ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p.2.2.2 ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ gamma16MassScale N d p ∧
      1 + 5 * δ / (1 / 2 - δ) ≤ log (gamma16MassScale N d p) / log p.2.2.2 ∧
      log (gamma16MassScale N d p) / log p.2.2.2 ≤
        1 / (gamma16Alpha * wuLocalExponent k δ) := by
  have hR := (omega3XPhi_source_bounds hN hδ hδhi hb hd).2.1
  obtain ⟨h4, h1, h2, h3, hlo, h12, h23, _, _⟩ :=
    gamma16_mass_prime_bounds (by linarith) hp
  have hs := wu_buchstab_prime_window_bounds hN hδ hδhi hb
    (by norm_num : (2 : ℝ) ≤ 5 / 2) (by norm_num : (5 / 2 : ℝ) ≤ 291 / 100)
    (by norm_num : (291 / 100 : ℝ) ≤ 10) hd
  have hd0 : 0 < d := hs.1
  have hN0 : 0 < N := by omega
  have hx : 0 < gamma16MassScale N d p := by
    have h10 := h1.pos
    have h20 := h2.pos
    have h30 := h3.pos
    have h40 := h4.pos
    unfold gamma16MassScale
    positivity
  obtain ⟨ht, hu, hv, hw⟩ := gamma16_mass_coordinate_bounds hR hp
  have hg := gamma16_source_argument hN hδ hδhi hb hd ht hu hv hw
  rw [← gamma16_mass_log_identity hN0 hd0 hR hp] at hg
  have hy1 : (1 : ℝ) < p.2.2.2 := by exact_mod_cast h3.one_lt
  have hxy : (p.2.2.2 : ℝ) < gamma16MassScale N d p := by
    have hgap : 0 < 5 * δ / (1 / 2 - δ) := by positivity
    have hu1 : 1 < log (gamma16MassScale N d p) / log p.2.2.2 := by linarith [hg.1]
    have hlog := (lt_div_iff₀ (log_pos hy1)).mp hu1
    apply (log_lt_log_iff (by linarith : (0 : ℝ) < p.2.2.2) hx).mp
    simpa only [one_mul] using hlog
  have hl1 : (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p.2.1 := by
    have hh := hs.2.2.2.1
    rw [(gamma16_cutoffs N d δ).1] at hh
    exact hh.trans hlo
  have hl2 : (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p.2.2.1 :=
    hl1.trans (by exact_mod_cast h12.le)
  have hl3 : (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p.2.2.2 :=
    hl2.trans (by exact_mod_cast h23.le)
  exact ⟨hd0, hx, by exact_mod_cast h3.two_le, hxy, hl1, hl2, hl3,
    hl3.trans hxy.le, hg.1, hg.2⟩

theorem gamma16_buchstab_uniform (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d),
        let x := gamma16MassScale N d p
        let y := (p.2.2.2 : ℝ)
        |(roughCount x y : ℝ) - x * buchstab (log x / log y) / log y| ≤ ε * (x / log y) := by
  let u0 : ℝ := 1 + 2 * δ / (1 / 2 - δ)
  have hu0 : 1 < u0 := by
    have : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    dsimp [u0]
    linarith
  obtain ⟨M, hM⟩ := exists_nat_gt
    (max (1 / (gamma16Alpha * wuLocalExponent k δ)) u0)
  have hMu : u0 < (M : ℝ) := (le_max_right _ _).trans_lt hM
  have hM2 : 2 ≤ M := by
    have : (1 : ℝ) < M := hu0.trans hMu
    have : 1 < M := by exact_mod_cast this
    omega
  obtain ⟨X, _, hX⟩ := roughCount_uniform_buchstab_fixed M hM2 hu0 hε
  have hη : 0 < wuLocalExponent k δ / 10 := by
    exact div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd p hp
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨_, _, hy, hxy, _, _, _, hxg, hug, hub⟩ :=
    gamma16_mass_geometry (by omega) hδ hδhi hb hd hp
  have hxX := (hT N ((le_max_right _ _).trans hN)).trans hxg
  have hu : log (gamma16MassScale N d p) / log p.2.2.2 ∈ Icc u0 (M : ℝ) := by
    refine ⟨?_, hub.trans ((le_max_left _ _).trans hM.le)⟩
    dsimp [u0]
    have hh : 2 * δ / (1 / 2 - δ) ≤ 5 * δ / (1 / 2 - δ) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hy1 : (1 : ℝ) < p.2.2.2 := by linarith
  obtain ⟨_, _, _, hcoord, hnorm⟩ := omega3X_buchstab_coordinates hy1 hxy.le
  obtain ⟨hpos, hrel⟩ := hX _ hxX _ hu
  rw [← hcoord, hnorm] at hrel
  rw [hnorm] at hpos
  let B := gamma16MassScale N d p *
    buchstab (log (gamma16MassScale N d p) / log p.2.2.2) / log p.2.2.2
  have he : (roughCount (gamma16MassScale N d p) p.2.2.2 : ℝ) / B - 1 =
      ((roughCount (gamma16MassScale N d p) p.2.2.2 : ℝ) - B) / B := by
    have hB : B ≠ 0 := hpos.ne'
    field_simp
  change |(roughCount (gamma16MassScale N d p) p.2.2.2 : ℝ) / B - 1| < ε at hrel
  rw [he, abs_div, abs_of_pos hpos] at hrel
  exact ((div_lt_iff₀ hpos).mp hrel).le.trans
    (mul_le_mul_of_nonneg_left (omega3X_buchstab_main_term_bounds hy1 hxy.le).2 hε.le)

end Wu2008DoubleSieve
