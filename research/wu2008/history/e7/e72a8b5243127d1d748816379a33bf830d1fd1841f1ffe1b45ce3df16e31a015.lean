import MathlibNt.Wu2008DoubleSieve.Gamma16MassErrors

/-! # The actual X16 main-mass approximation, with no mass-estimate premise -/

namespace Wu2008DoubleSieve

open Finset Set Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem gamma16_buchstab_sum_identity {N d : ℕ} {δ : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / d) :
    (∑ p ∈ gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d),
      gamma16MassScale N d p * buchstab (log (gamma16MassScale N d p) / log p.2.2.2) / log p.2.2.2) =
      (N : ℝ) / (d * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        gamma16PrimeKernelSum ((N : ℝ) ^ (1 / 2 - δ) / d) (omega3XPhi N d δ) := by
  rw [gamma16PrimeKernelSum, mul_sum]
  apply sum_congr rfl
  intro p hp
  have h := gamma16_mass_prime_bounds (by linarith) hp
  have hl3 := (log_pos (by exact_mod_cast h.2.2.2.1.one_lt : (1 : ℝ) < p.2.2.2)).ne'
  have hlR := (log_pos hR).ne'
  rw [gamma16_mass_log_identity hN hd hR hp]
  unfold gamma16MassScale gamma16Kernel
  generalize log ((N : ℝ) ^ (1 / 2 - δ) / d) = L at hlR ⊢
  generalize buchstab
    ((omega3XPhi N d δ - log p.2.1 / L - log p.2.2.1 / L - log p.2.2.2 / L - log p.1 / L) /
      (log p.2.2.2 / L)) = B
  field_simp [hlR, hl3]

theorem gamma16_mass_fibre_main (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (∑ p ∈ gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d),
          ((gamma16MassNFibre N d p).card : ℝ)) ≤
        (N : ℝ) / (d * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
          gamma16FourthIntegral (omega3XPhi N d δ) +
        ε * (N : ℝ) / (d * log N) := by
  let lam := wuLocalExponent k δ
  let η := lam / 10
  have hlam : 0 < lam := wuLocalExponent_pos k hδ hδhi
  have hη : 0 < η := by dsimp [η]; positivity
  let eQ := ε * lam / 3
  let eB := ε * η / 1875
  have heQ : 0 < eQ := by dsimp [eQ]; positivity
  have heB : 0 < eB := by dsimp [eB]; positivity
  obtain ⟨TQ, _, hTQ⟩ := gamma16_source_quadrature k hδ hδhi heQ
  obtain ⟨TB, _, hTB⟩ := gamma16_buchstab_uniform k hδ hδhi heB
  obtain ⟨TE, hTE⟩ := eventually_atTop.mp
    (omega3_repeated_scalar_budget hη (show 0 < ε / 3750 by positivity))
  refine ⟨max 4 (max TQ (max TB TE)), le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hg := omega3XPhi_source_bounds hN2 hδ hδhi hb hd
  have hd0 := (wu_buchstab_prime_window_bounds hN2 hδ hδhi hb
    (by norm_num : (2 : ℝ) ≤ 5 / 2) (by norm_num : (5 / 2 : ℝ) ≤ 291 / 100)
    (by norm_num : (291 / 100 : ℝ) ≤ 10) hd).1
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hR : 1 < R := hg.2.1
  have hlogR : 0 < log R := log_pos hR
  have hLR : lam * log N ≤ log R := by
    have h := log_le_log (rpow_pos_of_pos hNr _) hg.1
    rwa [log_rpow hNr] at h
  obtain ⟨hm, hq⟩ := hTQ N (by omega) i Δ V hb d hd
  have hgeom (p) (hp : p ∈ gamma16MassPrimes R) :=
    gamma16_mass_geometry hN2 hδ hδhi hb hd hp
  have hrepeat := gamma16_repeated_mass_finite (N := N) (d := d) hR
    (rpow_pos_of_pos hNr η) hm (fun p hp => ⟨(hgeom p hp).2.2.2.2.1, (hgeom p hp).2.2.2.2.2.1⟩)
  have hlogs : ∀ p ∈ gamma16MassPrimes R, η * log N ≤ log (p.2.2.2 : ℝ) := by
    intro p hp
    have h := log_le_log (rpow_pos_of_pos hNr η) (hgeom p hp).2.2.2.2.2.2.1
    rwa [log_rpow hNr] at h
  have herr := gamma16_buchstab_error_mass (N := N) (d := d) hR (mul_pos hη hlog) hm hlogs
  have hrough :
      (∑ p ∈ gamma16MassPrimes R, (roughCount (gamma16MassScale N d p) p.2.2.2 : ℝ)) ≤
      (∑ p ∈ gamma16MassPrimes R,
        gamma16MassScale N d p * buchstab (log (gamma16MassScale N d p) / log p.2.2.2) / log p.2.2.2) +
      eB * (∑ p ∈ gamma16MassPrimes R, gamma16MassScale N d p / log p.2.2.2) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have h := (le_abs_self _).trans (hTB N (by omega) i Δ V hb d hd p hp)
    linarith
  rw [gamma16_buchstab_sum_identity hN0 hd0 hR] at hrough
  have hquad :
      (N : ℝ) / (d * log R) * gamma16PrimeKernelSum R (omega3XPhi N d δ) ≤
      (N : ℝ) / (d * log R) * gamma16FourthIntegral (omega3XPhi N d δ) +
        (ε / 3) * (N : ℝ) / (d * log N) := by
    have hq' : gamma16PrimeKernelSum R (omega3XPhi N d δ) ≤
        gamma16FourthIntegral (omega3XPhi N d δ) + eQ := by
      have hh := (le_abs_self _).trans hq.le
      linarith
    have hp := mul_le_mul_of_nonneg_left hq' (show 0 ≤ (N : ℝ) / (d * log R) by positivity)
    have he : (N : ℝ) / (d * log R) * eQ ≤ (ε / 3) * (N : ℝ) / (d * log N) := by
      calc
        _ ≤ (N : ℝ) / (d * (lam * log N)) * eQ :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left hNr.le (by positivity) (mul_le_mul_of_nonneg_left hLR hdr.le))
            heQ.le
        _ = _ := by dsimp [eQ]; field_simp
    linarith
  have heBpaid : eB * (625 * (N : ℝ) / (d * (η * log N))) =
      (ε / 3) * (N : ℝ) / (d * log N) := by
    dsimp [eB]
    field_simp
    ring
  have hscalar := hTE N (by omega)
  have hcube : 1 ≤ (1 + log (N : ℝ)) ^ 3 := one_le_pow₀ (by linarith)
  have heN : 1250 * (N : ℝ) / (N : ℝ) ^ η ≤ (ε / 3) * ((N : ℝ) / log N) := by
    have hh := mul_le_mul_of_nonneg_left hcube (show 0 ≤ (N : ℝ) / (N : ℝ) ^ η by positivity)
    simp only [mul_one] at hh
    have hh' : (N : ℝ) / (N : ℝ) ^ η ≤ (ε / 3750) * ((N : ℝ) / log N) :=
      hh.trans hscalar
    calc
      _ = 1250 * ((N : ℝ) / (N : ℝ) ^ η) := by ring
      _ ≤ 1250 * ((ε / 3750) * ((N : ℝ) / log N)) :=
        mul_le_mul_of_nonneg_left hh' (by norm_num)
      _ = _ := by ring
  have hepaid : 1250 * (N : ℝ) / (d * (N : ℝ) ^ η) ≤
      (ε / 3) * (N : ℝ) / (d * log N) := by
    calc
      _ = (1250 * (N : ℝ) / (N : ℝ) ^ η) / d := by ring
      _ ≤ ((ε / 3) * ((N : ℝ) / log N)) / d :=
        div_le_div_of_nonneg_right heN hdr.le
      _ = _ := by ring
  have hcount :
      (∑ p ∈ gamma16MassPrimes R, ((gamma16MassNFibre N d p).card : ℝ)) ≤
      (∑ p ∈ gamma16MassPrimes R, (roughCount (gamma16MassScale N d p) p.2.2.2 : ℝ)) +
      (∑ p ∈ gamma16MassPrimes R,
        ((⌊gamma16MassScale N d p / p.2.1⌋₊ : ℝ) + ⌊gamma16MassScale N d p / p.2.2.1⌋₊)) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    exact_mod_cast (by simpa only [Nat.add_assoc] using
      gamma16_mass_fibre_rough (N := N) hd0 (by linarith : 0 ≤ R) hp)
  have hBpaid := mul_le_mul_of_nonneg_left herr heB.le
  rw [heBpaid] at hBpaid
  change (∑ p ∈ gamma16MassPrimes R, ((gamma16MassNFibre N d p).card : ℝ)) ≤
    (N : ℝ) / (d * log R) * gamma16FourthIntegral (omega3XPhi N d δ) +
      ε * (N : ℝ) / (d * log N)
  have he3 : (ε / 3) * (N : ℝ) / (d * log N) +
      (ε / 3) * (N : ℝ) / (d * log N) + (ε / 3) * (N : ℝ) / (d * log N) =
      ε * (N : ℝ) / (d * log N) := by ring
  dsimp only [R] at hquad hcount hBpaid hrepeat ⊢
  linarith only [hrough, hquad, hcount, hBpaid, hrepeat, hepaid, he3]

theorem gamma16_X_main (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        let W := convolutionWuWindows N Δ V
        gamma16X N δ W ≤
          (N : ℝ) * (∑ d ∈ boxConvolutionSupport W,
            (convolutionCoeff W d : ℝ) /
              (d * log ((N : ℝ) ^ (1 / 2 - δ) / d)) * gamma16FourthIntegral (omega3XPhi N d δ)) +
          ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T, hT4, hT⟩ := gamma16_mass_fibre_main k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb
  dsimp only
  apply (gamma16_X_le_mass_count N δ (convolutionWuWindows N Δ V)).trans
  unfold gamma16MassCount boxConvolutionReciprocalMass
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (hT N hN i Δ V hb d hd)
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
  convert h using 1
  ring

end Wu2008DoubleSieve
