import MathlibNt.Wu2008DoubleSieve.Omega3XFiniteReorder
import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeTransport

/-!
# Compact geometry of the actual X prime triples

Wu04, arXiv TeX lines 2215–2238. The closed upper endpoint for the third
prime is retained. Only `d ≥ 1` and the established quotient cutoff bounds
are used; no bound on the square of the whole supported product is needed.
-/

namespace Wu2008DoubleSieve

open Real

/-- The strict gap follows from the actual ordered prime sizes, including
when the largest prime equals the closed upper cutoff. -/
theorem omega3X_log_gap {N d p1 p2 p3 δ : ℝ}
    (hN : 1 < N) (hd : 1 ≤ d) (h1 : 0 < p1) (h2 : 1 < p2)
    (h12 : p1 < p2) (h23 : p2 < p3)
    (h3 : p3 ≤ (N ^ (1 / 2 - δ) / d) ^ (1 / 2 : ℝ))
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    1 + 4 * δ / (1 / 2 - δ) <
      log (N / (d * p1 * p2 * p3)) / log p2 := by
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have h20 : 0 < p2 := by linarith
  have h30 : 0 < p3 := h20.trans h23
  have hc : 0 < 1 / 2 - δ := by linarith
  have hq : 0 < N ^ (1 / 2 - δ) / d := by positivity
  have hlogd : 0 ≤ log d := log_nonneg hd
  have hlog2 : 0 < log p2 := log_pos h2
  have hlog12 : log p1 < log p2 := log_lt_log h1 h12
  have hlog23 : log p2 < log p3 := log_lt_log h20 h23
  have hlog3 := log_le_log h30 h3
  rw [log_rpow hq, log_div (rpow_pos_of_pos hN0 _).ne' hd0.ne',
    log_rpow hN0] at hlog3
  have hlogx : log (N / (d * p1 * p2 * p3)) =
      log N - (log d + log p1 + log p2 + log p3) := by
    rw [log_div hN0.ne' (by positivity), log_mul (by positivity) h30.ne',
      log_mul (by positivity) h20.ne', log_mul hd0.ne' h1.ne']
  have hgap : 2 * δ * log N <
      log (N / (d * p1 * p2 * p3)) - log p2 := by
    rw [hlogx]
    nlinarith
  have hy : 2 * log p2 ≤ (1 / 2 - δ) * log N := by
    nlinarith
  have hratio : (4 * δ / (1 / 2 - δ)) * log p2 ≤ 2 * δ * log N := by
    have hmul :
        (4 * δ / (1 / 2 - δ) * log p2) * (1 / 2 - δ) ≤
          (2 * δ * log N) * (1 / 2 - δ) := by
      calc
        _ = (4 * δ / (1 / 2 - δ) * (1 / 2 - δ)) * log p2 := by ring
        _ = 2 * δ * (2 * log p2) := by rw [div_mul_cancel₀ _ hc.ne']; ring
        _ ≤ 2 * δ * ((1 / 2 - δ) * log N) :=
          mul_le_mul_of_nonneg_left hy (by positivity)
        _ = _ := by ring
    nlinarith
  apply (lt_div_iff₀ hlog2).mpr
  nlinarith

/-- All size and logarithmic bounds are instantiated from literal membership
in the finite majorant's triple set, rather than a supplied analytic domain. -/
theorem omega3X_prime_triple_geometry {i k N d p1 p2 p3 : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hp : (p1, p2, p3) ∈ omega3XPrimes N δ s t d) :
    0 < omega3XScale N d p1 p2 p3 ∧
    (2 : ℝ) ≤ p2 ∧
    (p2 : ℝ) < omega3XScale N d p1 p2 p3 ∧
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p2 ∧
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ omega3XScale N d p1 p2 p3 ∧
    omega3XScale N d p1 p2 p3 ≤ N ∧
    1 + 4 * δ / (1 / 2 - δ) <
      log (omega3XScale N d p1 p2 p3) / log p2 ∧
    log (omega3XScale N d p1 p2 p3) / log p2 ≤
      1 / (wuLocalExponent k δ / 10) := by
  obtain ⟨hp2, hp1, _, hp3, h23, h3s⟩ := mem_omega3XPrimes.mp hp
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have hsp := wu_buchstab_prime_window_bounds hN hδ hδhi hb hs hst ht hd
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hsp.1
  have hd0 : (0 : ℝ) < d := by linarith
  have h10 : (0 : ℝ) < p1 := by exact_mod_cast h1.1.pos
  have h21 : (1 : ℝ) < p2 := by exact_mod_cast h2.1.one_lt
  have h20 : (0 : ℝ) < p2 := by linarith
  have h30 : (0 : ℝ) < p3 := by exact_mod_cast hp3.pos
  have hx : 0 < omega3XScale N d p1 p2 p3 := by unfold omega3XScale; positivity
  have hgap := omega3X_log_gap hN1 hd1 h10 h21 h1.2.2.2
    (by exact_mod_cast h23) (h3s.trans hsp.2.2.2.2) hδ hδhi
  change 1 + 4 * δ / (1 / 2 - δ) <
    log (omega3XScale N d p1 p2 p3) / log p2 at hgap
  have hlog2 : 0 < log (p2 : ℝ) := log_pos h21
  have hc : 0 < 1 / 2 - δ := by linarith
  have hg0 : 0 < 4 * δ / (1 / 2 - δ) := by positivity
  have hxy : (p2 : ℝ) < omega3XScale N d p1 p2 p3 := by
    have hu : 1 < log (omega3XScale N d p1 p2 p3) / log p2 := by linarith
    have hl : log (p2 : ℝ) < log (omega3XScale N d p1 p2 p3) := by
      simpa only [one_mul] using (lt_div_iff₀ hlog2).mp hu
    exact (log_lt_log_iff h20 hx).mp hl
  have hyg : (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p2 :=
    hsp.2.2.2.1.trans h2.2.2.1
  have hden : 1 ≤ (d : ℝ) * p1 * p2 * p3 := by
    have hn : 1 ≤ d * p1 * p2 * p3 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hsp.1 h1.1.pos) h2.1.pos) hp3.pos
    exact_mod_cast hn
  have hxN : omega3XScale N d p1 p2 p3 ≤ N := by
    exact div_le_self hN0.le hden
  have hη : 0 < wuLocalExponent k δ / 10 :=
    div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hlowlog := log_le_log (rpow_pos_of_pos hN0 _) hyg
  rw [log_rpow hN0] at hlowlog
  have hhighlog := log_le_log hx hxN
  have hu : log (omega3XScale N d p1 p2 p3) / log p2 ≤
      1 / (wuLocalExponent k δ / 10) := by
    apply (div_le_iff₀ hlog2).mpr
    calc
      _ ≤ log (N : ℝ) := hhighlog
      _ ≤ log (p2 : ℝ) / (wuLocalExponent k δ / 10) :=
        (le_div_iff₀ hη).mpr (by nlinarith)
      _ = _ := by ring
  exact ⟨hx, by exact_mod_cast h2.1.two_le, hxy, hyg, hyg.trans hxy.le,
    hxN, hgap, hu⟩

end Wu2008DoubleSieve
