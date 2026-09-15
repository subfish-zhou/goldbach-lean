import MathlibNt.Wu2008DoubleSieve.Omega3XFiniteRough
import MathlibNt.Wu2008DoubleSieve.Omega3XErrorBudget

/-!
# Actual closed X is bounded by literal rough counts with a paid exception

Wu04, TeX2215--2238. Only the repeated-p1 error is estimated here.
The actual rough-count majorant is not replaced by a Buchstab main term.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem omega3XPrimes_mem_Icc {N d : ℕ} {δ s t : ℝ} {a : ℕ × ℕ × ℕ}
    (ha : a ∈ omega3XPrimes N δ s t d) :
    a.1 ∈ Icc 1 N ∧ a.2.1 ∈ Icc 1 N ∧ a.2.2 ∈ Icc 1 N := by
  rcases a with ⟨p1, p2, p3⟩
  obtain ⟨h2, h1, h3N, h3, h23, _⟩ := mem_omega3XPrimes.mp ha
  have h12 : p1 < p2 := by exact_mod_cast (mem_primeWindow.mp h1).2.2.2
  exact ⟨mem_Icc.mpr ⟨(mem_primeWindow.mp h1).1.pos, (h12.le.trans h23.le).trans h3N⟩,
    mem_Icc.mpr ⟨(mem_primeWindow.mp h2).1.pos, h23.le.trans h3N⟩,
    mem_Icc.mpr ⟨h3.pos, h3N⟩⟩

theorem omega3XRepeatedMajorant_source_le {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    omega3XRepeatedMajorant N δ s t (convolutionWuWindows N Δ V) ≤
      (((N : ℝ) / (N : ℝ) ^ (wuLocalExponent k δ / 10)) * (1 + log N) ^ 3) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold omega3XRepeatedMajorant omega3XScale
  apply omega3_repeated_weighted_floor_le _ _ (rpow_pos_of_pos hNr _)
  · intro d hd
    exact (omega3_source_support_le_Q hN hδ hδhi hb hd).1
  · intro d _ a ha
    exact omega3XPrimes_mem_Icc ha
  · intro d hd a ha
    rcases a with ⟨p1, p2, p3⟩
    have h1 := (mem_omega3XPrimes.mp ha).2.1
    exact (wu_buchstab_prime_window_bounds hN hδ hδhi hb hs hst ht hd).2.2.2.1.trans
      (mem_primeWindow.mp h1).2.2.1

/-- One fixed threshold precedes every box and every actual ordered triple. -/
theorem omega3XRepeatedMajorant_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        omega3XRepeatedMajorant N δ s t (convolutionWuWindows N Δ V) ≤
          ε * ((N : ℝ) / log N) *
            boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have hη : 0 < wuLocalExponent k δ / 10 := by
    have := wuLocalExponent_pos k hδ hδhi
    positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp (omega3_repeated_scalar_budget hη hε)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hsource := omega3XRepeatedMajorant_source_le
    (show 2 ≤ N by omega) hδ hδhi hb hs hst ht
  have hmass : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  exact hsource.trans
    (mul_le_mul_of_nonneg_right (hT N ((le_max_right _ _).trans hN)) hmass)

/-- Physical raw-X comparison, with the repeated-p1 term actually paid. -/
theorem omega3SieveX_le_rough_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        omega3SieveX N δ s t W ≤ omega3XRoughMajorant N δ s t W +
          ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T, hT4, hT⟩ := omega3XRepeatedMajorant_relative k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hN4 := hT4.trans hN
  exact (omega3SieveX_le_rough_add_repeated N δ s t (convolutionWuWindows N Δ V)
    fun d hd => (omega3_source_support_le_Q (show 2 ≤ N by omega) hδ hδhi hb hd).1).trans
      (add_le_add le_rfl (hT N hN i Δ V hb s t hs hst ht))

end Wu2008DoubleSieve
