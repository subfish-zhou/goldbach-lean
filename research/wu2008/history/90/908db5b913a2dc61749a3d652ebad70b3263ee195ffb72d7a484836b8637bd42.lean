import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeTransport

/-!
# Uniform source geometry for the labelled switching count

Wu04 (5.3)--(5.4). All prime factors of a source convolution product
are large, including repeated factors and overlapping windows. The support
bound retains the saving delta rather than replacing Q by N.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries

theorem omega3_source_support_le_Q {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) := by
  have h := wu_buchstab_prime_window_bounds (s := 2) (t := 2)
    hN hδ hδhi hb le_rfl le_rfl (by norm_num) hd
  refine ⟨h.1, ?_⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast h.1
  have := (lt_div_iff₀ hd0).mp h.2.2.1
  linarith

theorem omega3_source_window_lower (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ j p, p ∈ convolutionWuWindows N Δ V j →
        p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (convolutionWuWindows_eventually_lower_cutoff (pow_pos hδ (k + 1)))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb j p hp
  have hp' := mem_convolutionWuWindows.mp hp
  refine ⟨hp'.1, hp'.2.1, ?_⟩
  have hη := wuLocalExponent_pos k hδ hδhi
  have hηle : wuLocalExponent k δ / 10 ≤ δ ^ (k + 1) / 2 := by
    have : wuLocalExponent k δ ≤ δ ^ (k + 1) := min_le_left _ _
    linarith
  exact (rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by have := (le_max_left 4 T).trans hN; omega))
    hηle).trans ((hT N ((le_max_right _ _).trans hN) Δ hb.2.1 hb.2.2.1
      (V j) (hb.2.2.2.2.1 j)).trans hp'.2.2.1)

/-- A prime divisor of a product of prime-window labels is one of the
original labels. No factorization uniqueness for the entire tuple is used. -/
theorem omega3_support_prime_lower {i d : ℕ} {Y : ℝ} (W : Fin i → Finset ℕ)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ Y ≤ (p : ℝ))
    (hd : d ∈ boxConvolutionSupport W) {q : ℕ} (hq : q.Prime) (hqd : q ∣ d) :
    Y ≤ (q : ℝ) := by
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hd
  obtain ⟨j, _, hj⟩ := hq.prime.dvd_finsetProd_iff v |>.mp hqd
  have hp := hW j (v j) (Fintype.mem_piFinset.mp hv j)
  have he : q = v j := (Nat.dvd_prime hp.1).mp hj |>.resolve_left hq.ne_one
  simpa only [he] using hp.2

theorem omega3_source_theta_lower {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    2 * liuUniversalProduct * (N : ℝ) / log N ^ 2 *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  apply boxTheta_lower_of_support _ hN
  · intro d hd
    exact (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1
  · intro d hd
    have h := wu_buchstab_prime_window_bounds (s := 2) (t := 2)
      (show 2 ≤ N by omega) hδ hδhi hb le_rfl le_rfl (by norm_num) hd
    refine ⟨h.2.2.1, ?_⟩
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.1
    exact (div_le_self (rpow_nonneg (Nat.cast_nonneg N) _) hd1).trans
      (by
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ N by omega)) (show 1 / 2 - δ ≤ 1 by linarith))

end Wu2008DoubleSieve
