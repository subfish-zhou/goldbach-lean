import MathlibNt.Wu2008DoubleSieve.Omega3SourceBounds

/-!
# Geometry of strengthened switching cofactors

The strict roughness condition permits p1 and p2 to divide n. Only the
coprimalities actually needed for e to be coprime to N are used.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3_cofactor_prime_lower {d n p1 p2 q : ℕ} {Y : ℝ}
    (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hd : ∀ r, r.Prime → r ∣ d → Y ≤ (r : ℝ))
    (h1 : Y ≤ (p1 : ℝ)) (h2 : Y ≤ (p2 : ℝ))
    (hn : ∀ r : ℕ, r.Prime → (r : ℝ) < p2 → r ≠ p1 → ¬r ∣ n)
    (hq : q.Prime) (hqe : q ∣ d * n * p1 * p2) :
    Y ≤ (q : ℝ) := by
  rcases hq.dvd_mul.mp hqe with h | h
  · rcases hq.dvd_mul.mp h with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · exact hd q hq h
      · by_cases he : q = p1
        · simpa only [he] using h1
        · by_contra hlow
          exact hn q hq ((lt_of_not_ge hlow).trans_le h2) he h
    · have he : q = p1 := (Nat.dvd_prime hp1).mp h |>.resolve_left hq.ne_one
      simpa only [he] using h1
  · have he : q = p2 := (Nat.dvd_prime hp2).mp h |>.resolve_left hq.ne_one
    simpa only [he] using h2

theorem omega3_cofactor_coprime {N d n p1 p2 : ℕ}
    (hd : d.Coprime N) (hn : n.Coprime N)
    (h1 : p1.Coprime N) (h2 : p2.Coprime N) :
    (d * n * p1 * p2).Coprime N :=
  ((hd.mul_left hn).mul_left h1).mul_left h2

theorem omega3_cofactor_power_gap {N e p : ℕ} {η : ℝ}
    (hN : 0 < N) (hp : (N : ℝ) ^ η ≤ p) (hep : e * p ≤ N) :
    (e : ℝ) ≤ (N : ℝ) ^ (1 - η) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < (N : ℝ) ^ η := rpow_pos_of_pos hNr _
  have he : (e : ℝ) * (N : ℝ) ^ η ≤ N := by
    exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg e)).trans (by exact_mod_cast hep)
  rw [rpow_sub hNr, rpow_one]
  exact (le_div_iff₀ hr).mpr he

/-- Uniform cofactor support for every legal source box and both moving
cutoffs. The label's explicit strict roughness condition is preserved. -/
theorem omega3_source_cofactor_geometry (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ (d n p1 p2 : ℕ) (s t : ℝ),
        d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) →
        2 ≤ s → s ≤ t → t ≤ 10 →
        p1 ∈ primeWindow N (wuLocalCutoff N δ d t) (p2 : ℝ) →
        p2 ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) →
        0 < n → n.Coprime N →
        (∀ r : ℕ, r.Prime → (r : ℝ) < p2 → r ≠ p1 → ¬r ∣ n) →
        d * n * p1 * p2 * p2 ≤ N →
        0 < d * n * p1 * p2 ∧ (d * n * p1 * p2).Coprime N ∧
        (d * n * p1 * p2 : ℕ) ≤ N ∧
        (d * n * p1 * p2 : ℕ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
        ∀ r, r.Prime → r ∣ d * n * p1 * p2 →
          (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ r := by
  obtain ⟨T, hT4, hT⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb d n p1 p2 s t hd hs hst ht hp1 hp2 hn hnN hrough hsize
  have hN4 : 4 ≤ N := hT4.trans hN
  have hsp := wu_buchstab_prime_window_bounds (by omega) hδ hδhi hb hs hst ht hd
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have hdN : d.Coprime N :=
    convolutionCoeff_coprime (fun j p hp => (mem_convolutionWuWindows.mp hp).2.1)
      (mem_boxConvolutionSupport.mp hd)
  have hpos : 0 < d * n * p1 * p2 := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hsp.1 hn) h1.1.pos) h2.1.pos
  have heN : d * n * p1 * p2 ≤ N :=
    (Nat.le_mul_of_pos_right _ h2.1.pos).trans hsize
  refine ⟨hpos, omega3_cofactor_coprime hdN hnN h1.2.1 h2.2.1, heN,
    omega3_cofactor_power_gap (by omega) (hsp.2.2.2.1.trans h2.2.2.1) hsize, ?_⟩
  intro r hr hrd
  exact omega3_cofactor_prime_lower h1.1 h2.1
    (fun r hr hrd => omega3_support_prime_lower _ (fun j p hp =>
      ⟨(hT N hN i Δ V hb j p hp).1, (hT N hN i Δ V hb j p hp).2.2⟩) hd hr hrd)
    (hsp.2.2.2.1.trans h1.2.2.1) (hsp.2.2.2.1.trans h2.2.2.1) hrough hr hrd

end Wu2008DoubleSieve
