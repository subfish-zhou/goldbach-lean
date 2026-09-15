import MathlibNt.Wu2008DoubleSieve.Omega3LayerBounded
import MathlibNt.Wu2008DoubleSieve.Omega3ClosedEnlargement

/-!
# Literal lower and upper profiles on the common layers

The selected label retains d and p2. Its real endpoints are p2 and
min(N/e,z_d), also when the prime interval is empty. All bounds follow from
actual label membership, never from the existence of a prime in the interval.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def omega3LayerLower (L : Finset Omega3CofactorIndex) (j e : ℕ) : ℝ :=
  (omega3LayerLabel L j e).2.1

noncomputable def omega3LayerUpper (N : ℕ) (δ s : ℝ)
    (L : Finset Omega3CofactorIndex) (j e : ℕ) : ℝ :=
  min ((N : ℝ) / e) (wuLocalCutoff N δ (omega3LayerLabel L j e).1 s)

theorem omega3_cofactor_actual_profile_geometry {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    {c : Omega3CofactorIndex}
    (hc : c ∈ omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)) :
    let e := (omega3CofactorValue c : ℝ)
    let lower := (c.2.1 : ℝ)
    let upper := min ((N : ℝ) / e) (wuLocalCutoff N δ c.1 s)
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ e ∧
    e ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ lower ∧
    lower ≤ upper ∧
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ upper ∧
    e * lower ≤ N ∧ e * upper ≤ N := by
  rcases c with ⟨d, p2, p1, n⟩
  obtain ⟨hd, h2, h1, _, hn, hsize, _⟩ := mem_omega3CofactorLabels.mp hc
  have hw := wu_buchstab_prime_window_bounds hN hδ hδhi hb hs hst ht hd
  have hp1 := (mem_primeWindow.mp h1).1.pos
  have hp2 := (mem_primeWindow.mp h2).1.pos
  have hp2lower : (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ p2 :=
    hw.2.2.2.1.trans (mem_primeWindow.mp h2).2.2.1
  have hepos : 0 < omega3CofactorValue ⟨d, p2, p1, n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hw.1 hn) hp1) hp2
  have heposr : (0 : ℝ) < omega3CofactorValue ⟨d, p2, p1, n⟩ := by
    exact_mod_cast hepos
  have hp2e : p2 ≤ omega3CofactorValue ⟨d, p2, p1, n⟩ :=
    Nat.le_mul_of_pos_left p2 (Nat.mul_pos (Nat.mul_pos hw.1 hn) hp1)
  have hsizeR : (omega3CofactorValue ⟨d, p2, p1, n⟩ : ℝ) * p2 ≤ N := by
    exact_mod_cast hsize
  have hlower : (p2 : ℝ) ≤ min ((N : ℝ) / omega3CofactorValue ⟨d, p2, p1, n⟩)
      (wuLocalCutoff N δ d s) := by
    apply le_min
    · exact (le_div_iff₀ heposr).mpr (by simpa only [mul_comm] using hsizeR)
    · exact (mem_primeWindow.mp h2).2.2.2.le
  refine ⟨hp2lower.trans (by exact_mod_cast hp2e),
    omega3_cofactor_power_gap (by omega) hp2lower hsize,
    hp2lower, hlower, hp2lower.trans hlower, hsizeR, ?_⟩
  have hu := (le_div_iff₀ heposr).mp
    (min_le_left ((N : ℝ) / omega3CofactorValue ⟨d, p2, p1, n⟩)
      (wuLocalCutoff N δ d s))
  simpa only [mul_comm] using hu

/-- The closed enlargement is exactly the interval used by the profiles;
neither coprimality to N nor a nonempty prime interval is imposed. -/
theorem omega3Layer_prime_fibre_iff {N : ℕ} {δ s : ℝ}
    {L : Finset Omega3CofactorIndex} {j e p : ℕ}
    (he : e ∈ omega3LayerSupport L j) (hepos : 0 < e) :
    p ∈ omega3CofactorPrimeFibreLE N δ s (omega3LayerLabel L j e) ↔
      p.Prime ∧ omega3LayerLower L j e < p ∧
        (p : ℝ) ≤ omega3LayerUpper N δ s L j e := by
  have hvalue := (omega3LayerLabel_mem he).2
  have her : (0 : ℝ) < e := by exact_mod_cast hepos
  simp only [omega3CofactorPrimeFibreLE, mem_filter, mem_range, Nat.lt_succ_iff,
    omega3LayerLower, omega3LayerUpper, le_min_iff, hvalue]
  constructor
  · rintro ⟨_, hp, hlow, hhigh, hsize⟩
    refine ⟨hp, by exact_mod_cast hlow, ?_, hhigh⟩
    apply (le_div_iff₀ her).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using hsize : p * e ≤ N)
  · rintro ⟨hp, hlow, hsize, hhigh⟩
    have hsizeN : e * p ≤ N := by
      have h := (le_div_iff₀ her).mp hsize
      exact_mod_cast (by simpa only [mul_comm] using h : (e : ℝ) * p ≤ N)
    exact ⟨(Nat.le_mul_of_pos_left p hepos).trans hsizeN, hp,
      by exact_mod_cast hlow, hhigh, hsizeN⟩

theorem omega3Layer_actual_geometry {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    {j e : ℕ}
    (he : e ∈ omega3LayerSupport
      (omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)) j) :
    let L := omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ e ∧
    (e : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ omega3LayerLower L j e ∧
    omega3LayerLower L j e ≤ omega3LayerUpper N δ s L j e ∧
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ omega3LayerUpper N δ s L j e ∧
    (e : ℝ) * omega3LayerLower L j e ≤ N ∧
    (e : ℝ) * omega3LayerUpper N δ s L j e ≤ N := by
  have hlabel := omega3LayerLabel_mem he
  have hg := omega3_cofactor_actual_profile_geometry hN hδ hδhi hb hs hst ht hlabel.1
  simpa only [hlabel.2, omega3LayerLower, omega3LayerUpper] using hg

/-- A test may retain d as well as e and both endpoints. No endpoint is
recovered from e alone, and the chosen layers remain independent of the test. -/
theorem omega3Layer_profile_sum {i : ℕ} (N : ℕ) (δ s : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B) (F : ℕ → ℕ → ℝ → ℝ → ℝ) :
    (∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
      F c.1 (omega3CofactorValue c) c.2.1
        (min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 s))) =
      ∑ j ∈ range B, ∑ e ∈ omega3LayerSupport L j,
        omega3LayerCoefficient W L j e *
          F (omega3LayerLabel L j e).1 e (omega3LayerLower L j e)
            (omega3LayerUpper N δ s L j e) := by
  rw [omega3Layer_weighted_sum W L B hB]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro e he
  simp only [(omega3LayerLabel_mem he).2, omega3LayerLower, omega3LayerUpper]

end Wu2008DoubleSieve
