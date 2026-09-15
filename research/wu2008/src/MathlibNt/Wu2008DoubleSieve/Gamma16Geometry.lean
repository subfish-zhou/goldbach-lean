import MathlibNt.Wu2008DoubleSieve.Gamma16Multiplicity
import MathlibNt.Wu2008DoubleSieve.Omega3CofactorGeometry

/-! # Whole-support geometry, including profiles with empty last-prime fibres -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem gamma16_profile_geometry {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) {c : Gamma16Profile}
    (hc : c ∈ gamma16Profiles N δ (convolutionWuWindows N Δ V)) :
    0 < gamma16Cofactor c ∧ gamma16Cofactor c ≤ N ∧
      (gamma16Cofactor c).Coprime N ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ gamma16Cofactor c ∧
      (gamma16Cofactor c : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
      2 ≤ c.2.1 ∧
      (c.2.1 : ℝ) ≤ min ((N : ℝ) / gamma16Cofactor c) (wuLocalCutoff N δ c.1 (5 / 2)) ∧
      (gamma16Cofactor c : ℝ) *
        min ((N : ℝ) / gamma16Cofactor c) (wuLocalCutoff N δ c.1 (5 / 2)) ≤ N ∧
      ∀ j : Fin 3, (gamma16Selected c j).Prime ∧
        gamma16Selected c j ∣ gamma16Cofactor c ∧
        (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (gamma16Selected c j : ℝ) := by
  rcases c with ⟨d, p3, p2, p1, n⟩
  obtain ⟨hd, h3, h2, h1, _, hn, hsize, _⟩ := mem_gamma16Profiles.mp hc
  have hw := wu_buchstab_prime_window_bounds hN hδ hδhi hb
    (s := 5 / 2) (t := 291 / 100) (by norm_num) (by norm_num) (by norm_num) hd
  have h1' := mem_primeWindow.mp h1
  have h2' := mem_primeWindow.mp h2
  have h3' := mem_primeWindow.mp h3
  have hepos : 0 < gamma16Cofactor ⟨d, p3, p2, p1, n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hw.1 hn) h1'.1.pos)
      h2'.1.pos) h3'.1.pos
  have heposr : (0 : ℝ) < gamma16Cofactor ⟨d, p3, p2, p1, n⟩ := by exact_mod_cast hepos
  have heN := (Nat.le_mul_of_pos_right _ h3'.1.pos).trans hsize
  have hlow := hw.2.2.2.1.trans h3'.2.2.1
  have hp3e : p3 ≤ gamma16Cofactor ⟨d, p3, p2, p1, n⟩ :=
    Nat.le_mul_of_pos_left p3
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hw.1 hn) h1'.1.pos) h2'.1.pos)
  have hsizeR : (gamma16Cofactor ⟨d, p3, p2, p1, n⟩ : ℝ) * p3 ≤ N := by
    exact_mod_cast hsize
  refine ⟨hepos, heN, gamma16_cofactor_coprime (fun d hd =>
    convolutionCoeff_coprime (fun j p hp => (mem_convolutionWuWindows.mp hp).2.1)
      (mem_boxConvolutionSupport.mp hd)) hc,
    hlow.trans (by exact_mod_cast hp3e), omega3_cofactor_power_gap (by omega) hlow hsize,
    h3'.1.two_le, le_min ((le_div_iff₀ heposr).mpr (by simpa only [mul_comm] using hsizeR))
      h3'.2.2.2.le, ?_, ?_⟩
  · have hu := (le_div_iff₀ heposr).mp
      (min_le_left ((N : ℝ) / gamma16Cofactor ⟨d, p3, p2, p1, n⟩)
        (wuLocalCutoff N δ d (5 / 2)))
    simpa only [mul_comm] using hu
  · intro j
    fin_cases j
    · exact ⟨h1'.1, ⟨d * n * p2 * p3, by dsimp [gamma16Selected, gamma16Cofactor]; ring⟩,
        hw.2.2.2.1.trans h1'.2.2.1⟩
    · exact ⟨h2'.1, ⟨d * n * p1 * p3, by dsimp [gamma16Selected, gamma16Cofactor]; ring⟩,
        hw.2.2.2.1.trans h2'.2.2.1⟩
    · exact ⟨h3'.1, ⟨d * n * p1 * p2, by dsimp [gamma16Selected, gamma16Cofactor]; ring⟩,
        hlow⟩

theorem gamma16_cofactor_rough {i N : ℕ} {δ Y : ℝ} {W : Fin i → Finset ℕ}
    (hd : ∀ d ∈ boxConvolutionSupport W, ∀ q, q.Prime → q ∣ d → Y ≤ (q : ℝ))
    (hl : ∀ d ∈ boxConvolutionSupport W, Y ≤ wuLocalCutoff N δ d (291 / 100))
    {c : Gamma16Profile} (hc : c ∈ gamma16Profiles N δ W) :
    ∀ q, q.Prime → q ∣ gamma16Cofactor c → Y ≤ (q : ℝ) := by
  rcases c with ⟨d, p3, p2, p1, n⟩
  obtain ⟨hdW, h3, h2, h1, _, _, _, hg⟩ := mem_gamma16Profiles.mp hc
  have h1' := mem_primeWindow.mp h1
  have h2' := mem_primeWindow.mp h2
  have h3' := mem_primeWindow.mp h3
  have hn (q : ℕ) (hq : q.Prime) (hqn : q ∣ n) : Y ≤ (q : ℝ) := by
    by_cases he1 : q = p1
    · exact he1 ▸ (hl d hdW).trans h1'.2.2.1
    by_cases he2 : q = p2
    · exact he2 ▸ (hl d hdW).trans h2'.2.2.1
    by_contra he
    exact hg.2.2 q hq ((lt_of_not_ge he).trans_le ((hl d hdW).trans h3'.2.2.1))
      he1 he2 hqn
  intro q hq hqe
  have hprime (p : ℕ) (hp : p.Prime) (hlow : Y ≤ (p : ℝ)) (hqp : q ∣ p) :
      Y ≤ (q : ℝ) := by
    have he := (Nat.dvd_prime hp).mp hqp |>.resolve_left hq.ne_one
    exact he ▸ hlow
  rcases hq.dvd_mul.mp hqe with hqe | hqe
  · rcases hq.dvd_mul.mp hqe with hqe | hqe
    · rcases hq.dvd_mul.mp hqe with hqe | hqe
      · exact (hq.dvd_mul.mp hqe).elim (hd d hdW q hq) (hn q hq)
      · exact hprime p1 h1'.1 ((hl d hdW).trans h1'.2.2.1) hqe
    · exact hprime p2 h2'.1 ((hl d hdW).trans h2'.2.2.1) hqe
  · exact hprime p3 h3'.1 ((hl d hdW).trans h3'.2.2.1) hqe

noncomputable def gamma16FibreConstant (k : ℕ) (δ : ℝ) : ℝ :=
  (max 1 (1 / (wuLocalExponent k δ / 10))) ^ (k + 3)

noncomputable def gamma16LayerCount (k : ℕ) (δ : ℝ) : ℕ := ⌈gamma16FibreConstant k δ⌉₊

theorem gamma16_source_fibres (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (∀ e, (∑ c ∈ (gamma16Profiles N δ (convolutionWuWindows N Δ V)).filter
            (fun c => gamma16Cofactor c = e),
          (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)) ≤ gamma16FibreConstant k δ) ∧
        (∀ c ∈ gamma16Profiles N δ (convolutionWuWindows N Δ V),
          ∀ q, q.Prime → q ∣ gamma16Cofactor c →
            (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ)) := by
  obtain ⟨T, hT, hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb
  have hN2 : 2 ≤ N := by omega
  have hW : ∀ j p, p ∈ convolutionWuWindows N Δ V j →
      p.Prime ∧ (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (p : ℝ) :=
    fun j p hp => ⟨(hw N hN i Δ V hb j p hp).1, (hw N hN i Δ V hb j p hp).2.2⟩
  constructor
  · intro e
    by_cases hn : ((gamma16Profiles N δ (convolutionWuWindows N Δ V)).filter
        (fun c => gamma16Cofactor c = e)).Nonempty
    · obtain ⟨c, hc⟩ := hn
      obtain ⟨hc, he⟩ := mem_filter.mp hc
      have hg := gamma16_profile_geometry hN2 hδ hδhi hb hc
      apply gamma16_weighted_fibre_le _ _ hb.1 (by omega) (he ▸ hg.1) (he ▸ hg.2.1)
        (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hW
      · exact fun _ hc => (mem_filter.mp hc).2
      · intro c hc j
        obtain ⟨hc, he⟩ := mem_filter.mp hc
        have hg := (gamma16_profile_geometry hN2 hδ hδhi hb hc).2.2.2.2.2.2.2.2 j
        exact ⟨hg.1, he ▸ hg.2.1, hg.2.2⟩
    · rw [not_nonempty_iff_eq_empty.mp hn, sum_empty]
      exact pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) _
  · intro c hc
    apply gamma16_cofactor_rough (fun d hd q hq hqd =>
      omega3_support_prime_lower _ hW hd hq hqd) (fun d hd => ?_) hc
    exact (wu_buchstab_prime_window_bounds hN2 hδ hδhi hb
      (s := 5 / 2) (t := 291 / 100) (by norm_num) (by norm_num) (by norm_num) hd).2.2.2.1

end Wu2008DoubleSieve