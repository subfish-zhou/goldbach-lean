import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateProfiles
import MathlibNt.Wu2008DoubleSieve.Omega3R1Layers

/-! # Actual two-colour profiles and the closed last-prime gate -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

def fourthRowTripleGatedWord (ten : Bool) : List ℕ :=
  [if ten then 1 else 0, 1, 2]

noncomputable def fourthRowTripleGatedBand (N : ℕ) (δ : ℝ) (ten : Bool)
    (d p q : ℕ) : Prop :=
  fourthRowMotherColour (wuLocalCutoff N δ d (89 / 25))
    (wuLocalCutoff N δ d (291 / 100)) p = (if ten then 1 else 0) ∧
  fourthRowMotherColour (wuLocalCutoff N δ d (89 / 25))
    (wuLocalCutoff N δ d (291 / 100)) q = 1

noncomputable def fourthRowTripleGatedGate (N d : ℕ) (δ : ℝ) (p : ℕ) : Prop :=
  wuLocalCutoff N δ d (291 / 100) ≤ p

noncomputable def fourthRowTripleGatedProfiles {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (ten : Bool) : Finset Omega3CofactorIndex :=
  (omega3CofactorLabels N δ (5 / 2) (103 / 25) W).filter
    (fun c => fourthRowTripleGatedBand N δ ten c.1 c.2.2.1 c.2.1)

noncomputable def fourthRowTripleGatedFibre (N : ℕ) (δ : ℝ) (c : Omega3CofactorIndex) : Finset ℕ :=
  (omega3CofactorPrimeFibreLE N δ (5 / 2) c).filter (fourthRowTripleGatedGate N c.1 δ)

noncomputable def fourthRowTripleGatedUpper (N : ℕ) (δ : ℝ) (c : Omega3CofactorIndex) : ℝ :=
  min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 (5 / 2))

noncomputable def fourthRowTripleGatedLower (N : ℕ) (δ : ℝ) (c : Omega3CofactorIndex) : ℝ :=
  min (fourthRowTripleGatedUpper N δ c)
    (max (c.2.1 : ℝ) ((⌈wuLocalCutoff N δ c.1 (291 / 100)⌉₊ - 1 : ℕ) : ℝ))

theorem fourthRowTripleGated_colour_one (b c : ℝ) (p : ℕ) :
    fourthRowMotherColour b c p = 1 ↔ b ≤ p ∧ (p : ℝ) < c := by
  unfold fourthRowMotherColour
  split_ifs <;> simp_all

theorem fourthRowTripleGated_word_iff (N d p q r : ℕ) (δ : ℝ) (ten : Bool) :
    [p, q, r].map (fourthRowMotherColour (wuLocalCutoff N δ d (89 / 25))
      (wuLocalCutoff N δ d (291 / 100))) = fourthRowTripleGatedWord ten ↔
      fourthRowTripleGatedBand N δ ten d p q ∧ fourthRowTripleGatedGate N d δ r := by
  simp only [fourthRowTripleGatedWord, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  constructor
  · rintro ⟨hp, hq, hr⟩
    refine ⟨⟨hp, hq⟩, ?_⟩
    have hh := (fourthRowTripleGated_colour_one _ _ _).mp hq
    exact (fourthRowMother_colour_two (hh.1.trans hh.2.le) r).mp hr
  · rintro ⟨⟨hp, hq⟩, hr⟩
    have hh := (fourthRowTripleGated_colour_one _ _ _).mp hq
    exact ⟨hp, hq, (fourthRowMother_colour_two (hh.1.trans hh.2.le) r).mpr hr⟩

theorem fourthRowTripleGated_ceil_gate {H : ℝ} (hH : 0 < H) (p : ℕ) :
    H ≤ p ↔ ((⌈H⌉₊ - 1 : ℕ) : ℝ) < p := by
  rw [← Nat.ceil_le]
  have hc := Nat.ceil_pos.mpr hH
  norm_cast
  omega

theorem fourthRowTripleGated_fibre_profile {N : ℕ} {δ : ℝ} {c : Omega3CofactorIndex}
    (he : 0 < omega3CofactorValue c) (hH : 0 < wuLocalCutoff N δ c.1 (291 / 100)) :
    fourthRowTripleGatedFibre N δ c =
      omega3ProfilePrimes N (fourthRowTripleGatedLower N δ c) (fourthRowTripleGatedUpper N δ c) := by
  have her : (0 : ℝ) < omega3CofactorValue c := by exact_mod_cast he
  ext p
  simp only [fourthRowTripleGatedFibre, fourthRowTripleGatedGate, omega3CofactorPrimeFibreLE,
    omega3ProfilePrimes, mem_filter, mem_range, Nat.lt_succ_iff,
    fourthRowTripleGated_ceil_gate hH]
  have hs : omega3CofactorValue c * p ≤ N ↔
      (p : ℝ) ≤ (N : ℝ) / omega3CofactorValue c := by
    rw [le_div_iff₀ her]
    norm_cast
    rw [Nat.mul_comm]
  have ho : c.2.1 < p ↔ (c.2.1 : ℝ) < p := by norm_cast
  rw [hs, ho]
  simp only [fourthRowTripleGatedLower, fourthRowTripleGatedUpper, min_lt_iff, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hN, hp, hq, hf, heN⟩, hgate⟩
    exact ⟨hN, hp, Or.inr ⟨hq, hgate⟩, heN, hf⟩
  · rintro ⟨hN, hp, hlo, heN, hf⟩
    have hh : ¬min ((N : ℝ) / omega3CofactorValue c) (wuLocalCutoff N δ c.1 (5 / 2)) < p :=
      not_lt.mpr (le_min heN hf)
    obtain ⟨hq, hgate⟩ := hlo.resolve_left (by simpa only [min_lt_iff] using hh)
    exact ⟨⟨hN, hp, hq, hf, heN⟩, hgate⟩

theorem fourthRowTripleGated_geometry {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    {c : Omega3CofactorIndex}
    (hc : c ∈ omega3CofactorLabels N δ (5 / 2) (103 / 25) (convolutionWuWindows N Δ V)) :
    0 < omega3CofactorValue c ∧ 0 < wuLocalCutoff N δ c.1 (291 / 100) ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ omega3CofactorValue c ∧
      (omega3CofactorValue c : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
      2 ≤ fourthRowTripleGatedLower N δ c ∧
      fourthRowTripleGatedLower N δ c ≤ fourthRowTripleGatedUpper N δ c ∧
      (omega3CofactorValue c : ℝ) * fourthRowTripleGatedUpper N δ c ≤ N := by
  have hg := omega3_cofactor_actual_profile_geometry hN hδ hδhi hb
    (by norm_num : (2 : ℝ) ≤ 5 / 2) (by norm_num : (5 / 2 : ℝ) ≤ 103 / 25)
    (by norm_num : (103 / 25 : ℝ) ≤ 10) hc
  obtain ⟨hd, hq, hp, _, hn, _, _⟩ := mem_omega3CofactorLabels.mp hc
  have hd0 := (omega3_source_support_le_Q hN hδ hδhi hb hd).1
  have he : 0 < omega3CofactorValue c :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd0 hn) (mem_primeWindow.mp hp).1.pos)
      (mem_primeWindow.mp hq).1.pos
  have hq2 : (2 : ℝ) ≤ c.2.1 := by exact_mod_cast (mem_primeWindow.mp hq).1.two_le
  have hU : (c.2.1 : ℝ) ≤ fourthRowTripleGatedUpper N δ c := hg.2.2.2.1
  refine ⟨he, ?_, hg.1, hg.2.1, ?_, min_le_left _ _, hg.2.2.2.2.2.2⟩
  · unfold wuLocalCutoff
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hdr : (0 : ℝ) < c.1 := by exact_mod_cast hd0
    positivity
  · exact le_min (hq2.trans hU) (hq2.trans (le_max_left _ _))

end Wu2008DoubleSieve
