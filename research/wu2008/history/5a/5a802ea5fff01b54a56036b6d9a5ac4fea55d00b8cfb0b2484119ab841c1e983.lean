import MathlibNt.Wu2008DoubleSieve.FourthRowMotherPrefixMembers
import MathlibNt.Wu2008DoubleSieve.OmegaTerms
import MathlibNt.Wu2008DoubleSieve.Gamma16Carriers

/-! # Literal ordered source-label carriers for every surviving fourth-row term -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourthRowMotherColour (b c : ℝ) (p : ℕ) : ℕ :=
  if (p : ℝ) < b then 0 else if (p : ℝ) < c then 1 else 2

theorem fourthRowMother_colour_monotone (b c : ℝ) :
    Monotone (fourthRowMotherColour b c) := by
  intro p q hpq
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  unfold fourthRowMotherColour
  split_ifs <;> first | omega | linarith

theorem fourthRowMother_colour_le_two (b c : ℝ) (p : ℕ) :
    fourthRowMotherColour b c p ≤ 2 := by
  unfold fourthRowMotherColour
  split_ifs <;> omega

noncomputable def fourthRowMotherTuples (P : Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | 1 => P.image fun p => [p]
  | 2 => ((P ×ˢ P).filter fun p => p.1 < p.2).image fun p => [p.1, p.2]
  | 3 => (orderedTriples P).image fun p => [p.1, p.2.1, p.2.2]
  | 4 => ((P ×ˢ (P ×ˢ (P ×ˢ P))).filter fun p =>
      p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2).image
        fun p => [p.1, p.2.1, p.2.2.1, p.2.2.2]
  | _ + 5 => ∅

theorem fourthRowMother_tuple_pair {P : Finset ℕ} {p q : ℕ} :
    [p, q] ∈ fourthRowMotherTuples P 2 ↔ p ∈ P ∧ q ∈ P ∧ p < q := by
  simp only [fourthRowMotherTuples, mem_image, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hab⟩, he⟩
    have he' : a = p ∧ b = q := by simpa using he
    obtain ⟨rfl, rfl⟩ := he'
    exact ⟨ha, hb, hab⟩
  · rintro ⟨hp, hq, hpq⟩
    exact ⟨(p, q), ⟨⟨hp, hq⟩, hpq⟩, rfl⟩

theorem fourthRowMother_tuple_triple {P : Finset ℕ} {p q r : ℕ} :
    [p, q, r] ∈ fourthRowMotherTuples P 3 ↔ (p, q, r) ∈ orderedTriples P := by
  simp only [fourthRowMotherTuples, mem_image]
  constructor
  · rintro ⟨⟨a, b, c⟩, ht, he⟩
    have he' : a = p ∧ b = q ∧ c = r := by simpa using he
    obtain ⟨rfl, rfl, rfl⟩ := he'
    exact ht
  · intro h
    exact ⟨(p, q, r), h, rfl⟩

theorem fourthRowMother_tuple_quadruple {P : Finset ℕ} {p q r t : ℕ} :
    [p, q, r, t] ∈ fourthRowMotherTuples P 4 ↔
      p ∈ P ∧ q ∈ P ∧ r ∈ P ∧ t ∈ P ∧ p < q ∧ q < r ∧ r < t := by
  simp only [fourthRowMotherTuples, mem_image, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨a, b, c, d⟩, ⟨⟨ha, hb, hc, hd⟩, hab, hbc, hcd⟩, he⟩
    have he' : a = p ∧ b = q ∧ c = r ∧ d = t := by simpa using he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he'
    exact ⟨ha, hb, hc, hd, hab, hbc, hcd⟩
  · rintro ⟨hp, hq, hr, ht, hpq, hqr, hrt⟩
    exact ⟨(p, q, r, t), ⟨⟨hp, hq, hr, ht⟩, hpq, hqr, hrt⟩, rfl⟩

noncomputable def fourthRowMotherPrefixCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  sourceSieveCarrier N (d * l.prod) (d * (l.take (l.length - 2)).prod * N)
    (l.getD (l.length - 2) 0)

noncomputable def fourthRowMotherPrefixTerm (N d M : ℕ) (a b c f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ fourthRowMotherTuples (primeWindow M a f) cs.length,
    if l.map (fourthRowMotherColour b c) = cs then
      ((fourthRowMotherPrefixCarrier N d l).card : ℝ) else 0

noncomputable def fourthRowMotherSingle (N d M : ℕ) (a u : ℝ) : ℝ :=
  ∑ p ∈ primeWindow M a u, (sourceSieveCount N (d * p) (d * N) a : ℝ)

noncomputable def fourthRowMotherPair (N d M : ℕ) (a u v w : ℝ) : ℝ :=
  ∑ q ∈ primeWindow M v w, ∑ p ∈ primeWindow M a u,
    if p < q then (sourceSieveCount N (d * p * q) (d * N) a : ℝ) else 0

noncomputable def fourthRowMotherNine (N d M : ℕ) (b f : ℝ) : ℝ :=
  ∑ r ∈ primeWindow M b f, ∑ q ∈ primeWindow M b r, ∑ p ∈ primeWindow M b q,
    (sourceSieveCount N (d * p * q * r) (d * p * N) q : ℝ)

noncomputable def fourthRowMotherLocal (N d M : ℕ) (a b c f : ℝ) : ℝ :=
  4 * (sourceSieveCount N d (d * N) a : ℝ) + (sourceSieveCount N d (d * N) b : ℝ) -
    2 * fourthRowMotherSingle N d M a f - fourthRowMotherSingle N d M a c +
    fourthRowMotherPair N d M a c a c + fourthRowMotherPair N d M a b c f +
    fourthRowMotherPrefixTerm N d M a b c f [0, 0] +
    fourthRowMotherPrefixTerm N d M a b c f [0, 1] +
    fourthRowMotherNine N d M b f +
    fourthRowMotherPrefixTerm N d M a b c f [1, 1, 2] +
    fourthRowMotherPrefixTerm N d M a b c f [1, 2, 2] +
    fourthRowMotherPrefixTerm N d M a b c f [0, 1, 2] +
    fourthRowMotherPrefixTerm N d M a b c f [0, 2, 2] +
    fourthRowMotherPrefixTerm N d M a b c f [2, 2, 2, 2]

end Wu2008DoubleSieve
