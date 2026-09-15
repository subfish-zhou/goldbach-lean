import MathlibNt.Wu2008DoubleSieve.FourthRowMotherCarriers

/-! # First-three distinct-divisor labels and the literal four-prime prefix carrier -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_four_dvd {a b c t n : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (ht : t.Prime)
    (hab : a < b) (hbc : b < c) (hct : c < t) :
    a * b * c * t ∣ n ↔ a ∣ n ∧ b ∣ n ∧ c ∣ n ∧ t ∣ n := by
  have hat := (Nat.coprime_primes ha ht).mpr (ne_of_lt (hab.trans (hbc.trans hct)))
  have hbt := (Nat.coprime_primes hb ht).mpr (ne_of_lt (hbc.trans hct))
  have hct' := (Nat.coprime_primes hc ht).mpr (ne_of_lt hct)
  have hcop : (a * b * c).Coprime t := (hat.mul_left hbt).mul_left hct'
  constructor
  · intro h
    obtain ⟨han, hbn, hcn⟩ := (triple_dvd_iff ha hb hc hab hbc).mp
      ((dvd_mul_right (a * b * c) t).trans h)
    exact ⟨han, hbn, hcn, (dvd_mul_left t (a * b * c)).trans h⟩
  · rintro ⟨han, hbn, hcn, htn⟩
    exact hcop.mul_dvd_of_dvd_of_dvd
      ((triple_dvd_iff ha hb hc hab hbc).mpr ⟨han, hbn, hcn⟩) htn

theorem fourthRowMother_remove_two {M n p q r : ℕ} {a f : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hap : a ≤ (p : ℝ))
    (hpq : p < q) (hqr : q < r) (hrf : (r : ℝ) < f) :
    Sifted (M * p * q) n r ↔
      Sifted M n a ∧
        ∀ t ∈ primeWindow M a f, t < r → t ≠ p → t ≠ q → ¬t ∣ n := by
  have hpr : (p : ℝ) < r := by exact_mod_cast hpq.trans hqr
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  constructor
  · intro h
    constructor
    · intro t ht htM hta
      have htp : t ≠ p := by
        intro he
        subst t
        linarith
      have htq : t ≠ q := by
        intro he
        subst t
        linarith
      exact h t ht ((htM.mul_right ((Nat.coprime_primes ht hp).mpr htp)).mul_right
        ((Nat.coprime_primes ht hq).mpr htq)) (hta.trans (hap.trans_lt hpr))
    · intro t ht htr htp htq
      obtain ⟨htp', htM, _, _⟩ := mem_primeWindow.mp ht
      exact h t htp' ((htM.mul_right ((Nat.coprime_primes htp' hp).mpr htp)).mul_right
        ((Nat.coprime_primes htp' hq).mpr htq)) (by exact_mod_cast htr)
  · rintro ⟨hs, hm⟩ t ht htMpq htr
    obtain ⟨htMp, htq⟩ := Nat.coprime_mul_iff_right.mp htMpq
    obtain ⟨htM, htp⟩ := Nat.coprime_mul_iff_right.mp htMp
    by_cases hta : (t : ℝ) < a
    · exact hs t ht htM hta
    · exact hm t (mem_primeWindow.mpr ⟨ht, htM, le_of_not_gt hta, htr.trans hrf⟩)
        (by exact_mod_cast htr) ((Nat.coprime_primes ht hp).mp htp)
        ((Nat.coprime_primes ht hq).mp htq)

theorem fourthRowMother_quadruple_carrier (N d : ℕ) {a f : ℝ} {p q r t : ℕ}
    (hp : p ∈ primeWindow (d * N) a f) (hq : q ∈ primeWindow (d * N) a f)
    (hr : r ∈ primeWindow (d * N) a f) (ht : t ∈ primeWindow (d * N) a f)
    (hpq : p < q) (hqr : q < r) (hrt : r < t) :
    (sieveCarrier N d (d * N) a).filter
      (fun ell => [p, q, r, t] ∈ fourthRowMotherPrefixes
        (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d)) 4) =
      sourceSieveCarrier N (d * (p * q * r * t)) (d * p * q * N) r := by
  obtain ⟨hpp, _, hap, _⟩ := mem_primeWindow.mp hp
  obtain ⟨hqp, _, _, _⟩ := mem_primeWindow.mp hq
  obtain ⟨hrp, _, _, hrf⟩ := mem_primeWindow.mp hr
  obtain ⟨htp, _, _, _⟩ := mem_primeWindow.mp ht
  have hmod : d * p * q * N = d * N * p * q := by ring
  have hcop (v : ℕ) (hv : v.Coprime (d * N * p * q)) : v.Coprime d :=
    (Nat.coprime_mul_iff_right.mp
      (Nat.coprime_mul_iff_right.mp (Nat.coprime_mul_iff_right.mp hv).1).1).1
  ext ell
  rw [hmod]
  simp only [mem_filter, sieveCarrier, sourceSieveCarrier,
    fourthRowMother_mem_quadruple, divisorsIn, mem_filter]
  constructor
  · rintro ⟨⟨hell, hellp, hd, hs⟩, ⟨_, hpn⟩, ⟨_, hqn⟩, ⟨_, hrn⟩,
      ⟨_, htn⟩, _, _, _, hm⟩
    have hprod := (fourthRowMother_four_dvd hpp hqp hrp htp hpq hqr hrt).mpr
      ⟨hpn, hqn, hrn, htn⟩
    refine ⟨hell, hellp, (Nat.dvd_div_iff_mul_dvd hd).mp hprod, ?_⟩
    apply (sifted_quotient_iff hd (fun v _ hv _ => hcop v hv)).mp
    apply (fourthRowMother_remove_two hpp hqp hap hpq hqr hrf).mpr
    refine ⟨hs, ?_⟩
    intro v hv hvr hvp hvq hvn
    exact (hm v ⟨hv, hvn⟩ hvr).elim hvp hvq
  · rintro ⟨hell, hellp, hdiv, hs⟩
    have hd : d ∣ N - ell := (dvd_mul_right d (p * q * r * t)).trans hdiv
    have hprod := (Nat.dvd_div_iff_mul_dvd hd).mpr hdiv
    obtain ⟨hpn, hqn, hrn, htn⟩ :=
      (fourthRowMother_four_dvd hpp hqp hrp htp hpq hqr hrt).mp hprod
    have hs' := (sifted_quotient_iff hd (fun v _ hv _ => hcop v hv)).mpr hs
    obtain ⟨hsa, hm⟩ := (fourthRowMother_remove_two hpp hqp hap hpq hqr hrf).mp hs'
    refine ⟨⟨hell, hellp, hd, hsa⟩, ⟨hp, hpn⟩, ⟨hq, hqn⟩, ⟨hr, hrn⟩,
      ⟨ht, htn⟩, hpq, hqr, hrt, ?_⟩
    intro v hv hvr
    by_cases hvp : v = p
    · exact Or.inl hvp
    · by_cases hvq : v = q
      · exact Or.inr hvq
      · exact False.elim (hm v hv.1 hvr hvp hvq hv.2)

theorem fourthRowMother_gamma16_output_bounds {N d ell : ℕ} {p : Gamma16Tuple}
    (hN : 4 ≤ N) (he : Even N) (hell : ell ∈ gamma16PrefixCarrier N d p) :
    ∀ j, p j ≤ N := by
  obtain ⟨hrange, hprime, hdiv, _⟩ := mem_filter.mp hell
  have hlt := omega3_prime_output_lt hN he hprime
    (Nat.le_of_lt_succ (mem_range.mp hrange))
  have hdv (j : Fin 4) : p j ∣ d * gamma16Product p := by
    fin_cases j
    · change p 0 ∣ _
      exact ⟨d * p 1 * p 2 * p 3, by unfold gamma16Product; ring⟩
    · change p 1 ∣ _
      exact ⟨d * p 0 * p 2 * p 3, by unfold gamma16Product; ring⟩
    · change p 2 ∣ _
      exact ⟨d * p 0 * p 1 * p 3, by unfold gamma16Product; ring⟩
    · change p 3 ∣ _
      exact ⟨d * p 0 * p 1 * p 2, by unfold gamma16Product; ring⟩
  intro j
  exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) ((hdv j).trans hdiv)).trans (Nat.sub_le N ell)

end Wu2008DoubleSieve
