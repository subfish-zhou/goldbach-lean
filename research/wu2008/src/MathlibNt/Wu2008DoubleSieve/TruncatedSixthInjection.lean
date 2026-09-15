import MathlibNt.Wu2008DoubleSieve.TruncatedSixthCarriers

/-!
# Excess four-prime atoms inject into omitted positive pairs

The prime index is retained by `(a,b,c,d,r) -> (c,d,r)`.
The existing first-two-divisor uniqueness theorem recovers a and b.
Neither squarefreeness nor a multiplicity budget is needed.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem truncatedSixth_first_two {N a b c d r : ℕ} {z w u : ℝ}
    (ht : (a, b, c, d) ∈ s3DistinctQuadruples N (s3SecondRange N z w u))
    (hr : r ∈ sieveCarrier N (a * b * c * d) N (b : ℝ)) :
    (a, b, c) ∈ firstTwoTriples (divisorsIn (primeWindow N z w) (N - r)) := by
  obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, _, _, hab, hbc, hcd, hcw, _⟩ :=
    mem_s3_second_quadruples.mp ht
  obtain ⟨_, _, hD, hs⟩ := mem_filter.mp hr
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
  have han : a ∣ N - r := (((dvd_mul_right a b).trans (dvd_mul_right (a * b) c)).trans
    (dvd_mul_right (a * b * c) d)).trans hD
  have hbn : b ∣ N - r := (((dvd_mul_left b a).trans (dvd_mul_right (a * b) c)).trans
    (dvd_mul_right (a * b * c) d)).trans hD
  have hcn : c ∣ N - r := ((dvd_mul_left c (a * b)).trans
    (dvd_mul_right (a * b * c) d)).trans hD
  apply mem_firstTwoTriples.mpr
  refine ⟨mem_filter.mpr ⟨mem_primeWindow.mpr
      ⟨ha, haN, hza, hab'.trans (hbc'.trans hcw)⟩, han⟩,
    mem_filter.mpr ⟨mem_primeWindow.mpr
      ⟨hb, hbN, hza.trans hab'.le, hbc'.trans hcw⟩, hbn⟩,
    mem_filter.mpr ⟨mem_primeWindow.mpr
      ⟨hc, hcN, (hza.trans hab'.le).trans hbc'.le, hcw⟩, hcn⟩, hab, hbc, ?_⟩
  intro q hq hqb
  obtain ⟨hqwin, hqn⟩ := mem_filter.mp hq
  obtain ⟨hqp, hqN, _, _⟩ := mem_primeWindow.mp hqwin
  by_contra hqa
  have hqD : q.Coprime (a * b * c * d) :=
    Nat.coprime_mul_iff_right.mpr
      ⟨Nat.coprime_mul_iff_right.mpr
        ⟨Nat.coprime_mul_iff_right.mpr
          ⟨(Nat.coprime_primes hqp ha).mpr hqa,
            (Nat.coprime_primes hqp hb).mpr (ne_of_lt hqb)⟩,
          (Nat.coprime_primes hqp hc).mpr (ne_of_lt (hqb.trans hbc))⟩,
        (Nat.coprime_primes hqp hd).mpr (ne_of_lt ((hqb.trans hbc).trans hcd))⟩
  exact hs q hqp hqN (by exact_mod_cast hqb) ((dvd_quotient_iff hD hqD).mpr hqn)

theorem truncatedSixth_pair_carrier {N a b c d r : ℕ} {z w u : ℝ}
    (ht : (a, b, c, d) ∈ s3DistinctQuadruples N (s3SecondRange N z w u))
    (hr : r ∈ sieveCarrier N (a * b * c * d) N (b : ℝ)) :
    r ∈ sieveCarrier N (c * d) N z := by
  obtain ⟨ha, _, hza, hb, _, _, _, _, _, _, hab, _⟩ :=
    mem_s3_second_quadruples.mp ht
  obtain ⟨hrR, hrp, hD, hs⟩ := mem_filter.mp hr
  have hCD : c * d ∣ N - r :=
    (dvd_mul_left (c * d) (a * b)).trans (by simpa only [mul_assoc] using hD)
  have hAB : a * b ∣ (N - r) / (c * d) :=
    (Nat.dvd_div_iff_mul_dvd hCD).mpr (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hD)
  have hzb : z ≤ (b : ℝ) := hza.trans (by exact_mod_cast hab.le)
  have hs' : Sifted N (((N - r) / (c * d)) / (a * b)) z := by
    rw [Nat.div_div_eq_div_mul, show c * d * (a * b) = a * b * c * d by ring]
    exact fun q hq hqN hqz => hs q hq hqN (hqz.trans_le hzb)
  refine mem_filter.mpr ⟨hrR, hrp, hCD, (sifted_quotient_iff hAB ?_).mp hs'⟩
  intro q hq _ hqz
  have hqa : q < a := by exact_mod_cast hqz.trans_le hza
  exact Nat.coprime_mul_iff_right.mpr
    ⟨(Nat.coprime_primes hq ha).mpr (ne_of_lt hqa),
      (Nat.coprime_primes hq hb).mpr (ne_of_lt (hqa.trans hab))⟩

def truncatedSixthAtomMap (x : (_t : ℕ × ℕ × ℕ × ℕ) × ℕ) :
    (_t : ℕ × ℕ) × ℕ :=
  ⟨(x.1.2.2.1, x.1.2.2.2), x.2⟩

theorem truncatedSixthAtomMap_mem {N : ℕ} {z w u V : ℝ}
    {x : (_t : ℕ × ℕ × ℕ × ℕ) × ℕ}
    (hx : x ∈ truncatedSixthExcessAtoms N z w u V) :
    truncatedSixthAtomMap x ∈ truncatedSixthOmittedAtoms N z w u V := by
  rcases x with ⟨⟨a, b, c, d⟩, r⟩
  obtain ⟨ht, hr⟩ := mem_sigma.mp hx
  obtain ⟨ht, hV⟩ := mem_filter.mp ht
  obtain ⟨_, _, hza, _, _, hc, hcN, hd, hdN, hdu, hab, hbc, _, hcw, hwd⟩ :=
    mem_s3_second_quadruples.mp ht
  apply mem_sigma.mpr
  refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, hV⟩,
    truncatedSixth_pair_carrier ht hr⟩
  · exact mem_primeWindow.mpr
      ⟨hc, hcN, hza.trans (by exact_mod_cast (hab.trans hbc).le), hcw⟩
  · exact mem_primeWindow.mpr ⟨hd, hdN, hwd, hdu⟩

theorem truncatedSixthAtomMap_injOn (N : ℕ) (z w u V : ℝ) :
    Set.InjOn truncatedSixthAtomMap (truncatedSixthExcessAtoms N z w u V) := by
  rintro ⟨⟨a, b, c, d⟩, r⟩ hx ⟨⟨a', b', c', d'⟩, r'⟩ hy heq
  have hcd := congrArg Sigma.fst heq
  have hr := congrArg (fun x : (_t : ℕ × ℕ) × ℕ => x.2) heq
  have hc : c = c' := congrArg Prod.fst hcd
  have hd : d = d' := congrArg Prod.snd hcd
  dsimp only [truncatedSixthAtomMap] at hr
  subst c'; subst d'; subst r'
  obtain ⟨hxT, hxR⟩ := mem_sigma.mp hx
  obtain ⟨hyT, hyR⟩ := mem_sigma.mp hy
  have hfirst := truncatedSixth_first_two (mem_filter.mp hxT).1 hxR
  have hsecond := truncatedSixth_first_two (mem_filter.mp hyT).1 hyR
  obtain ⟨ha, hb⟩ := firstTwoTriples_first_two_unique hfirst hsecond
  subst a'; subst b'
  rfl

/-- Every excess incidence is paid by an actual omitted positive-pair
incidence, with no repeated-prime or squarefree error. -/
theorem truncatedSixth_excess_le_omitted (N : ℕ) (z w u V : ℝ) :
    truncatedSixthExcessMass N z w u V ≤ truncatedSixthOmittedMass N z w u V := by
  rw [← truncatedSixthExcessAtoms_card, ← truncatedSixthOmittedAtoms_card]
  exact_mod_cast card_le_card_of_injOn truncatedSixthAtomMap
    (fun _ hx => truncatedSixthAtomMap_mem hx) (truncatedSixthAtomMap_injOn N z w u V)

end Wu2008DoubleSieve
