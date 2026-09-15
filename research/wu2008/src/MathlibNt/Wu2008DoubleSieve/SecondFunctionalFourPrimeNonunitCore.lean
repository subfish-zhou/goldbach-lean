import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeUnitFinite

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset
open scoped Classical

/-- Positive divisible complements, excluding precisely the unit quotient. -/
theorem quotient_core {N ell m : ℕ} (hell : ell < N) (hm : 0 < m)
    (hdiv : m ∣ N - ell) (hne : N - ell ≠ m) :
    2 ≤ (N - ell) / m ∧ (N - ell) / m ≤ N ∧
      m * ((N - ell) / m) = N - ell ∧
      N - m * ((N - ell) / m) = ell := by
  have heq := Nat.mul_div_cancel' hdiv
  have hpos : 0 < (N - ell) / m := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at heq
    omega
  have hnot : (N - ell) / m ≠ 1 := by
    intro h
    rw [h, mul_one] at heq
    exact hne heq.symm
  refine ⟨by omega, (Nat.le_mul_of_pos_left _ hm).trans (heq.le.trans (Nat.sub_le _ _)), heq, ?_⟩
  rw [heq]
  omega

theorem carrier_data {N d ell : ℕ} {l : List ℕ}
    (h : ell ∈ secondFunctionalFourPrimeNonunitCarrier N d l) :
    ell ≤ N ∧ ell.Prime ∧ d * l.prod ∣ N - ell ∧ N - ell ≠ d * l.prod := by
  obtain ⟨hs, hn⟩ := mem_filter.mp h
  obtain ⟨hr, hp, hd, _⟩ := mem_filter.mp hs
  exact ⟨Nat.le_of_lt_succ (mem_range.mp hr), hp, hd, hn⟩

theorem carrier_quotient {N d ell : ℕ} {l : List ℕ}
    (hN : 4 ≤ N) (he : Even N) (hm : 0 < d * l.prod)
    (h : ell ∈ secondFunctionalFourPrimeNonunitCarrier N d l) :
    2 ≤ (N - ell) / (d * l.prod) ∧ (N - ell) / (d * l.prod) ≤ N ∧
      d * l.prod * ((N - ell) / (d * l.prod)) = N - ell ∧
      N - d * l.prod * ((N - ell) / (d * l.prod)) = ell := by
  obtain ⟨hle, hp, hd, hn⟩ := carrier_data h
  exact quotient_core (omega3_prime_output_lt hN he hp hle) hm hd hn

/-- The original mask, not modulus one, descends along divisibility. -/
theorem carrier_mask {N d ell p1 p2 p3 p4 : ℕ}
    (h : ell ∈ secondFunctionalFourPrimeNonunitCarrier N d [p1,p2,p3,p4]) :
    Sifted (d * p1 * p2 * N) ((N-ell) / (d * [p1,p2,p3,p4].prod)) p3 := by
  have hs := (mem_filter.mp h).1
  change ell ∈ sourceSieveCarrier N (d * [p1,p2,p3,p4].prod)
    (d * ([p1,p2,p3,p4].take (4-2)).prod * N) p3 at hs
  obtain ⟨_,_,hd,hz⟩ := mem_filter.mp hs
  have heq := Nat.mul_div_cancel' hd
  rw [← heq] at hz
  simpa only [List.take_succ_cons, List.take_zero, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc] using (sifted_mul_iff _ _ _ _).mp hz |>.2

/-- Exact unscaled-to-quotient conversion; the composite prefix needs no coprimality. -/
theorem prefix_quotient_carrier {N d p1 p2 p3 p4 : ℕ}
    (h3 : p3.Prime) (h4 : p4.Prime) (h34 : p3 ≤ p4) :
    secondFunctionalMotherPrefixCarrier N d [p1,p2,p3,p4] =
      sieveCarrier N (d * [p1,p2,p3,p4].prod) (d*p1*p2*N) p3 := by
  have h := source_strict_triple_carrier (N := N) (a := d*p1*p2) h3 h4 h34
  simpa only [secondFunctionalMotherPrefixCarrier, fourthRowMotherPrefixCarrier,
    List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
    List.prod_cons, List.prod_nil, List.getD_cons_succ, List.getD_cons_zero,
    mul_one, mul_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.cast_id,
    show N * (d * (p1 * p2)) = d * (p1 * (p2 * N)) by ring] using h

end Wu2008DoubleSieve.FourPrimeNonunit


