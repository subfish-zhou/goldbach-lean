import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitCore
import Wu18938Campaign.M2.RawCount

namespace Wu18938Campaign.M2

open Finset Wu2008DoubleSieve
open scoped Classical

noncomputable def selectedCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  sourceSieveCarrier N (d * l.prod) (d * l.prod * N) (l.getD (l.length - 2) 0)

theorem prefix_eq_selected_append {N d p q : ℕ} (pre : List ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    secondFunctionalMotherPrefixCarrier N d (pre ++ [p, q]) =
      selectedCarrier N d (pre ++ [p, q]) := by
  rw [HighNonunit.prefix_quotient_carrier pre hp hq hpq]
  unfold selectedCarrier
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right _ N)]
  have hs (n : ℕ) :
      Sifted (d * (pre ++ [p, q]).prod * N) n (p : ℝ) ↔
        Sifted (d * pre.prod * N) n (p : ℝ) := by
    rw [show d * (pre ++ [p, q]).prod * N =
      (d * pre.prod * N) * p * q by
        simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one]
        ring,
      sifted_mul_modulus_of_le hq (by exact_mod_cast hpq),
      sifted_mul_modulus_of_le hp le_rfl]
  ext ell
  simp only [sieveCarrier, mem_filter, HighNonunit.get_penultimate, hs]

theorem prefix_eq_selected {N d : ℕ} {l : List ℕ}
    (hlen : 2 ≤ l.length) (hord : l.Pairwise (· < ·))
    (hprime : ∀ p ∈ l, p.Prime) :
    secondFunctionalMotherPrefixCarrier N d l = selectedCarrier N d l := by
  obtain ⟨pre, p, q, rfl⟩ := HighNonunit.split_last_two hlen
  have hpq : p < q := by
    simpa using (List.pairwise_append.mp hord).2.1
  exact prefix_eq_selected_append pre (hprime p (by simp)) (hprime q (by simp)) hpq.le

theorem selected_eq_quotient (N d : ℕ) (l : List ℕ) :
    selectedCarrier N d l =
      sieveCarrier N (d * l.prod) (d * l.prod * N) (l.getD (l.length - 2) 0) :=
  sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right _ N) _

theorem raw_selected_square {N d ell p : ℕ} {l : List ℕ}
    (hp : p.Prime) (hpN : p.Coprime N) (hpl : p ∈ l)
    (hcut : (p : ℝ) < l.getD (l.length - 2) 0)
    (hell : ell ∈ sourceSieveCarrier N (d * l.prod) (d * N)
      (l.getD (l.length - 2) 0)) :
    p ∣ d ∧ p ^ 2 ∣ N - ell := by
  obtain ⟨_, _, hd, hs⟩ := mem_filter.mp hell
  exact raw_prime_forces_square (fun q : ℕ => (q : ℝ) < l.getD (l.length - 2) 0)
    hp hpN (List.dvd_prod hpl) hd hcut hs

theorem raw_labels_selector {N d : ℕ} (l : List ℕ) (z : ℝ)
    (hprime : ∀ p ∈ l, p.Prime) (hcoprime : ∀ p ∈ l, p.Coprime N) :
    Sifted (d * N) (d * l.prod) z ↔
      ∀ p ∈ l, (p : ℝ) < z → p ∣ d :=
  raw_product_selector (fun p : ℕ => (p : ℝ) < z) l hprime hcoprime

theorem raw_squarefree_empty {N d : ℕ} {l : List ℕ}
    (hlen : 3 ≤ l.length) (hord : l.Pairwise (· < ·))
    (hprime : ∀ p ∈ l, p.Prime ∧ p.Coprime N) :
    (sourceSieveCarrier N (d * l.prod) (d * N) (l.getD (l.length - 2) 0)).filter
      (fun ell => Squarefree (N - ell)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ell hell
  obtain ⟨hell, hsf⟩ := mem_filter.mp hell
  cases l with
  | nil => simp at hlen
  | cons p l =>
    have hi : l.length - 2 < l.length := by simp only [List.length_cons] at hlen; omega
    have hm : l.getD (l.length - 2) 0 ∈ l := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    have hlt := (List.pairwise_cons.mp hord).1 _ hm
    have hcut : (p : ℝ) < (p :: l).getD ((p :: l).length - 2) 0 := by
      simp only [List.length_cons,
        show l.length + 1 - 2 = (l.length - 2) + 1 by
          simp only [List.length_cons] at hlen; omega,
        List.getD_cons_succ]
      exact_mod_cast hlt
    obtain ⟨hp, hpN⟩ := hprime p (by simp)
    have hs := (raw_selected_square hp hpN (by simp) hcut hell).2
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp (by simpa only [pow_two] using hs)

theorem gamma20_selected_carrier {N d p q r s t : ℕ}
    (hs : s.Prime) (ht : t.Prime) (hst : s ≤ t) :
    secondFunctionalMotherPrefixCarrier N d [p, q, r, s, t] =
      sourceSieveCarrier N (d * (p * q * r * s * t))
        (d * (p * q * r * s * t) * N) s := by
  simpa [selectedCarrier, mul_assoc] using
    prefix_eq_selected_append (N := N) (d := d) [p, q, r] hs ht hst

theorem gamma21_selected_carrier {N d p q r s t u : ℕ}
    (ht : t.Prime) (hu : u.Prime) (htu : t ≤ u) :
    secondFunctionalMotherPrefixCarrier N d [p, q, r, s, t, u] =
      sourceSieveCarrier N (d * (p * q * r * s * t * u))
        (d * (p * q * r * s * t * u) * N) t := by
  simpa [selectedCarrier, mul_assoc] using
    prefix_eq_selected_append (N := N) (d := d) [p, q, r, s] ht hu htu

end Wu18938Campaign.M2
