import U8SmallPrefixLocalRoots
import Mathlib.Data.Nat.Squarefree

noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct

/-- Actual roots in the residue ring, valid for composite moduli too. -/
def residueRootCount (m N a : ℕ) : ℕ :=
  Nat.card {x : ZMod m // x * ((N : ZMod m) - (a : ZMod m) * x) = 0}

/-- CRT transports the polynomial equation itself, not an assumed density. -/
def residueRootCRT (m n N a : ℕ) (h : m.Coprime n) :
    {x : ZMod (m*n) // x*((N : ZMod (m*n))-(a : ZMod (m*n))*x)=0} ≃
    {x : ZMod m // x*((N : ZMod m)-(a : ZMod m)*x)=0} ×
    {x : ZMod n // x*((N : ZMod n)-(a : ZMod n)*x)=0} := by
  let E := ZMod.chineseRemainder h
  refine (Equiv.subtypeEquiv E.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  have he := E.injective.eq_iff (a := x*((N : ZMod (m*n))-(a : ZMod (m*n))*x)) (b := 0)
  simpa [map_mul, map_sub, map_natCast, map_zero, Prod.ext_iff] using he.symm

theorem residueRootCount_mul (m n N a : ℕ) (h : m.Coprime n) :
    residueRootCount (m*n) N a = residueRootCount m N a * residueRootCount n N a := by
  unfold residueRootCount
  rw [Nat.card_congr (residueRootCRT m n N a h), Nat.card_prod]

theorem residueRootCount_one (N a : ℕ) : residueRootCount 1 N a = 1 := by
  unfold residueRootCount
  have : Unique {x : ZMod 1 // x*((N : ZMod 1)-(a : ZMod 1)*x)=0} :=
    { default := ⟨0, by simp⟩, uniq := fun _ => Subsingleton.elim _ _ }
  exact Nat.card_unique

theorem residueRootCount_prime {p : ℕ} [Fact p.Prime] (N a : ℕ) :
    residueRootCount p N a = (localRoots p N a).card := by
  classical
  simp only [residueRootCount, Nat.card_eq_fintype_card, Fintype.card_subtype,
    localRoots]

/-- Multiplicativity over a finite set of distinct actual primes. -/
theorem residueRootCount_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (N a : ℕ) :
    residueRootCount (s.prod id) N a = ∏ p ∈ s, residueRootCount p N a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [residueRootCount_one]
  | @insert p s hp ih =>
    have hpP := hs p (mem_insert_self p s)
    have hsP : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    have hc : p.Coprime (s.prod id) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (hpP.coprime_iff_not_dvd).mpr fun hd =>
        hp ((hsP q hq).eq_one_or_self_of_dvd p hd |>.resolve_left hpP.ne_one ▸ hq)
    rw [prod_insert hp, prod_insert hp, id_eq, residueRootCount_mul p (s.prod id) N a hc, ih hsP]

/-- The squarefree CRT formula; includes the modulus-one endpoint. -/
theorem residueRootCount_squarefree {m : ℕ} (hm : Squarefree m) (N a : ℕ) :
    residueRootCount m N a = ∏ p ∈ m.primeFactors, residueRootCount p N a := by
  nth_rw 1 [← Nat.prod_primeFactors_of_squarefree hm]
  exact residueRootCount_prod _ (fun p hp => Nat.prime_of_mem_primeFactors hp) N a

/-- Public canonical density numerator, with no dependence on the pair. -/
def nuN (N m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, if p ∣ N then 1 else 2

theorem small_prime_not_dvd_pair {N p : ℕ} {e : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hp : p.Prime)
    (hsmall : (p : ℝ) < (N : ℝ)^originalAlpha) :
    ¬p ∣ t.1*t.2 := by
  have hd := pairs_data ht
  have hp1 : p < t.1 := by exact_mod_cast hsmall.trans_le hd.2.2.2.1
  have hp2 : p < t.2 := hp1.trans hd.2.2.2.2.2.2.1
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact (ne_of_lt hp1) ((hd.1.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one)
  · exact (ne_of_lt hp2) ((hd.2.1.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one)

/-- Squarefree roots on small-prime support depend only on N. -/
theorem residueRootCount_eq_nuN {N m : ℕ} {e : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hm : Squarefree m)
    (hsmall : ∀ p ∈ m.primeFactors,
      (p : ℝ) < (N : ℝ)^originalAlpha) :
    residueRootCount m N (t.1*t.2) = nuN N m := by
  classical
  rw [residueRootCount_squarefree hm, nuN]
  apply prod_congr rfl
  intro p hp
  have hpP := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpP⟩
  have ha := small_prime_not_dvd_pair ht hpP (hsmall p hp)
  rw [residueRootCount_prime]
  by_cases hN : p ∣ N
  · rw [if_pos hN, localRoots_card_one_of_dvd_N ha hN]
  · rw [if_neg hN, localRoots_card_two ha hN]

/-- CRT and the inherited prime-root theorem give the actual original-pair numerator. -/
theorem residueRootCount_original {N m : ℕ} {e : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hm : Squarefree m) :
    residueRootCount m N (t.1*t.2) =
      ∏ p ∈ m.primeFactors, if p ∣ (t.1*t.2)*N then 1 else 2 := by
  classical
  rw [residueRootCount_squarefree hm]
  apply prod_congr rfl
  intro p hp
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  rw [residueRootCount_prime, localRoots_card_original ht]

theorem sievePrimes_prod_squarefree (Z : ℝ) : Squarefree ((sievePrimes Z).prod id) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (mem_sievePrimes.mp hp).1 (mem_sievePrimes.mp hq).1).mpr hpq
  · intro p hp
    exact (mem_sievePrimes.mp hp).1.squarefree

/-- Legal finite sieve divisors automatically have squarefree CRT moduli. -/
theorem sieve_lcm_squarefree {d f : ℕ} {Z : ℝ}
    (hd : d ∣ (sievePrimes Z).prod id) (hf : f ∣ (sievePrimes Z).prod id) :
    Squarefree (Nat.lcm d f) :=
  (sievePrimes_prod_squarefree Z).squarefree_of_dvd (Nat.lcm_dvd hd hf)

/-- Support transport is proved from actual divisibility in the prime product. -/
theorem small_sieve_rootCount {N m : ℕ} {e Z : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hm : m ∣ (sievePrimes Z).prod id)
    (hZ : Z ≤ (N : ℝ)^originalAlpha) :
    residueRootCount m N (t.1*t.2) = nuN N m := by
  apply residueRootCount_eq_nuN ht ((sievePrimes_prod_squarefree Z).squarefree_of_dvd hm)
  intro p hp
  have hpQ := Nat.primeFactors_mono hm (sievePrimes_prod_ne_zero Z) hp
  have he : ((sievePrimes Z).prod id).primeFactors = sievePrimes Z :=
    Nat.primeFactors_prod fun q hq => (mem_sievePrimes.mp hq).1
  rw [he] at hpQ
  exact (mem_sievePrimes.mp hpQ).2.trans_le hZ

/-- Small support is imposed on D, independently of the original cube-root sieve cutoff. -/
theorem lcm_rootCount_small_support {N d f : ℕ} {e Z : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e)
    (hd : d ∣ (sievePrimes Z).prod id) (hf : f ∣ (sievePrimes Z).prod id)
    (hsd : ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ)^originalAlpha)
    (hsf : ∀ p ∈ f.primeFactors, (p : ℝ) < (N : ℝ)^originalAlpha) :
    residueRootCount (Nat.lcm d f) N (t.1*t.2) = nuN N (Nat.lcm d f) := by
  apply residueRootCount_eq_nuN ht (sieve_lcm_squarefree hd hf)
  intro p hp
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  rcases hpP.dvd_mul.mp (hpd.trans (Nat.lcm_dvd_mul d f)) with h | h
  · exact hsd p (hpP.mem_primeFactors h (ne_zero_of_dvd_ne_zero (sievePrimes_prod_ne_zero Z) hd))
  · exact hsf p (hpP.mem_primeFactors h (ne_zero_of_dvd_ne_zero (sievePrimes_prod_ne_zero Z) hf))

end U8Literal.SmallProduct
