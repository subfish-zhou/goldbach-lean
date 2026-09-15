import U8SmallPrefixTwoLinear
import Mathlib.Data.ZMod.Basic

/-! Actual local roots of r(N-p1*p2*r), not an assumed two-dimensional density.
These finite identities do not estimate the Selberg quadratic or its remainder. -/
noncomputable section
open Finset
namespace U8Literal.SmallProduct

/-- Local bad residues for both linear forms simultaneously. -/
def localRoots (p N a : ℕ) [Fact p.Prime] : Finset (ZMod p) := by
  classical
  exact univ.filter fun x => x*((N : ZMod p)-(a : ZMod p)*x)=0

theorem twoLinear_dvd_iff_local {p N r : ℕ} [Fact p.Prime]
    {e : ℝ} {t : ℕ × ℕ} (hr : r ∈ interval N e t) :
    p ∣ twoLinear N t r ↔ (r : ZMod p) ∈ localRoots p N (t.1*t.2) := by
  classical
  have hprod := (mem_filter.mp hr).2.2.1
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [twoLinear, localRoots, mem_filter, mem_univ, true_and]
  rw [Nat.cast_mul, Nat.cast_sub hprod.le]
  simp only [Nat.cast_mul]

/-- For nonvanishing leading coefficient, the roots are exactly 0 and N/a. -/
theorem localRoots_eq_pair {p N a : ℕ} [Fact p.Prime] (ha : ¬p ∣ a) :
    localRoots p N a = {0, (N : ZMod p)/(a : ZMod p)} := by
  classical
  have ha0 : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff a p).mp h)
  ext x
  simp only [localRoots, mem_filter, mem_univ, true_and, mul_eq_zero,
    mem_insert, mem_singleton]
  apply or_congr Iff.rfl
  rw [sub_eq_zero, eq_div_iff ha0]
  constructor <;> intro h <;> simpa only [mul_comm] using h.symm

/-- Exactly two roots away from p dividing aN: this is where dimension two enters. -/
theorem localRoots_card_two {p N a : ℕ} [Fact p.Prime]
    (ha : ¬p ∣ a) (hN : ¬p ∣ N) : (localRoots p N a).card = 2 := by
  classical
  rw [localRoots_eq_pair ha]
  apply card_pair
  have ha0 : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff a p).mp h)
  have hN0 : (N : ZMod p) ≠ 0 := fun h => hN ((ZMod.natCast_eq_zero_iff N p).mp h)
  exact Ne.symm (div_ne_zero hN0 ha0)

/-- If p divides N but not a, the two roots coincide and give one residue. -/
theorem localRoots_card_one_of_dvd_N {p N a : ℕ} [Fact p.Prime]
    (ha : ¬p ∣ a) (hN : p ∣ N) : (localRoots p N a).card = 1 := by
  classical
  rw [localRoots_eq_pair ha, (ZMod.natCast_eq_zero_iff N p).mpr hN]
  simp

/-- If p divides a but not N, only r=0 is excluded. -/
theorem localRoots_eq_singleton_of_dvd_a {p N a : ℕ} [Fact p.Prime]
    (ha : p ∣ a) (hN : ¬p ∣ N) : localRoots p N a = {0} := by
  classical
  have ha0 := (ZMod.natCast_eq_zero_iff a p).mpr ha
  have hN0 : (N : ZMod p) ≠ 0 := fun h => hN ((ZMod.natCast_eq_zero_iff N p).mp h)
  ext x
  simp only [localRoots, mem_filter, mem_univ, true_and, ha0, zero_mul,
    sub_zero, mul_eq_zero, hN0, or_false, mem_singleton]

/-- The original copN masks remove the inadmissible case p dividing both a and N. -/
theorem localRoots_card_original {N p : ℕ} [Fact p.Prime] {e : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) :
    (localRoots p N (t.1*t.2)).card = if p ∣ (t.1*t.2)*N then 1 else 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hcop := (pairs_data ht).2.2.1
  by_cases ha : p ∣ t.1*t.2
  · have hN : ¬p ∣ N := fun hN => hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop ha hN)
    rw [localRoots_eq_singleton_of_dvd_a ha hN, card_singleton, if_pos (dvd_mul_of_dvd_left ha N)]
  · by_cases hN : p ∣ N
    · rw [localRoots_card_one_of_dvd_N ha hN, if_pos (dvd_mul_of_dvd_right hN (t.1*t.2))]
    · rw [localRoots_card_two ha hN, if_neg]
      exact fun h => (hp.dvd_mul.mp h).elim ha hN

/-- Prime-pair membership maps into no bad residue for every legal sieve prime. -/
theorem primePair_avoids_localRoots {N p r : ℕ} [Fact p.Prime] {e Z : ℝ}
    {t : ℕ × ℕ} (ht : t ∈ pairs N e) (hr : r ∈ primePair N e t)
    (hp : p ∈ sievePrimes Z) (hZb : Z ≤ (t.2 : ℝ)) (hZo : Z ≤ (1-e)*(N : ℝ)) :
    (r : ZMod p) ∉ localRoots p N (t.1*t.2) := by
  intro hbad
  have hd := (twoLinear_dvd_iff_local (mem_filter.mp hr).1).mpr hbad
  have hc := primePair_coprime ht hr hZb hZo
  have hpQ : p ∣ (sievePrimes Z).prod id := dvd_prod_of_mem id hp
  exact (show p ≠ 1 from (mem_sievePrimes.mp hp).1.ne_one)
    (Nat.eq_one_of_dvd_coprimes hc hd hpQ)

end U8Literal.SmallProduct
