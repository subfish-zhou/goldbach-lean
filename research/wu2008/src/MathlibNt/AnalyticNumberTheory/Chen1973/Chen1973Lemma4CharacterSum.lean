/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacters
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.Squarefree

/-!
# Chen 1973, Lemma 4: a primitive-character sum

This module follows the statement and proof printed on p. 115 of Chen's original
1973 paper.  The scan states that `k` is odd and squarefree and `m ≠ 1`; its
primitive-root sentence tacitly also needs `(m,k)=1`.  We retain that coprimality
hypothesis explicitly, as required by the source proof.

The proof has two finite layers.  At one prime, the primitive characters are all
characters except the principal character, so orthogonality gives the local
factor `p-2` when `m ≡ 1 (mod p)` and absolute value `1` otherwise.  This module
proves the local layer and final elementary product comparison.  The downstream
module `Chen1973Lemma4CRT` constructs the CRT equivalence, proves the exact
squarefree local-factor product, and discharges the factorization premise.
-/

noncomputable section

open Classical Complex Finset
open scoped BigOperators

namespace AnalyticNumberTheory.LargeSieve

/-- Chen p. 115: `Z(m,k)`, before taking its absolute value. -/
def chen1973Lemma4CharacterSum (k m : ℕ) : ℂ :=
  ∑ χ : PrimitiveCharacter k, χ.1 (m : ZMod k)

/-- The magnitude of Chen's one-prime geometric sum. -/
def chen1973Lemma4LocalMagnitude (p m : ℕ) : ℕ :=
  if p ∣ m - 1 then p - 2 else 1

/-- For an odd prime modulus, primitivity is exactly nonprincipality.  This is
the formal version of the range `1 ≤ ν ≤ p-2` in Chen's proof. -/
theorem chen1973_isPrimitive_iff_ne_one_of_odd_prime
    {p : ℕ} (hp : p.Prime) (_hodd : Odd p)
    (χ : DirichletCharacter ℂ p) :
    χ.IsPrimitive ↔ χ ≠ 1 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro hχ hχone
    have hc : χ.conductor = p := hχ
    rw [hχone, DirichletCharacter.conductor_one] at hc
    exact hp.ne_one hc.symm
  · intro hχ
    have hd : χ.conductor ∣ p := χ.conductor_dvd_level
    have hc : χ.conductor = 1 ∨ χ.conductor = p := (Nat.dvd_prime hp).mp hd
    rcases hc with hc | hc
    · exact False.elim (hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).2 hc))
    · exact hc

/-- The filtered primitive family at an odd prime is `univ.erase 1`. -/
theorem chen1973_primitiveCharacters_prime_eq_erase_one
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    primitiveCharacters p = (Finset.univ.erase (1 : DirichletCharacter ℂ p)) := by
  ext χ
  rw [mem_primitiveCharacters]
  simp [chen1973_isPrimitive_iff_ne_one_of_odd_prime hp hodd χ]

/-- Chen's local geometric sum, written without choosing a primitive root:
all characters give the orthogonality sum, and the principal term is removed. -/
theorem chen1973_prime_characterSum_eq
    {p m : ℕ} (hp : p.Prime) (hodd : Odd p) (hmp : Nat.Coprime m p) :
    chen1973Lemma4CharacterSum p m =
      (if (m : ZMod p) = 1 then (p.totient : ℂ) else 0) - 1 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [chen1973Lemma4CharacterSum]
  rw [show (∑ χ : PrimitiveCharacter p, χ.1 (m : ZMod p)) =
      ∑ χ ∈ primitiveCharacters p, χ (m : ZMod p) from
    sum_primitive_eq_filter (fun χ => χ (m : ZMod p))]
  rw [chen1973_primitiveCharacters_prime_eq_erase_one hp hodd]
  have hone : (1 : DirichletCharacter ℂ p) (m : ZMod p) = 1 := by
    have hu : IsUnit (m : ZMod p) := (ZMod.isUnit_iff_coprime m p).2 hmp
    exact MulChar.one_apply hu
  have herase := Finset.sum_erase_add (Finset.univ : Finset (DirichletCharacter ℂ p))
    (fun χ => χ (m : ZMod p))
    (Finset.mem_univ (1 : DirichletCharacter ℂ p))
  calc
    (∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ p)), χ (m : ZMod p)) =
        (∑ χ : DirichletCharacter ℂ p, χ (m : ZMod p)) -
          (1 : DirichletCharacter ℂ p) (m : ZMod p) := by
      exact eq_sub_of_add_eq herase
    _ = _ := by
      rw [DirichletCharacter.sum_characters_eq]
      rw [hone]

/-- The congruence in the local factor is exactly divisibility of `m-1`. -/
lemma chen1973_natCast_zmod_eq_one_iff
    {p m : ℕ} (_hp : p.Prime) (hm : 0 < m) :
    (m : ZMod p) = 1 ↔ p ∣ m - 1 := by
  rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by norm_num,
    ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    exact (Nat.modEq_iff_dvd' (n := p) (a := 1) (b := m) (by omega)).mp h.symm
  · intro h
    exact ((Nat.modEq_iff_dvd' (n := p) (a := 1) (b := m) (by omega)).mpr h).symm


/-- The product of the prime factors of squarefree `k` which divide `n` is
exactly `gcd k n`. -/
theorem chen1973_prod_selected_primeFactors_eq_gcd
    {k n : ℕ} (hk : Squarefree k) (hn : n ≠ 0) :
    ∏ p ∈ k.primeFactors.filter (· ∣ n), p = k.gcd n := by
  have hk0 : k ≠ 0 := hk.ne_zero
  have hg : Squarefree (k.gcd n) := hk.gcd_left n
  rw [← Nat.prod_primeFactors_of_squarefree hg]
  rw [Nat.primeFactors_gcd hk0 hn]
  congr 1
  ext p
  simp [Nat.mem_primeFactors, hk0, hn]
  tauto

/-- The finite local product in Chen's last displayed calculation is at most
the product of the selected prime divisors. -/
theorem chen1973_localMagnitude_product_le_selected
    (k m : ℕ) :
    (∏ p ∈ k.primeFactors, chen1973Lemma4LocalMagnitude p m) ≤
      ∏ p ∈ k.primeFactors.filter (· ∣ m - 1), p := by
  rw [Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    by_cases hpm : p ∣ m - 1
    · simp only [chen1973Lemma4LocalMagnitude, if_pos hpm]
      exact Nat.sub_le p 2
    · simp [chen1973Lemma4LocalMagnitude, hpm]


end AnalyticNumberTheory.LargeSieve
