import MathlibNt.Wu2004MeanValue.IndexedSieve
import Mathlib.Data.Finset.Prod

/-!
# Literal small-product triples

The carrier consists of triples `(p,r,q)`, not switched pairs or prime values.
It implements the frozen manuscript's definition of `E_{a,eta}(N)`.
The map to the accepted sigma carrier is proved injective on this carrier.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

def originalTriples (N : ℕ) (a η : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (range (N + 1) ×ˢ (range (N + 1) ×ˢ range (N + 1))).filter
    (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧
      N = t.1 + t.2.1 * t.2.2 ∧ t.2.1 ≤ t.2.2 ∧
      (t.2.2 : ℝ) ^ (a - 1) < t.2.1 ∧ (t.2.1 : ℝ) * t.2.2 ≤ η * N)

def originalTripleCount (N : ℕ) (a η : ℝ) : ℕ :=
  (originalTriples N a η).card

theorem mem_originalTriples {N p r q : ℕ} {a η : ℝ} :
    (p, r, q) ∈ originalTriples N a η ↔
      p.Prime ∧ r.Prime ∧ q.Prime ∧ N = p + r * q ∧ r ≤ q ∧
        (q : ℝ) ^ (a - 1) < r ∧ (r : ℝ) * q ≤ η * N := by
  simp only [originalTriples, mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hr : r ≤ r * q := Nat.le_mul_of_pos_right r h.2.2.1.pos
    have hq : q ≤ r * q := Nat.le_mul_of_pos_left q h.2.1.pos
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

def originalTriplePair (t : ℕ × ℕ × ℕ) : Σ _ : ℕ, ℕ :=
  ⟨t.2.1, t.2.2⟩

theorem originalTriplePair_injOn (N : ℕ) (a η : ℝ) :
    Set.InjOn originalTriplePair (originalTriples N a η : Set (ℕ × ℕ × ℕ)) := by
  rintro ⟨p, r, q⟩ ht ⟨p', r', q'⟩ hu he
  have hr : r = r' := congrArg Sigma.fst he
  have hq : q = q' := congrArg (fun t : Σ _ : ℕ, ℕ => t.2) he
  have htN := (mem_originalTriples.mp ht).2.2.2.1
  have huN := (mem_originalTriples.mp hu).2.2.2.1
  subst r'
  subst q'
  have hp : p = p' := by omega
  subst p'
  rfl

theorem originalTripleCount_eq_card_image (N : ℕ) (a η : ℝ) :
    originalTripleCount N a η =
      ((originalTriples N a η).image originalTriplePair).card :=
  (card_image_of_injOn (originalTriplePair_injOn N a η)).symm

theorem originalTriple_pairValue {N : ℕ} {a η : ℝ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ originalTriples N a η) :
    pairValue N (originalTriplePair t) = t.1 := by
  have he := (mem_originalTriples.mp ht).2.2.2.1
  simp only [pairValue, originalTriplePair, he, Nat.add_sub_cancel]

theorem originalTriple_prime_value_sifted {N : ℕ} {a η z : ℝ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ originalTriples N a η) (hz : z ≤ (1 - η) * N) :
    (pairValue N (originalTriplePair t)).Coprime (siftingProduct N z) := by
  obtain ⟨hp, _, _, hN, _, _, hη⟩ := mem_originalTriples.mp ht
  have hNr : (N : ℝ) = t.1 + (t.2.1 : ℝ) * t.2.2 := by exact_mod_cast hN
  rw [originalTriple_pairValue ht]
  apply prime_coprime_siftingProduct hp
  nlinarith

theorem originalTriple_source_coprime {N : ℕ} {a η : ℝ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ originalTriples N a η) (hη : η < 1 / 2) :
    t.2.1.Coprime N := by
  obtain ⟨hp, hr, hq, hN, _, _, hsmall⟩ := mem_originalTriples.mp ht
  apply hr.coprime_iff_not_dvd.mpr
  intro hd
  have hdp : t.2.1 ∣ t.1 := by
    exact (Nat.dvd_add_iff_left (dvd_mul_right t.2.1 t.2.2)).mpr (hN ▸ hd)
  have hpr : t.2.1 = t.1 := (Nat.prime_dvd_prime_iff_eq hr hp).mp hdp
  have hrprod : t.2.1 ≤ t.2.1 * t.2.2 :=
    Nat.le_mul_of_pos_right _ hq.pos
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (hN ▸ hp.pos.trans_le (Nat.le_add_right t.1 (t.2.1 * t.2.2)))
  have hNle : (N : ℝ) ≤ 2 * ((t.2.1 : ℝ) * t.2.2) := by
    have he : (N : ℝ) = t.1 + (t.2.1 : ℝ) * t.2.2 := by exact_mod_cast hN
    have hp' : (t.2.1 : ℝ) = t.1 := by exact_mod_cast hpr
    have hr' : (t.2.1 : ℝ) ≤ (t.2.1 : ℝ) * t.2.2 := by exact_mod_cast hrprod
    linarith
  nlinarith

def originalTriplesLow (N : ℕ) (a η R : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (originalTriples N a η).filter (fun t => (t.2.1 : ℝ) * t.2.2 ≤ R)

def originalTriplesBlock (H : ℝ) (N : ℕ) (a η : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (originalTriples N a η).filter
    (fun t => H < (t.2.1 : ℝ) * t.2.2 ∧ (t.2.1 : ℝ) * t.2.2 ≤ 2 * H)

def originalTripleBlockCount (H : ℝ) (N : ℕ) (a η : ℝ) : ℕ :=
  (originalTriplesBlock H N a η).card

theorem originalTriple_source_le_sqrt {N : ℕ} {a η X : ℝ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ originalTriples N a η) (hX : (t.2.1 : ℝ) * t.2.2 ≤ X) :
    (t.2.1 : ℝ) ≤ Real.sqrt X := by
  have hrq : (t.2.1 : ℝ) ≤ t.2.2 := by
    exact_mod_cast (mem_originalTriples.mp ht).2.2.2.2.1
  have hX0 : 0 ≤ X := (by positivity : 0 ≤ (t.2.1 : ℝ) * t.2.2).trans hX
  apply (Real.le_sqrt (Nat.cast_nonneg _) hX0).mpr
  nlinarith [mul_le_mul_of_nonneg_left hrq (Nat.cast_nonneg t.2.1)]

theorem originalTriplesLow_card_le {N : ℕ} {a η R : ℝ} (hR : 0 ≤ R) :
    (originalTriplesLow N a η R).card ≤
      (⌊Real.sqrt R⌋₊ + 1) * (⌊R⌋₊ + 1) := by
  let rectangle := range (⌊Real.sqrt R⌋₊ + 1) ×ˢ range (⌊R⌋₊ + 1)
  have hinj : Set.InjOn (fun t : ℕ × ℕ × ℕ => t.2)
      (originalTriplesLow N a η R : Set (ℕ × ℕ × ℕ)) := by
    intro t ht u hu he
    apply originalTriplePair_injOn N a η (mem_filter.mp ht).1 (mem_filter.mp hu).1
    exact congrArg (fun rq : ℕ × ℕ => (⟨rq.1, rq.2⟩ : Σ _ : ℕ, ℕ)) he
  have hmaps : ∀ t ∈ originalTriplesLow N a η R, t.2 ∈ rectangle := by
    intro t ht
    obtain ⟨ht, hprod⟩ := mem_filter.mp ht
    have hsqrt := originalTriple_source_le_sqrt ht hprod
    have hr1 : (1 : ℝ) ≤ t.2.1 := by
      exact_mod_cast (mem_originalTriples.mp ht).2.1.one_lt.le
    have hq : (t.2.2 : ℝ) ≤ R := by
      nlinarith [Nat.cast_nonneg (α := ℝ) t.2.2]
    simpa only [rectangle, mem_product, mem_range, Nat.lt_succ_iff,
      Nat.le_floor_iff (Real.sqrt_nonneg R), Nat.le_floor_iff hR] using
      And.intro hsqrt hq
  have hcard := card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => t.2) hmaps hinj
  simpa only [rectangle, card_product, card_range] using hcard

end
end Wu2004MeanValue
