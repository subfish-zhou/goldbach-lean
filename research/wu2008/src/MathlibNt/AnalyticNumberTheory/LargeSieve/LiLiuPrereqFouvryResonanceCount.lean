import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryReciprocalCorrelation
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

/-!
# Finite counting of the genuine zero-numerator branch

Fouvry (1987), pp. 631--632, (4.8)--(4.9). The first beta index `n`
is common to both phases. Frequencies remain integers: no positivity or
same-tuple restriction is imposed on the variable frequency.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem iv3_resonance_equation
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ} (ha : a ≠ 0)
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' = 0) :
    (h * n₂' * s') * ((d₁ : ℤ) * n - n₂) =
      h' * n₂ * s * ((d₁ : ℤ) * n - n₂') := by
  exact sub_eq_zero.mp ((mul_eq_zero.mp hl).resolve_left ha)

/-- Primitivity makes the variable second beta coordinate a divisor of
the fixed signed product, rather than of a product involving itself. -/
theorem iv3_resonance_n₂_dvd
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ} (ha : a ≠ 0)
    (hc : (d₁ * n).Coprime n₂)
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' = 0) :
    n₂ ∣ (h * n₂' * s').natAbs := by
  let P : ℤ := h * n₂' * s'
  have he := iv3_resonance_equation ha hl
  have hd : (n₂ : ℤ) ∣ P * ((d₁ : ℤ) * n - n₂) := by
    refine ⟨h' * s * ((d₁ : ℤ) * n - n₂'), ?_⟩
    dsimp only [P]
    rw [he]
    ring
  have hp : (n₂ : ℤ) ∣ P * (d₁ * n : ℕ) := by
    have heq : P * (d₁ * n : ℕ) =
        P * ((d₁ : ℤ) * n - n₂) + P * n₂ := by push_cast; ring
    rw [heq]
    exact hd.add (dvd_mul_left (n₂ : ℤ) P)
  have habs : n₂ ∣ P.natAbs * (d₁ * n) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      Int.natAbs_dvd_natAbs.mpr hp
  exact hc.symm.dvd_of_dvd_mul_right habs

theorem iv3_resonance_s_dvd
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ} (ha : a ≠ 0)
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' = 0) :
    s ∣ ((h * n₂' * s') * ((d₁ : ℤ) * n - n₂)).natAbs := by
  have hd : (s : ℤ) ∣ (h * n₂' * s') * ((d₁ : ℤ) * n - n₂) := by
    refine ⟨h' * n₂ * ((d₁ : ℤ) * n - n₂'), ?_⟩
    rw [iv3_resonance_equation ha hl]
    ring
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd

/-- The signed frequency is unique once the two natural coordinates are
fixed. Both signs are covered by cancellation in the integers. -/
theorem iv3_resonance_frequency_unique
    {d₁ n n₂ n₂' s s' : ℕ} {a h h₁ h₂ : ℤ} (ha : a ≠ 0)
    (hn₂ : 0 < n₂) (hs : 0 < s) (hδ : (d₁ : ℤ) * n - n₂' ≠ 0)
    (h₁l : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h₁ = 0)
    (h₂l : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h₂ = 0) :
    h₁ = h₂ := by
  have he := (iv3_resonance_equation ha h₁l).symm.trans
    (iv3_resonance_equation ha h₂l)
  have hn₂' : (n₂ : ℤ) ≠ 0 := by positivity
  have hs' : (s : ℤ) ≠ 0 := by positivity
  exact mul_right_cancel₀ hn₂' (mul_right_cancel₀ hs' (mul_right_cancel₀ hδ he))

/-- The two finite divisor choices which encode every resonant triple. -/
def iv3ResonanceDivisorPairs (d₁ n : ℕ) (P : ℤ) : Finset (Σ _ : ℕ, ℕ) :=
  P.natAbs.divisors.sigma fun n₂ ↦
    (P * ((d₁ : ℤ) * n - n₂)).natAbs.divisors

theorem card_iv3ResonanceDivisorPairs (d₁ n : ℕ) (P : ℤ) :
    (iv3ResonanceDivisorPairs d₁ n P).card =
      ∑ n₂ ∈ P.natAbs.divisors,
        fouvryTau 2 (P * ((d₁ : ℤ) * n - n₂)).natAbs := by
  simp only [iv3ResonanceDivisorPairs, card_sigma, fouvryTau_two]

/-- Forget the uniquely determined signed frequency, not either natural
coordinate. -/
def iv3ResonanceEncode (t : ℕ × ℕ × ℤ) : Σ _ : ℕ, ℕ := ⟨t.1, t.2.1⟩

theorem iv3_resonance_encode_injOn
    {d₁ n n₂' s' : ℕ} {a h : ℤ} (ha : a ≠ 0)
    (hδ' : (d₁ : ℤ) * n - n₂' ≠ 0) {S : Finset (ℕ × ℕ × ℤ)}
    (hS : ∀ t ∈ S, 0 < t.1 ∧ 0 < t.2.1 ∧
      iv3CorrelationNumerator d₁ n t.1 n₂' t.2.1 s' a h t.2.2 = 0) :
    Set.InjOn iv3ResonanceEncode S := by
  rintro ⟨n₂, s, h₁⟩ ht ⟨m₂, u, h₂⟩ hu he
  have hn : n₂ = m₂ := congrArg Sigma.fst he
  have hs : s = u := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) he
  subst m₂
  subst u
  have hh := iv3_resonance_frequency_unique ha (hS _ ht).1
    (hS _ ht).2.1 hδ' (hS _ ht).2.2 (hS _ hu).2.2
  exact congrArg (fun j : ℤ => (n₂, s, j)) hh

theorem iv3_resonance_encode_mem
    {d₁ n n₂' s' : ℕ} {a h : ℤ} (ha : a ≠ 0)
    (hP : h * n₂' * s' ≠ 0) {t : ℕ × ℕ × ℤ}
    (hc : (d₁ * n).Coprime t.1) (hδ : (d₁ : ℤ) * n - t.1 ≠ 0)
    (hl : iv3CorrelationNumerator d₁ n t.1 n₂' t.2.1 s' a h t.2.2 = 0) :
    iv3ResonanceEncode t ∈ iv3ResonanceDivisorPairs d₁ n (h * n₂' * s') := by
  apply mem_sigma.mpr
  constructor
  · exact Nat.mem_divisors.mpr
      ⟨iv3_resonance_n₂_dvd ha hc hl, Int.natAbs_ne_zero.mpr hP⟩
  · exact Nat.mem_divisors.mpr
      ⟨iv3_resonance_s_dvd ha hl, Int.natAbs_ne_zero.mpr (mul_ne_zero hP hδ)⟩

/-- A genuine aggregate bound over every resonant triple in an arbitrary
finite carrier. There is no restriction to equal labels or equal frequencies. -/
theorem iv3_resonance_card_le_divisor_sum
    {d₁ n n₂' s' : ℕ} {a h : ℤ} (ha : a ≠ 0)
    (hP : h * n₂' * s' ≠ 0) (hδ' : (d₁ : ℤ) * n - n₂' ≠ 0)
    (S : Finset (ℕ × ℕ × ℤ))
    (hS : ∀ t ∈ S, 0 < t.1 ∧ 0 < t.2.1 ∧
      (d₁ * n).Coprime t.1 ∧ (d₁ : ℤ) * n - t.1 ≠ 0 ∧
      iv3CorrelationNumerator d₁ n t.1 n₂' t.2.1 s' a h t.2.2 = 0) :
    S.card ≤ ∑ n₂ ∈ (h * n₂' * s').natAbs.divisors,
      fouvryTau 2 ((h * n₂' * s') * ((d₁ : ℤ) * n - n₂)).natAbs := by
  rw [← card_iv3ResonanceDivisorPairs]
  apply card_le_card_of_injOn iv3ResonanceEncode
  · intro t ht
    exact iv3_resonance_encode_mem ha hP (hS t ht).2.2.1
      (hS t ht).2.2.2.1 (hS t ht).2.2.2.2
  · exact iv3_resonance_encode_injOn ha hδ'
      (fun t ht => ⟨(hS t ht).1, (hS t ht).2.1, (hS t ht).2.2.2.2⟩)

/-- Coordinate-dependent nonnegative weights can be summed directly over
the finite divisor encoding; arbitrary signed original weights are allowed. -/
theorem iv3_resonance_sum_le_divisor_sum
    {d₁ n n₂' s' : ℕ} {a h : ℤ} (ha : a ≠ 0)
    (hP : h * n₂' * s' ≠ 0) (hδ' : (d₁ : ℤ) * n - n₂' ≠ 0)
    (S : Finset (ℕ × ℕ × ℤ))
    (hS : ∀ t ∈ S, 0 < t.1 ∧ 0 < t.2.1 ∧
      (d₁ * n).Coprime t.1 ∧ (d₁ : ℤ) * n - t.1 ≠ 0 ∧
      iv3CorrelationNumerator d₁ n t.1 n₂' t.2.1 s' a h t.2.2 = 0)
    (w : ℕ × ℕ × ℤ → ℝ) (W : ℕ → ℕ → ℝ)
    (hW : ∀ j k, 0 ≤ W j k) (hw : ∀ t ∈ S, w t ≤ W t.1 t.2.1) :
    (∑ t ∈ S, w t) ≤
      ∑ n₂ ∈ (h * n₂' * s').natAbs.divisors,
        ∑ s ∈ ((h * n₂' * s') * ((d₁ : ℤ) * n - n₂)).natAbs.divisors,
          W n₂ s := by
  have hinj := iv3_resonance_encode_injOn ha hδ'
    (fun t ht => ⟨(hS t ht).1, (hS t ht).2.1, (hS t ht).2.2.2.2⟩)
  have hsub : S.image iv3ResonanceEncode ⊆
      iv3ResonanceDivisorPairs d₁ n (h * n₂' * s') := by
    rintro z hz
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
    exact iv3_resonance_encode_mem ha hP (hS t ht).2.2.1
      (hS t ht).2.2.2.1 (hS t ht).2.2.2.2
  calc
    _ ≤ ∑ t ∈ S, W t.1 t.2.1 := sum_le_sum hw
    _ = ∑ z ∈ S.image iv3ResonanceEncode, W z.1 z.2 := by
      rw [sum_image hinj]
      rfl
    _ ≤ ∑ z ∈ iv3ResonanceDivisorPairs d₁ n (h * n₂' * s'), W z.1 z.2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hW z.1 z.2)
    _ = _ := by rw [iv3ResonanceDivisorPairs, sum_sigma]

/-- In particular each fixed Gram weight or span bound can be paid once
per divisor encoding, with the actual resonance multiplicity. -/
theorem iv3_resonance_sum_le_const_mul
    {d₁ n n₂' s' : ℕ} {a h : ℤ} (ha : a ≠ 0)
    (hP : h * n₂' * s' ≠ 0) (hδ' : (d₁ : ℤ) * n - n₂' ≠ 0)
    (S : Finset (ℕ × ℕ × ℤ))
    (hS : ∀ t ∈ S, 0 < t.1 ∧ 0 < t.2.1 ∧
      (d₁ * n).Coprime t.1 ∧ (d₁ : ℤ) * n - t.1 ≠ 0 ∧
      iv3CorrelationNumerator d₁ n t.1 n₂' t.2.1 s' a h t.2.2 = 0)
    (w : ℕ × ℕ × ℤ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ t ∈ S, w t ≤ B) :
    (∑ t ∈ S, w t) ≤ B *
      (∑ n₂ ∈ (h * n₂' * s').natAbs.divisors,
        (fouvryTau 2 ((h * n₂' * s') * ((d₁ : ℤ) * n - n₂)).natAbs : ℝ)) := by
  have hc : (S.card : ℝ) ≤
      ∑ n₂ ∈ (h * n₂' * s').natAbs.divisors,
        (fouvryTau 2 ((h * n₂' * s') * ((d₁ : ℤ) * n - n₂)).natAbs : ℝ) := by
    exact_mod_cast iv3_resonance_card_le_divisor_sum ha hP hδ' S hS
  calc
    _ ≤ ∑ _t ∈ S, B := sum_le_sum hw
    _ = B * S.card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hB

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
