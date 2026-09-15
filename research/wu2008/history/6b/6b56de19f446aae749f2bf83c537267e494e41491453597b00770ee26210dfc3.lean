import MathlibNt.Wu2004MeanValue.SiftedPairs

/-!
# The original quotient-sieve tail

The manuscript's `A_eta` consists of `N-p`, not switched prime-pair values.
Division is performed only after testing divisibility. Each source prime `r`
contributes its own sifted quotient cardinality to the literal sum.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

def originalTailPrimes (N : ℕ) (η : ℝ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ (p : ℝ) ≤ (1 - η) * N)

def originalTailA (N : ℕ) (η : ℝ) : Finset ℕ :=
  (originalTailPrimes N η).image (fun p => N - p)

def originalTailQuotients (N r : ℕ) (η : ℝ) : Finset ℕ :=
  ((originalTailA N η).filter (fun a => r ∣ a)).image (fun a => a / r)

def tailOriginalSum (N : ℕ) (c τ η : ℝ) : ℕ :=
  ∑ r ∈ tailSource N c τ,
    ((originalTailQuotients N r η).filter
      (fun m => m.Coprime (siftingProduct N r))).card

def originalTailPrimeIndices (N r : ℕ) (η : ℝ) : Finset ℕ :=
  (originalTailPrimes N η).filter
    (fun p => r ∣ N - p ∧ ((N - p) / r).Coprime (siftingProduct N r))

def originalTailIndices (N : ℕ) (c τ η : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (tailSource N c τ).sigma (fun r => originalTailPrimeIndices N r η)

theorem mem_originalTailPrimes {N p : ℕ} {η : ℝ} :
    p ∈ originalTailPrimes N η ↔
      p ≤ N ∧ p.Prime ∧ (p : ℝ) ≤ (1 - η) * N := by
  simp [originalTailPrimes]

theorem mem_originalTailA {N a : ℕ} {η : ℝ} :
    a ∈ originalTailA N η ↔
      ∃ p, p ≤ N ∧ p.Prime ∧ (p : ℝ) ≤ (1 - η) * N ∧ N - p = a := by
  simp only [originalTailA, mem_image, mem_originalTailPrimes]
  aesop

theorem mem_originalTailQuotients {N r m : ℕ} {η : ℝ} :
    m ∈ originalTailQuotients N r η ↔
      ∃ p ∈ originalTailPrimes N η, r ∣ N - p ∧ (N - p) / r = m := by
  simp only [originalTailQuotients, originalTailA, mem_image, mem_filter]
  aesop

theorem mem_originalTailPrimeIndices {N r p : ℕ} {η : ℝ} :
    p ∈ originalTailPrimeIndices N r η ↔
      p ≤ N ∧ p.Prime ∧ (p : ℝ) ≤ (1 - η) * N ∧ r ∣ N - p ∧
        ((N - p) / r).Coprime (siftingProduct N r) := by
  simp only [originalTailPrimeIndices, mem_filter, mem_originalTailPrimes]
  tauto

theorem mem_originalTailIndices {N r p : ℕ} {c τ η : ℝ} :
    (⟨r, p⟩ : Σ _ : ℕ, ℕ) ∈ originalTailIndices N c τ η ↔
      r ∈ tailSource N c τ ∧ p ∈ originalTailPrimeIndices N r η := by
  simp [originalTailIndices]

theorem originalTailQuotient_injective {N r : ℕ} {η : ℝ} :
    Set.InjOn (fun p => (N - p) / r) (originalTailPrimeIndices N r η) := by
  intro p hp q hq heq
  have hp' := mem_originalTailPrimeIndices.mp hp
  have hq' := mem_originalTailPrimeIndices.mp hq
  have h := congrArg (fun m => r * m) heq
  rw [Nat.mul_div_cancel' hp'.2.2.2.1, Nat.mul_div_cancel' hq'.2.2.2.1] at h
  omega

theorem originalTailQuotients_sifted_image (N r : ℕ) (η : ℝ) :
    (originalTailQuotients N r η).filter
        (fun m => m.Coprime (siftingProduct N r)) =
      (originalTailPrimeIndices N r η).image (fun p => (N - p) / r) := by
  ext m
  simp only [mem_filter, mem_originalTailQuotients, mem_image,
    originalTailPrimeIndices]
  constructor
  · rintro ⟨⟨p, hp, hd, rfl⟩, hs⟩
    exact ⟨p, ⟨hp, hd, hs⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hd, hs⟩, rfl⟩
    exact ⟨⟨p, hp, hd, rfl⟩, hs⟩

theorem tailOriginalSum_eq_primeIndex_card (N : ℕ) (c τ η : ℝ) :
    tailOriginalSum N c τ η = (originalTailIndices N c τ η).card := by
  rw [tailOriginalSum, originalTailIndices, card_sigma]
  apply sum_congr rfl
  intro r _
  rw [originalTailQuotients_sifted_image, card_image_of_injOn originalTailQuotient_injective]

def originalTailSwitch (N : ℕ) (t : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
  ⟨t.1, (N - t.2) / t.1⟩

theorem originalTailSwitch_injective {N : ℕ} {c τ η : ℝ} :
    Set.InjOn (originalTailSwitch N) (originalTailIndices N c τ η) := by
  rintro ⟨r, p⟩ hp ⟨s, q⟩ hq heq
  have hrs : r = s := congrArg Sigma.fst heq
  subst s
  have hp' := (mem_originalTailIndices.mp hp).2
  have hq' := (mem_originalTailIndices.mp hq).2
  have hpq : p = q := originalTailQuotient_injective hp' hq'
    (congrArg (fun t : Σ _ : ℕ, ℕ => t.2) heq)
  subst q
  rfl

theorem originalTailSwitch_pairValue {N r p : ℕ} {η : ℝ}
    (hp : p ∈ originalTailPrimeIndices N r η) :
    pairValue N (originalTailSwitch N ⟨r, p⟩) = p := by
  have h := mem_originalTailPrimeIndices.mp hp
  simp only [pairValue, originalTailSwitch, Nat.mul_div_cancel' h.2.2.2.1]
  omega

theorem originalTailSwitch_mem_tailPairs {N r p : ℕ} {c τ η : ℝ}
    (hr : r ∈ tailSource N c τ)
    (hp : p ∈ originalTailPrimeIndices N r η)
    (hm : ((N - p) / r).Prime) :
    originalTailSwitch N ⟨r, p⟩ ∈ tailPairs N c τ η := by
  have h := mem_originalTailPrimeIndices.mp hp
  have heq : r * ((N - p) / r) = N - p := Nat.mul_div_cancel' h.2.2.2.1
  have hreal : (r : ℝ) * (((N - p) / r : ℕ) : ℝ) = (N : ℝ) - p := by
    rw [← Nat.cast_mul, heq, Nat.cast_sub h.1]
  apply mem_tailPairs.mpr
  refine ⟨hr, hm, ?_, ?_⟩
  · rw [hreal]
    nlinarith [h.2.2.1]
  · rw [hreal]
    linarith [Nat.cast_nonneg (α := ℝ) p]

end
end Wu2004MeanValue
