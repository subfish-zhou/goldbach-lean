import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWGCD
import Mathlib.Data.Nat.Squarefree

/-!
# Large prime support produces a large square divisor

For the `d₁` exclusion in Fouvry (1984), (8.3), a large prime factor is
unnecessary: a positive integer supported on the primes of `d` produces
a square divisor of `d * s` at least as large as `s`.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- A squarefree integer supported on the primes of a positive integer divides it. -/
theorem squarefree_dvd_of_prime_support {a d : ℕ} (ha : Squarefree a)
    (hd : 0 < d) (hs : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ d) : a ∣ d := by
  rw [← Nat.prod_primeFactors_of_squarefree ha]
  apply (Nat.prod_primeFactors_dvd_iff hd.ne').mpr
  intro p hp
  exact Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactors hp,
      hs p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), hd.ne'⟩

/-- The square witness uses the squarefree part of `s`, so it need not
contain any individually large prime. -/
theorem exists_square_dvd_of_prime_support {s d : ℕ} (hs : 0 < s) (hd : 0 < d)
    (hsd : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) :
    ∃ b : ℕ, 0 < b ∧ s ≤ b ^ 2 ∧ b ^ 2 ∣ d * s := by
  obtain ⟨a, c, ha, hc, he, hsq⟩ := Nat.sq_mul_squarefree_of_pos hs
  have has : a ∣ s := he ▸ dvd_mul_left a (c ^ 2)
  have had : a ∣ d :=
    squarefree_dvd_of_prime_support hsq hd (fun p hp hpa => hsd p hp (hpa.trans has))
  have hb : (c * a) ^ 2 = a * s := by rw [← he]; ring
  refine ⟨c * a, Nat.mul_pos hc ha, ?_, ?_⟩
  · rw [hb]
    exact Nat.le_mul_of_pos_left s ha
  · rw [hb]
    exact mul_dvd_mul_right had s

/-- The extraction transfers to any multiple of `d * s`. -/
theorem exists_square_dvd_of_supported_mul_dvd {s d n : ℕ}
    (hs : 0 < s) (hd : 0 < d)
    (hsd : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) (hn : d * s ∣ n) :
    ∃ b : ℕ, 0 < b ∧ s ≤ b ^ 2 ∧ b ^ 2 ∣ n := by
  obtain ⟨b, hb, hsb, hbd⟩ := exists_square_dvd_of_prime_support hs hd hsd
  exact ⟨b, hb, hsb, hbd.trans hn⟩

/-- In the five-gcd coordinates, a large `d₁` forces a square divisor of `N₁`. -/
theorem WGCDData.Valid.exists_square_dvd_N₁ {v : WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) :
    ∃ b : ℕ, 0 < b ∧ v.d₁ ≤ b ^ 2 ∧ b ^ 2 ∣ N₁ :=
  exists_square_dvd_of_supported_mul_dvd hv.d₁_pos hv.d_pos hv.d₁_support
    ⟨v.n₁, hv.N₁_eq⟩

/-- The canonical supported quotient has the square witness without any
hypothesis on the other modulus or the auxiliary indices. -/
theorem wGCDData_exists_square_dvd_N₁ (q r N₂ : ℕ) {N₁ : ℕ} (hN₁ : 0 < N₁) :
    ∃ b : ℕ, 0 < b ∧ (wGCDData q r N₁ N₂).d₁ ≤ b ^ 2 ∧ b ^ 2 ∣ N₁ := by
  let d := N₁.gcd N₂
  have hd : 0 < d := Nat.gcd_pos_of_pos_left N₂ hN₁
  have hu : 0 < N₁ / d :=
    Nat.div_pos (Nat.le_of_dvd hN₁ (Nat.gcd_dvd_left N₁ N₂)) hd
  apply exists_square_dvd_of_supported_mul_dvd (supportedPart_pos _ _) hd
    (fun _ hp hps => prime_dvd_supportedPart hp hps)
  calc
    d * supportedPart (N₁ / d) d ∣ d * (N₁ / d) :=
      mul_dvd_mul_left d (supportedPart_dvd hu d)
    _ = N₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left N₁ N₂)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
