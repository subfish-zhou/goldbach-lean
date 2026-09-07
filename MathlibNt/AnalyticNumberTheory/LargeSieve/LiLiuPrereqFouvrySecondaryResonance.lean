import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramAggregateBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGcdMean

/-!
# The nonzero secondary resonance with a common first beta index

The relation `h'*s = h*s'` does not force the correlation numerator to
vanish. In this branch its common `n*s'` factor is extracted before
averaging in `r`, never by applying a nonzero-coefficient mean in `n`.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def iv3SecondaryNumerator (d₁ n₂ n₂' : ℕ) (a h : ℤ) : ℤ :=
  a * d₁ * h * ((n₂' : ℤ) - n₂)

theorem iv3CorrelationNumerator_secondary
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s') :
    iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' =
      (n * s' : ℕ) * iv3SecondaryNumerator d₁ n₂ n₂' a h := by
  unfold iv3CorrelationNumerator iv3SecondaryNumerator
  push_cast
  calc
    _ = a * ((h * s') * n₂' * ((d₁ : ℤ) * n - n₂) -
        (h' * s) * n₂ * ((d₁ : ℤ) * n - n₂')) := by ring
    _ = _ := by rw [hsec]; ring

theorem iv3SecondaryNumerator_ne_zero
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) :
    iv3SecondaryNumerator d₁ n₂ n₂' a h ≠ 0 := by
  rw [iv3CorrelationNumerator_secondary hsec] at hl
  exact (mul_ne_zero_iff.mp hl).2

theorem iv3_secondary_gcd
    {d₁ n n₂ n₂' r s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s') :
    (n * r * s * s').gcd
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs =
      (n * s') * (r * s).gcd (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs := by
  rw [iv3CorrelationNumerator_secondary hsec, Int.natAbs_mul, Int.natAbs_natCast,
    show n * r * s * s' = (n * s') * (r * s) by ring, Nat.gcd_mul_left]

/-- A mean over a progression of multiples follows from the already proved
finite gcd mean by injective inclusion, with its step cost explicit. -/
theorem iv3_secondary_gcd_sum
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hs : 0 < s) (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) (B : ℕ) :
    (∑ r ∈ Ioc 0 B, (n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs) ≤
      (n * s') * (B * s * (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs.divisors.card) := by
  let A := (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs
  have hA : A ≠ 0 := Int.natAbs_ne_zero.mpr (iv3SecondaryNumerator_ne_zero hsec hl)
  simp_rw [iv3_secondary_gcd hsec]
  rw [← mul_sum]
  apply Nat.mul_le_mul_left
  calc
    (∑ r ∈ Ioc 0 B, (r * s).gcd A) =
        ∑ v ∈ (Ioc 0 B).image (fun r => r * s), v.gcd A := by
      rw [sum_image]
      intro r _ t _ he
      exact Nat.mul_right_cancel hs he
    _ ≤ ∑ v ∈ Ioc 0 (B * s), v.gcd A := by
      apply sum_le_sum_of_subset
      rintro v hv
      obtain ⟨r, hr, rfl⟩ := mem_image.mp hv
      exact mem_Ioc.mpr ⟨Nat.mul_pos (mem_Ioc.mp hr).1 hs,
        Nat.mul_le_mul_right s (mem_Ioc.mp hr).2⟩
    _ ≤ _ := by simpa only [Nat.gcd_comm] using sum_gcd_le hA (B * s)

/-- Square-root gcd mean in the secondary branch. It is uniform in the
common `n`, including the case where the coefficient for an `n`-mean is zero. -/
theorem iv3_secondary_sqrt_gcd_sum
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hs : 0 < s) (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) (B : ℕ) :
    (∑ r ∈ Ioc 0 B, Real.sqrt ((n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) ≤
      B * Real.sqrt ((n * s' * s *
        (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs.divisors.card : ℕ) : ℝ) := by
  let A := (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs
  have hm : (∑ r ∈ Ioc 0 B, ((n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) ≤
      ((n * s') * (B * s * A.divisors.card) : ℕ) := by
    exact_mod_cast iv3_secondary_gcd_sum hs hsec hl B
  calc
    _ ≤ Real.sqrt (B : ℝ) * Real.sqrt
        (∑ r ∈ Ioc 0 B, ((n * r * s * s').gcd
          (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) := by
      simpa using Real.sum_sqrt_mul_sqrt_le (f := fun _ : ℕ => (1 : ℝ))
        (g := fun r => ((n * r * s * s').gcd
          (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ))
        (Ioc 0 B) (fun _ => by positivity) (fun _ => by positivity)
    _ ≤ Real.sqrt (B : ℝ) *
        Real.sqrt (((n * s') * (B * s * A.divisors.card) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg B)]
      have he : (B : ℝ) * (((n * s') * (B * s * A.divisors.card) : ℕ) : ℝ) =
          (B : ℝ) ^ 2 * ((n * s' * s * A.divisors.card : ℕ) : ℝ) := by
        push_cast
        ring
      rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg B)]

/-- The secondary branch is not excluded by the nonzero numerator filter. -/
def wGramSecondaryResonant (L : WGramLabel) : Prop :=
  L.2.2.2.2 * L.2.1.2.1 = L.2.1.2.2 * L.2.2.2.1

theorem sum_wGram_nonzero_split_secondary
    (G : Finset WGramLabel) (K : WExtractedKey) (a : ℤ) (F : WGramLabel → ℝ) :
    (∑ L ∈ G.filter (fun L => wGramNumerator K a L ≠ 0), F L) =
      (∑ L ∈ G.filter (fun L =>
        wGramNumerator K a L ≠ 0 ∧ wGramSecondaryResonant L), F L) +
      ∑ L ∈ G.filter (fun L =>
        wGramNumerator K a L ≠ 0 ∧ ¬ wGramSecondaryResonant L), F L := by
  simpa only [filter_filter] using
    (sum_filter_add_sum_filter_not
      (G.filter (fun L => wGramNumerator K a L ≠ 0)) wGramSecondaryResonant F).symm

/-- A quantitative `r`-mean of the actual Fouvry cost on the secondary
branch. Both local endpoints are retained in the modulus bounds. This
does not assume the signed linear coefficient for an `n`-mean is nonzero. -/
theorem wGramFouvryCost_secondary_sum
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (a : ℤ) (R S M Z : ℝ) (K : WExtractedKey) (j cap : Fin 5 → ℕ)
    {n n₂ n₂' s s' : ℕ} {h h' : ℤ}
    (hn : 0 < n) (hs : 0 < s) (hs' : 0 < s')
    (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator K.1.2.1 n n₂ n₂' s s' a h h' ≠ 0)
    (lo hi : ℕ) :
    (∑ r ∈ Ioc lo hi, wGramFouvryCost ε C a R S M Z K j cap
      ((r, n), (n₂, s, h), (n₂', s', h'))) ≤
      (C * (a.natAbs.divisors.card : ℝ) *
        ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) /
          (n * (lo + 1) * s * s' : ℕ)) *
        (n * hi * s * s' : ℕ) ^ (1 / 2 + ε : ℝ)) *
      (hi * Real.sqrt ((n * s' * s *
        (iv3SecondaryNumerator K.1.2.1 n₂ n₂' a h).natAbs.divisors.card : ℕ) : ℝ)) := by
  let E : ℝ := C * (a.natAbs.divisors.card : ℝ) *
    ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) /
      (n * (lo + 1) * s * s' : ℕ)) *
    (n * hi * s * s' : ℕ) ^ (1 / 2 + ε : ℝ)
  let f := fun r => Real.sqrt ((n * r * s * s').gcd
    (iv3CorrelationNumerator K.1.2.1 n n₂ n₂' s s' a h h').natAbs : ℝ)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hpoint (r : ℕ) (hr : r ∈ Ioc lo hi) :
      wGramFouvryCost ε C a R S M Z K j cap
        ((r, n), (n₂, s, h), (n₂', s', h')) ≤ E * f r := by
    have hqlo : 0 < (n * (lo + 1) * s * s' : ℝ) := by positivity
    have hqr : (n * (lo + 1) * s * s' : ℝ) ≤ (n * r * s * s' : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right s' (Nat.mul_le_mul_right s
        (Nat.mul_le_mul_left n (mem_Ioc.mp hr).1))
    have hqhi : (n * r * s * s' : ℝ) ≤ (n * hi * s * s' : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right s' (Nat.mul_le_mul_right s
        (Nat.mul_le_mul_left n (mem_Ioc.mp hr).2))
    have hspan : (wGramSpan R S M Z K j cap
        ((r, n), (n₂, s, h), (n₂', s', h')) : ℝ) ≤
        (wKSectionGridUpper R S K j cap + 1 : ℕ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le _ _) 1
    have hd := div_le_div₀ (by positivity) hspan hqlo hqr
    have hp := Real.rpow_le_rpow (by positivity) hqhi (by linarith : 0 ≤ 1 / 2 + ε)
    change C * (a.natAbs.divisors.card : ℝ) *
      ((K.D' : ℝ) + (wGramSpan R S M Z K j cap
        ((r, n), (n₂, s, h), (n₂', s', h')) : ℝ) / (n * r * s * s' : ℕ)) *
      f r * (n * r * s * s' : ℕ) ^ (1 / 2 + ε : ℝ) ≤ E * f r
    dsimp only [E]
    push_cast at hd hp ⊢
    calc
      _ = (C * (a.natAbs.divisors.card : ℝ) *
          ((K.D' : ℝ) + (wGramSpan R S M Z K j cap
            ((r, n), (n₂, s, h), (n₂', s', h')) : ℝ) / (n * r * s * s')) *
          (n * r * s * s') ^ (1 / 2 + ε : ℝ)) * f r := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hd) (by positivity))
          hp (by positivity) (by positivity)
  calc
    _ ≤ ∑ r ∈ Ioc lo hi, E * f r := sum_le_sum hpoint
    _ = E * ∑ r ∈ Ioc lo hi, f r := (mul_sum _ _ _).symm
    _ ≤ E * ∑ r ∈ Ioc 0 hi, f r := by
      apply mul_le_mul_of_nonneg_left _ hE
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le lo) (mem_Ioc.mp hr).1,
          (mem_Ioc.mp hr).2⟩
      · intro r _ _
        exact Real.sqrt_nonneg _
    _ ≤ _ := mul_le_mul_of_nonneg_left (iv3_secondary_sqrt_gcd_sum hs hsec hl hi) hE

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
