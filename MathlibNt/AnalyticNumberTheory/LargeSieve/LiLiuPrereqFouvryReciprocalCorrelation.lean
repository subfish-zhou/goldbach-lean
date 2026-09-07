import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedPhase
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompleteWeil

/-!
# The same-first-index reciprocal correlation in F87 IV.3

Fouvry (1987), p. 632, (4.7)--(4.8). The two phases share `n`, not just
`d₁` and `r`. Their common modulus is `n*r*s*s'`, with no second copy of
`n`. The factors `s,s'` need not be coprime. Signed frequencies and residue,
zero correlation numerator, and modulus one are all retained.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The unmasked reciprocal circle phase, with the existing Bezout inverse. -/
def iv3ReciprocalCircle (q u : ℕ) (A : ℤ) : UnitAddCircle :=
  (((A * wPhaseInverse u q : ℤ) : ℝ) / q : ℝ)

/-- F87's original phase, after `k₂ = r*s`. -/
def iv3ReciprocalPhase (D d₁ n n₂ k r s : ℕ) (a : ℤ) : UnitAddCircle :=
  iv3ReciprocalCircle (n * r * s) (D * n₂ * k) (a * (d₁ * n - n₂))

/-- The signed integer in (4.8); both differences have the same `n`. -/
def iv3CorrelationNumerator (d₁ n n₂ n₂' s s' : ℕ) (a h h' : ℤ) : ℤ :=
  a * (h * n₂' * s' * (d₁ * n - n₂) - h' * n₂ * s * (d₁ * n - n₂'))

theorem wReciprocalPhase_eq_iv3 {v : WGCDData} {r s : ℕ}
    (hfactor : v.k₂ = r * s) (a : ℤ) :
    wReciprocalPhase v a =
      iv3ReciprocalPhase v.D' v.d₁ v.n₁ v.n₂ v.k₁ r s a := by
  unfold wReciprocalPhase iv3ReciprocalPhase iv3ReciprocalCircle
  rw [hfactor]
  simp only [Nat.cast_mul, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  congr 1
  ring_nf

theorem iv3ReciprocalCircle_fourier (q u : ℕ) (A h : ℤ) :
    fourier h (iv3ReciprocalCircle q u A) =
      fourier 1 (iv3ReciprocalCircle q u (h * A)) := by
  unfold iv3ReciprocalCircle
  rw [fourier_real_eq_fourierChar, fourier_real_eq_fourierChar]
  push_cast
  congr 2
  ring

/-- Inverse transport only uses divisibility of the moduli, not coprimality
of their quotient and the smaller modulus. -/
theorem iv3_inverse_transport {m j u v : ℕ}
    (hc : (u * v).Coprime (m * j)) :
    Int.ModEq m (wPhaseInverse u m) (v * wPhaseInverse (u * v) (m * j)) := by
  have hu : u.Coprime m :=
    (hc.of_dvd_left (dvd_mul_right u v)).of_dvd_right (dvd_mul_right m j)
  have hsmall : Int.ModEq m (wPhaseInverse u m * u) 1 := by
    simpa only [mul_comm] using wPhaseInverse_spec hu
  have hlarge := (wPhaseInverse_spec hc).of_dvd
    (show (m : ℤ) ∣ (m * j : ℕ) by exact_mod_cast dvd_mul_right m j)
  apply ((product_modEq_iff_of_coprime hu hsmall).mp ?_).symm
  simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hlarge

/-- Exact passage to a larger denominator and a common inverse. -/
theorem iv3ReciprocalCircle_common_denominator {m j u v : ℕ}
    (hm : 0 < m) (hj : 0 < j) (hc : (u * v).Coprime (m * j)) (A : ℤ) :
    iv3ReciprocalCircle m u A =
      iv3ReciprocalCircle (m * j) (u * v) (A * v * j) := by
  unfold iv3ReciprocalCircle
  rw [wPhase_circle_eq_of_modEq hm ((iv3_inverse_transport hc).mul_left A)]
  congr 1
  have hj' : (j : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem iv3ReciprocalCircle_sub (q u : ℕ) (A B : ℤ) :
    iv3ReciprocalCircle q u A - iv3ReciprocalCircle q u B =
      iv3ReciprocalCircle q u (A - B) := by
  unfold iv3ReciprocalCircle
  rw [← AddCircle.coe_sub]
  congr 1
  push_cast
  ring

private theorem iv3_fourier_sub (x y : UnitAddCircle) :
    fourier 1 (x - y) = fourier 1 x * star (fourier 1 y) := by
  rw [fourier_one, sub_eq_add_neg, AddCircle.toCircle_add, Circle.coe_mul]
  exact congrArg₂ (· * ·) fourier_one.symm
    (by simpa only [one_zsmul, RCLike.star_def] using (fourier_neg' (n := 1) (x := y)))

/-- The exact paired phase in (4.7). The sole coprimality hypothesis is that
the common inverse exists. In particular, there is no pairwise-coprimality
assumption on `n,r,s,s'`. -/
theorem iv3_reciprocal_correlation
    {D d₁ n n₂ n₂' k r s s' : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s')
    (hc : (D * n₂ * n₂' * k).Coprime (n * r * s * s')) (a h h' : ℤ) :
    fourier h (iv3ReciprocalPhase D d₁ n n₂ k r s a) *
        star (fourier h' (iv3ReciprocalPhase D d₁ n n₂' k r s' a)) =
      fourier 1 (iv3ReciprocalCircle (n * r * s * s') (D * n₂ * n₂' * k)
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h')) := by
  have hc₁ : ((D * n₂ * k) * n₂').Coprime ((n * r * s) * s') := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hc
  have hc₂ : ((D * n₂' * k) * n₂).Coprime ((n * r * s') * s) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hc
  unfold iv3ReciprocalPhase
  rw [iv3ReciprocalCircle_fourier _ _ _ h, iv3ReciprocalCircle_fourier _ _ _ h',
    iv3ReciprocalCircle_common_denominator (by positivity) hs' hc₁,
    iv3ReciprocalCircle_common_denominator (by positivity) hs hc₂]
  have hden : n * r * s' * s = n * r * s * s' := by ring
  have hinv₁ : D * n₂ * k * n₂' = D * n₂ * n₂' * k := by ring
  have hinv₂ : D * n₂' * k * n₂ = D * n₂ * n₂' * k := by ring
  rw [hden, hinv₁, hinv₂, ← iv3_fourier_sub, iv3ReciprocalCircle_sub]
  congr 2
  unfold iv3CorrelationNumerator
  ring

theorem norm_iv3_reciprocal_correlation
    (D d₁ n n₂ n₂' k r s s' : ℕ) (a h h' : ℤ) :
    ‖fourier h (iv3ReciprocalPhase D d₁ n n₂ k r s a) *
        star (fourier h' (iv3ReciprocalPhase D d₁ n n₂' k r s' a))‖ = 1 := by
  simp only [norm_mul, norm_star, fourier_apply, Circle.norm_coe, mul_one]

/-- The zero-numerator branch is exactly one, not just bounded by one. -/
theorem iv3_reciprocal_correlation_zero
    {D d₁ n n₂ n₂' k r s s' : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s')
    (hc : (D * n₂ * n₂' * k).Coprime (n * r * s * s')) (a h h' : ℤ)
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' = 0) :
    fourier h (iv3ReciprocalPhase D d₁ n n₂ k r s a) *
        star (fourier h' (iv3ReciprocalPhase D d₁ n n₂' k r s' a)) = 1 := by
  rw [iv3_reciprocal_correlation hn hr hs hs' hc, hl]
  simp [iv3ReciprocalCircle]

/-- Agreement with the inverse used by the complete Weil theorem, including
the trivial residue ring at modulus one. -/
theorem iv3_wPhaseInverse_zmod {q u : ℕ} (hc : u.Coprime q) :
    (wPhaseInverse u q : ZMod q) = (u : ZMod q)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  have he := (ZMod.intCast_eq_intCast_iff
    ((u : ℤ) * wPhaseInverse u q) 1 q).mpr (wPhaseInverse_spec hc)
  simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_one] using he

theorem iv3ReciprocalCircle_stdAddChar {q u : ℕ} [NeZero q]
    (hc : u.Coprime q) (A : ℤ) :
    fourier 1 (iv3ReciprocalCircle q u A) =
      ZMod.stdAddChar ((A : ZMod q) * (u : ZMod q)⁻¹) := by
  unfold iv3ReciprocalCircle
  rw [← ZMod.toAddCircle_intCast, fourier_one]
  change ZMod.stdAddChar ((A * wPhaseInverse u q : ℤ) : ZMod q) = _
  rw [Int.cast_mul, iv3_wPhaseInverse_zmod hc]

/-- Absorbing a fixed unit into the frequency does not change its gcd with
the modulus. This also covers zero and negative frequencies. -/
theorem iv3_gcd_inverse_twist {q u : ℕ} (hc : u.Coprime q) (A : ℤ) :
    q.gcd (A * wPhaseInverse u q).natAbs = q.gcd A.natAbs := by
  have hb : IsCoprime (wPhaseInverse u q) (q : ℤ) := by
    refine ⟨u, u.gcdB q, ?_⟩
    have he := Nat.gcd_eq_gcd_ab u q
    rw [hc.gcd_eq_one, Nat.cast_one] at he
    simpa only [wPhaseInverse, mul_comm] using he.symm
  have hi : (wPhaseInverse u q).natAbs.Coprime q := by
    have he := Int.isCoprime_iff_gcd_eq_one.mp hb
    exact he
  rw [Int.natAbs_mul]
  exact hi.gcd_mul_right_cancel_right _

theorem iv3ReciprocalCircle_eq_reciprocalPhase {q B k : ℕ} [NeZero q]
    (hB : B.Coprime q) (hk : k.Coprime q) (A : ℤ) :
    fourier 1 (iv3ReciprocalCircle q (B * k) A) =
      reciprocalPhase q (A * wPhaseInverse B q) (k : ZMod q) := by
  have hunit : IsUnit (k : ZMod q) := by
    exact ⟨⟨k, (k : ZMod q)⁻¹, ZMod.coe_mul_inv_eq_one k hk,
      by simpa only [mul_comm] using ZMod.coe_mul_inv_eq_one k hk⟩, rfl⟩
  rw [iv3ReciprocalCircle_stdAddChar (hB.mul_left hk),
    reciprocalPhase, if_pos hunit, Int.cast_mul, iv3_wPhaseInverse_zmod hB]
  have hi : ((B * k : ℕ) : ZMod q)⁻¹ =
      (B : ZMod q)⁻¹ * (k : ZMod q)⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    push_cast
    calc
      (B : ZMod q) * k * ((B : ZMod q)⁻¹ * (k : ZMod q)⁻¹) =
          ((B : ZMod q) * (B : ZMod q)⁻¹) *
            ((k : ZMod q) * (k : ZMod q)⁻¹) := by ring
      _ = 1 := by rw [ZMod.coe_mul_inv_eq_one B hB, ZMod.coe_mul_inv_eq_one k hk,
        one_mul]
  rw [hi, mul_assoc]

/-- The actual unweighted interval of positive `k`, with precisely its
coprimality restriction. No coefficient or additional carrier mask is present. -/
def iv3CorrelationInterval (D d₁ n n₂ n₂' r s s' : ℕ) (a h h' : ℤ)
    (X Y : ℕ) : ℂ :=
  ∑ k ∈ (Finset.Ioc X Y).filter (fun k ↦ k.Coprime (n * r * s * s')),
    fourier h (iv3ReciprocalPhase D d₁ n n₂ k r s a) *
      star (fourier h' (iv3ReciprocalPhase D d₁ n n₂' k r s' a))

/-- Natural interval endpoints give the same interval convention as the
established Fouvry bound: `X < k ≤ Y`. -/
theorem iv3_reciprocalInterval_nat {q : ℕ} [NeZero q] (d : ℤ) (X Y : ℕ) :
    (∑ k ∈ Finset.Ioc X Y, reciprocalPhase q d (k : ZMod q)) =
      reciprocalInterval q d X Y := by
  unfold reciprocalInterval
  simp only [Int.floor_natCast]
  apply Finset.sum_bij (fun (k : ℕ) _ ↦ (k : ℤ))
  · intro k hk
    simpa only [Finset.mem_Ioc, Nat.cast_lt, Nat.cast_le] using hk
  · intro k _ j _ he
    exact_mod_cast he
  · intro c hc
    have hc' := Finset.mem_Ioc.mp hc
    refine ⟨c.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
  · intro k _
    simp only [Int.cast_natCast]

theorem iv3CorrelationInterval_eq_reciprocalInterval
    {D d₁ n n₂ n₂' r s s' : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s')
    (hB : (D * n₂ * n₂').Coprime (n * r * s * s')) (a h h' : ℤ) (X Y : ℕ) :
    letI : NeZero (n * r * s * s') := ⟨by positivity⟩
    iv3CorrelationInterval D d₁ n n₂ n₂' r s s' a h h' X Y =
      reciprocalInterval (n * r * s * s')
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' *
          wPhaseInverse (D * n₂ * n₂') (n * r * s * s')) X Y := by
  let : NeZero (n * r * s * s') := ⟨by positivity⟩
  rw [← iv3_reciprocalInterval_nat]
  unfold iv3CorrelationInterval
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.Coprime (n * r * s * s')
  · rw [if_pos hk, iv3_reciprocal_correlation hn hr hs hs' (hB.mul_left hk),
      iv3ReciprocalCircle_eq_reciprocalPhase hB hk]
  · rw [if_neg hk]
    symm
    unfold reciprocalPhase
    rw [if_neg]
    intro hu
    exact hk ((ZMod.isUnit_iff_coprime k (n * r * s * s')).mp hu)

/-- The unconditional complete Weil theorem applies to this unweighted
interval, not to an arbitrarily weighted or further masked correlation. -/
theorem iv3CorrelationInterval_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D d₁ n n₂ n₂' r s s' : ℕ) (a h h' : ℤ) (X Y : ℕ),
        0 < n → 0 < r → 0 < s → 0 < s' →
        (D * n₂ * n₂').Coprime (n * r * s * s') →
        X ≤ Y → Y - X ≤ n * r * s * s' →
        ‖iv3CorrelationInterval D d₁ n n₂ n₂' r s s' a h h' X Y‖ ≤
          C * Real.sqrt ((n * r * s * s').gcd
            (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs) *
            (n * r * s * s' : ℕ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocalInterval_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro D d₁ n n₂ n₂' r s s' a h h' X Y hn hr hs hs' hB hXY hlen
  let : NeZero (n * r * s * s') := ⟨by positivity⟩
  rw [iv3CorrelationInterval_eq_reciprocalInterval hn hr hs hs' hB]
  have he := hbound (n * r * s * s') inferInstance
    (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' *
      wPhaseInverse (D * n₂ * n₂') (n * r * s * s')) X Y
    (by exact_mod_cast hXY) (by exact_mod_cast hlen)
  rw [iv3_gcd_inverse_twist hB] at he
  exact he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
