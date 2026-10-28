import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWPhase

/-!
# The three-factor reciprocal phase of the actual W residue

Fouvry (1984), p. 238, (8.13)--(8.15), and Fouvry (1987), p. 627, (3.11).
The integer parameters describe an already admissible five-gcd piece. We prove
the phase transformation, not the partition into such pieces or its error bound.
Every inverse below is a signed Bezout inverse modulo its displayed denominator.
-/

noncomputable section

open scoped FourierTransform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem wPhase_three_congruences
    (d d₁ D k₁ k₂ n₁ n₂ a b A B C : ℤ)
    (hA : Int.ModEq D (k₁ * k₂ * A) 1)
    (hB : Int.ModEq (d * d₁ * D) (n₁ * k₁ * k₂ * B) 1)
    (hC : Int.ModEq (n₁ * k₂) (d * d₁ * D * n₂ * k₁ * C) 1)
    (hb₁ : Int.ModEq k₁ (b * (d * d₁ * n₁)) a)
    (hb₂ : Int.ModEq k₂ (b * (d * n₂)) a) :
    let Z := b * A * d * d₁ * n₁ * k₁ * k₂ -
      a * B * n₁ * k₁ * k₂ + a +
        a * (d₁ * n₁ - n₂) * C * (d * d₁ * D) * k₁
    Int.ModEq (d * d₁ * D) (b * (d * d₁ * n₁)) Z ∧
      Int.ModEq k₁ (b * (d * d₁ * n₁)) Z ∧
      Int.ModEq (n₁ * k₂) (b * (d * d₁ * n₁)) Z := by
  obtain ⟨zA, hzA⟩ := hA.dvd
  obtain ⟨zB, hzB⟩ := hB.dvd
  obtain ⟨zC, hzC⟩ := hC.dvd
  obtain ⟨z₁, hz₁⟩ := hb₁.dvd
  obtain ⟨z₂, hz₂⟩ := hb₂.dvd
  dsimp
  refine ⟨Int.modEq_iff_dvd.mpr ?_, Int.modEq_iff_dvd.mpr ?_,
    Int.modEq_iff_dvd.mpr ?_⟩
  · refine ⟨-b * n₁ * zA + a * zB + a * (d₁ * n₁ - n₂) * C * k₁, ?_⟩
    linear_combination -b * d * d₁ * n₁ * hzA + a * hzB
  · refine ⟨b * A * d * d₁ * n₁ * k₂ - a * B * n₁ * k₂ +
      z₁ + a * (d₁ * n₁ - n₂) * C * (d * d₁ * D), ?_⟩
    linear_combination hz₁
  · refine ⟨b * A * d * d₁ * k₁ - a * B * k₁ +
      (a - b * d * d₁ * n₁) * zC + d₁ * z₂ * C * (d * d₁ * D) * k₁, ?_⟩
    linear_combination (a - b * d * d₁ * n₁) * hzC +
      d₁ * n₁ * C * (d * d₁ * D) * k₁ * hz₂

/-- Exact source three-factor phase of the existing product CRT residue.
`D' = d*d₁*D`; the genuine reciprocal denominator is `n₁*k₂`.
The original multipliers are `d*d₁*n₁` and `d*n₂`, and the original moduli
can be noncoprime. The hypotheses are arithmetic factorization/coprimality
conditions, not supplied phase identities. -/
theorem productCRTResidue_phase_threeFactor
    {q r d d₁ D k₁ k₂ n₁ n₂ : ℕ}
    (hd : 0 < d) (hd₁ : 0 < d₁) (hDpos : 0 < D)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hn₁ : 0 < n₁)
    (hL : q.lcm r = D * k₁ * k₂) (hk₁q : k₁ ∣ q) (hk₂r : k₂ ∣ r)
    (hD : (k₁ * k₂).Coprime D)
    (hD' : (n₁ * k₁ * k₂).Coprime (d * d₁ * D))
    (hk : k₁.Coprime (n₁ * k₂)) (hn₂ : n₂.Coprime (n₁ * k₂))
    (hc : WCompatible q r (d * d₁ * n₁) (d * n₂)) (a : ℤ) :
    let D' := d * d₁ * D
    let b := productCRTResidue q r (d * d₁ * n₁) (d * n₂) a
    (((b : ℝ) / (q.lcm r) : ℝ) : UnitAddCircle) =
      (((b : ℝ) * wPhaseInverse (k₁ * k₂) D / D -
        (a : ℝ) * wPhaseInverse (n₁ * k₁ * k₂) D' / D' : ℝ) : UnitAddCircle) +
      (((a : ℝ) / ((n₁ : ℝ) * k₁ * k₂ * D') : ℝ) : UnitAddCircle) +
      (((a : ℝ) * ((d₁ : ℝ) * n₁ - n₂) *
        wPhaseInverse (D' * n₂ * k₁) (n₁ * k₂) / ((n₁ : ℝ) * k₂) : ℝ) :
          UnitAddCircle) := by
  dsimp only
  let b := productCRTResidue q r (d * d₁ * n₁) (d * n₂) a
  let A := wPhaseInverse (k₁ * k₂) D
  let B := wPhaseInverse (n₁ * k₁ * k₂) (d * d₁ * D)
  let C := wPhaseInverse (d * d₁ * D * n₂ * k₁) (n₁ * k₂)
  let Z : ℤ := b * A * d * d₁ * n₁ * k₁ * k₂ -
    a * B * n₁ * k₁ * k₂ + a +
      a * ((d₁ : ℤ) * n₁ - n₂) * C * (d * d₁ * D : ℕ) * k₁
  have hVD : (n₁ * k₂).Coprime (d * d₁ * D) :=
    hD'.of_dvd_left ⟨k₁, by ring⟩
  have hU : (d * d₁ * D * n₂ * k₁).Coprime (n₁ * k₂) :=
    (hVD.symm.mul_left hn₂).mul_left hk
  have hb := productCRTResidue_spec a hc
  have hb₁ := hb.1.of_dvd (by exact_mod_cast hk₁q : (k₁ : ℤ) ∣ q)
  have hb₂ := hb.2.1.of_dvd (by exact_mod_cast hk₂r : (k₂ : ℤ) ∣ r)
  have ht := wPhase_three_congruences d d₁ D k₁ k₂ n₁ n₂ a b A B C
    (by simpa only [Nat.cast_mul] using wPhaseInverse_spec hD)
    (by simpa only [Nat.cast_mul] using wPhaseInverse_spec hD')
    (by simpa only [Nat.cast_mul] using wPhaseInverse_spec hU)
    (by simpa only [Nat.cast_mul] using hb₁)
    (by simpa only [Nat.cast_mul] using hb₂)
  change Int.ModEq (d * d₁ * D : ℕ) (b * (d * d₁ * n₁ : ℕ)) Z ∧
    Int.ModEq k₁ (b * (d * d₁ * n₁ : ℕ)) Z ∧
    Int.ModEq (n₁ * k₂ : ℕ) (b * (d * d₁ * n₁ : ℕ)) Z at ht
  have hKV := (Int.modEq_and_modEq_iff_modEq_mul
    (by simpa only [Int.natAbs_natCast] using hk :
      (k₁ : ℤ).natAbs.Coprime (n₁ * k₂ : ℕ))).mp ⟨ht.2.1, ht.2.2⟩
  have hDK : (d * d₁ * D).Coprime (k₁ * (n₁ * k₂)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hD'.symm
  have hAll := (Int.modEq_and_modEq_iff_modEq_mul
    (by simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hDK)).mp ⟨ht.1, hKV⟩
  have hAll' : Int.ModEq ((d * d₁ * D) * (k₁ * (n₁ * k₂)) : ℕ)
      (b * (d * d₁ * n₁ : ℕ)) Z := by
    simpa only [Nat.cast_mul] using hAll
  have hphase := wPhase_circle_eq_of_modEq
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd hd₁) hDpos)
      (Nat.mul_pos hk₁ (Nat.mul_pos hn₁ hk₂))) hAll'
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hd₁R : (d₁ : ℝ) ≠ 0 := by positivity
  have hDR : (D : ℝ) ≠ 0 := by positivity
  have hk₁R : (k₁ : ℝ) ≠ 0 := by positivity
  have hk₂R : (k₂ : ℝ) ≠ 0 := by positivity
  have hn₁R : (n₁ : ℝ) ≠ 0 := by positivity
  have hleft : (b * (d * d₁ * n₁ : ℕ) : ℤ) /
      (((d * d₁ * D) * (k₁ * (n₁ * k₂)) : ℕ) : ℝ) =
      (b : ℝ) / (q.lcm r : ℝ) := by
    rw [hL]
    push_cast
    field_simp
  rw [hleft] at hphase
  rw [hphase, ← AddCircle.coe_add, ← AddCircle.coe_add]
  congr 1
  dsimp [Z, A, B, C]
  push_cast
  field_simp
  ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
