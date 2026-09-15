import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryPoissonTail

/-!
# An actual W phase: CRT peeling and reciprocal inversion

This is the first reciprocal step of Fouvry (1984), p. 238, (8.14), applied
to the existing product CRT residue. The moduli `q,r` need not be coprime.
The peeled factor `k` is coprime to its complement in their lcm. No five-gcd
decomposition, small-modulus bound, or estimate for the finite remainder is
asserted here. In particular the complementary phase has not been discarded.
-/

noncomputable section

open scoped FourierTransform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Signed Bezout representative of the inverse of `n` modulo `m`. -/
def wPhaseInverse (n m : ℕ) : ℤ := n.gcdA m

theorem wPhaseInverse_spec {n m : ℕ} (h : n.Coprime m) :
    Int.ModEq m ((n : ℤ) * wPhaseInverse n m) 1 := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨n.gcdB m, ?_⟩
  have hb := Nat.gcd_eq_gcd_ab n m
  rw [h.gcd_eq_one, Nat.cast_one] at hb
  dsimp [wPhaseInverse]
  linarith

/-- Integer congruences give equal normalized phases, also for modulus one. -/
theorem wPhase_circle_eq_of_modEq {m : ℕ} (hm : 0 < m) {x y : ℤ}
    (h : Int.ModEq m x y) :
    (((x : ℝ) / m : ℝ) : UnitAddCircle) = ((y : ℝ) / m : ℝ) := by
  obtain ⟨z, hz⟩ := h.dvd
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-z, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hz' : (y : ℝ) - x = m * (z : ℝ) := by exact_mod_cast hz
  simp only [zsmul_eq_mul, Int.cast_neg, mul_one]
  field_simp
  nlinarith

/-- Reciprocal inversion with an arbitrary signed numerator and an actual
congruence. This is `b/k = a/(n*k) - a*bar(k)/n (mod 1)`. -/
theorem wPhase_reciprocity_of_product_congruence
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hc : n.Coprime k)
    {a b : ℤ} (hb : Int.ModEq k (b * n) a) :
    (((b : ℝ) / k : ℝ) : UnitAddCircle) =
      (((a : ℝ) / ((n : ℝ) * k) -
        (a : ℝ) * wPhaseInverse k n / n : ℝ) : UnitAddCircle) := by
  have he : (1 : ℤ) = (k : ℤ) * wPhaseInverse k n + n * k.gcdB n := by
    simpa only [wPhaseInverse, hc.symm.gcd_eq_one, Nat.cast_one]
      using Nat.gcd_eq_gcd_ab k n
  have hi : Int.ModEq k (((a : ℤ) * k.gcdB n) * n) a := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨a * wPhaseInverse k n, ?_⟩
    nlinarith [congrArg (fun z : ℤ ↦ a * z) he]
  have hb' := (product_modEq_iff_of_coprime hc hi).mp hb
  rw [wPhase_circle_eq_of_modEq hk hb']
  congr 1
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have he' : (1 : ℝ) = (k : ℝ) * wPhaseInverse k n + n * (k.gcdB n : ℝ) := by
    exact_mod_cast he
  push_cast
  field_simp
  nlinarith [congrArg (fun z : ℝ ↦ (a : ℝ) * z) he']

/-- A coprime CRT peel followed by reciprocal inversion. The input `b` is
arbitrary; its product congruence, rather than a phase identity, is the premise. -/
theorem wPhase_circle_peel {n k P : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hP : 0 < P)
    (hkP : k.Coprime P) (hnk : n.Coprime k)
    {a b : ℤ} (hb : Int.ModEq k (b * n) a) :
    (((b : ℝ) / ((k : ℝ) * P) : ℝ) : UnitAddCircle) =
      (((b : ℝ) * wPhaseInverse k P / P : ℝ) : UnitAddCircle) +
        (((a : ℝ) / ((n : ℝ) * k * P) -
          (a : ℝ) * wPhaseInverse k (n * P) / ((n : ℝ) * P) : ℝ) :
            UnitAddCircle) := by
  have he : (1 : ℤ) = k * wPhaseInverse k P + P * k.gcdB P := by
    simpa only [wPhaseInverse, hkP.gcd_eq_one, Nat.cast_one]
      using Nat.gcd_eq_gcd_ab k P
  have hi : Int.ModEq k ((P : ℤ) * k.gcdB P) 1 := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨wPhaseInverse k P, by linarith⟩
  have hb' : Int.ModEq k ((b * k.gcdB P) * (n * P : ℕ)) a := by
    simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm, mul_one]
      using hb.mul hi
  have hr := wPhase_reciprocity_of_product_congruence (Nat.mul_pos hn hP) hk
    (hnk.mul_left hkP.symm) hb'
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hP' : (P : ℝ) ≠ 0 := by positivity
  have he' : (1 : ℝ) = k * (wPhaseInverse k P : ℝ) + P * (k.gcdB P : ℝ) := by
    exact_mod_cast he
  have hs : (b : ℝ) / ((k : ℝ) * P) =
      (b : ℝ) * wPhaseInverse k P / P + (b * k.gcdB P : ℤ) / (k : ℝ) := by
    push_cast
    field_simp
    nlinarith [congrArg (fun z : ℝ ↦ (b : ℝ) * z) he']
  rw [hs, AddCircle.coe_add, hr]
  congr 2
  push_cast
  ring

/-- The reciprocal peel of the original, constructed W residue. Neither
coprimality of `q,r` nor reducedness of the signed residue `a` is imposed. -/
theorem productCRTResidue_phase_peel {q r n₁ n₂ k P : ℕ}
    (hn₁ : 0 < n₁) (hk : 0 < k) (hP : 0 < P)
    (hL : q.lcm r = k * P) (hkq : k ∣ q) (hkP : k.Coprime P)
    (hc : WCompatible q r n₁ n₂) (a : ℤ) :
    (((productCRTResidue q r n₁ n₂ a : ℝ) / (q.lcm r) : ℝ) : UnitAddCircle) =
      (((productCRTResidue q r n₁ n₂ a : ℝ) * wPhaseInverse k P / P : ℝ) :
        UnitAddCircle) +
      (((a : ℝ) / ((n₁ : ℝ) * (q.lcm r)) -
        (a : ℝ) * wPhaseInverse k (n₁ * P) / ((n₁ : ℝ) * P) : ℝ) :
          UnitAddCircle) := by
  have hb := (productCRTResidue_spec a hc).1.of_dvd
    (by exact_mod_cast hkq : (k : ℤ) ∣ q)
  simpa only [hL, Nat.cast_mul, mul_assoc] using
    wPhase_circle_peel hn₁ hk hP hkP (hc.1.of_dvd_right hkq) hb

private theorem wPhase_fourier_add (h : ℤ) (x y : UnitAddCircle) :
    fourier h (x + y) = fourier h x * fourier h y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The actual Fourier phase has a complementary CRT factor, a slow real
factor, and a reciprocal factor. The complementary modulus is `P`, not yet
the small modulus `D` of the five-gcd decomposition. -/
theorem productCRTResidue_fourier_peel {q r n₁ n₂ k P : ℕ}
    (hn₁ : 0 < n₁) (hk : 0 < k) (hP : 0 < P)
    (hL : q.lcm r = k * P) (hkq : k ∣ q) (hkP : k.Coprime P)
    (hc : WCompatible q r n₁ n₂) (a h : ℤ) :
    fourier h (((productCRTResidue q r n₁ n₂ a : ℝ) / (q.lcm r) : ℝ) :
      UnitAddCircle) =
      fourier h (((productCRTResidue q r n₁ n₂ a : ℝ) *
        wPhaseInverse k P / P : ℝ) : UnitAddCircle) *
      fourier h (((a : ℝ) / ((n₁ : ℝ) * (q.lcm r)) : ℝ) : UnitAddCircle) *
      fourier h ((-((a : ℝ) * wPhaseInverse k (n₁ * P) /
        ((n₁ : ℝ) * P)) : ℝ) : UnitAddCircle) := by
  rw [productCRTResidue_phase_peel hn₁ hk hP hL hkq hkP hc,
    sub_eq_add_neg, AddCircle.coe_add, wPhase_fourier_add, wPhase_fourier_add]
  exact (mul_assoc _ _ _).symm

/-- A reciprocal representation of the actual frequency, not a replacement
by its absolute value. All three phase factors and the zero cutoff remain. -/
def wPeeledPoissonFrequency (M : ℝ) (a : ℤ) (q r n₁ n₂ k P : ℕ) (h : ℤ) : ℂ :=
  if h = 0 then 0 else
    (M / (q.lcm r : ℝ)) •
        (𝓕 dyadicCutoffSchwartz) ((M / (q.lcm r : ℝ)) * h) *
      fourier h (((productCRTResidue q r n₁ n₂ a : ℝ) *
        wPhaseInverse k P / P : ℝ) : UnitAddCircle) *
      fourier h (((a : ℝ) / ((n₁ : ℝ) * (q.lcm r)) : ℝ) : UnitAddCircle) *
      fourier h ((-((a : ℝ) * wPhaseInverse k (n₁ * P) /
        ((n₁ : ℝ) * P)) : ℝ) : UnitAddCircle)

theorem wPoissonFrequency_eq_peeled {q r n₁ n₂ k P : ℕ}
    (hn₁ : 0 < n₁) (hk : 0 < k) (hP : 0 < P)
    (hL : q.lcm r = k * P) (hkq : k ∣ q) (hkP : k.Coprime P)
    (hc : WCompatible q r n₁ n₂) (M : ℝ) (a h : ℤ) :
    wPoissonFrequency M a q r n₁ n₂ h =
      wPeeledPoissonFrequency M a q r n₁ n₂ k P h := by
  unfold wPoissonFrequency dyadicCutoffPoissonRemainder wPeeledPoissonFrequency
  split_ifs
  · rfl
  · rw [productCRTResidue_fourier_peel hn₁ hk hP hL hkq hkP hc]
    simp only [mul_assoc]

/-- Exact propagation to the existing retained finite W remainder. The
factorization depends only on the modulus pair, and signed coefficients
are untouched. No coprimality between the original two moduli is required. -/
theorem truncatedWNonzeroMode_eq_peeled
    (M : ℝ) (H k P : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ)
    (hN : ∀ n ∈ N, 0 < n)
    (hfac : ∀ q ∈ reducedModuli Q a, ∀ r ∈ reducedModuli Q a,
      0 < k q r ∧ 0 < P q r ∧ q.lcm r = k q r * P q r ∧
        k q r ∣ q ∧ (k q r).Coprime (P q r)) :
    truncatedWNonzeroMode M H N Q β c a =
      ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
        ∑ n₁ ∈ N, ∑ n₂ ∈ N,
          if WCompatible q r n₁ n₂ then
            (c q * c r * β n₁ * β n₂) *
              (∑ h ∈ Finset.Icc (-(H q r : ℤ)) (H q r),
                wPeeledPoissonFrequency M a q r n₁ n₂ (k q r) (P q r) h).re
          else 0 := by
  classical
  unfold truncatedWNonzeroMode
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  obtain ⟨hk, hP, hL, hkq, hkP⟩ := hfac q hq r hr
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  apply Finset.sum_congr rfl
  intro n₂ _
  split_ifs with hc
  · congr 2
    apply Finset.sum_congr rfl
    intro h _
    exact wPoissonFrequency_eq_peeled (hN n₁ hn₁) hk hP hL hkq hkP hc M a h
  · rfl

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
