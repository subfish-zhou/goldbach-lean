import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryReciprocalCorrelation

/-!
# Reciprocal cancellation on unit-step arithmetic progressions

The step is a unit modulo the modulus, not necessarily one as an integer.
The integer parameter retains its multiplicity on intervals longer than the
modulus. Only the inherent nonunit vanishing of `reciprocalPhase` is imposed.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The actual unweighted sum over the integer parameter `X < t ≤ Y`. -/
def reciprocalProgression (q : ℕ) [NeZero q] (d b : ℤ) (v : ℕ)
    (X Y : ℤ) : ℂ :=
  ∑ t ∈ Finset.Ioc X Y, reciprocalPhase q d ((b + (v : ℤ) * t : ℤ) : ZMod q)

/-- Multiplying the argument by a unit twists only the frequency. -/
theorem reciprocalPhase_unit_mul {q v : ℕ} [NeZero q] (hv : v.Coprime q)
    (d : ℤ) (z : ZMod q) :
    reciprocalPhase q d ((v : ZMod q) * z) =
      reciprocalPhase q (d * wPhaseInverse v q) z := by
  have hu : IsUnit (v : ZMod q) := (ZMod.isUnit_iff_coprime v q).mpr hv
  by_cases hz : IsUnit z
  · have hi : ((v : ZMod q) * z)⁻¹ = (v : ZMod q)⁻¹ * z⁻¹ := by
      apply ZMod.inv_eq_of_mul_eq_one
      calc
        (v : ZMod q) * z * ((v : ZMod q)⁻¹ * z⁻¹) =
            ((v : ZMod q) * (v : ZMod q)⁻¹) * (z * z⁻¹) := by ring
        _ = 1 := by rw [ZMod.mul_inv_of_unit _ hu, ZMod.mul_inv_of_unit _ hz, one_mul]
    simp only [reciprocalPhase, if_pos (hu.mul hz), if_pos hz, Int.cast_mul,
      iv3_wPhaseInverse_zmod hv, hi, mul_assoc]
  · have hn : ¬ IsUnit ((v : ZMod q) * z) := fun h ↦ hz (IsUnit.mul_iff.mp h).2
    simp only [reciprocalPhase, if_neg hn, if_neg hz]

/-- Exact reduction to a shifted integer interval. There is no reduction of
the parameter modulo `q`, so repeated residues are counted correctly. -/
theorem reciprocalProgression_eq_reciprocalInterval {q v : ℕ} [NeZero q]
    (hv : v.Coprime q) (d b X Y : ℤ) :
    reciprocalProgression q d b v X Y =
      reciprocalInterval q (d * wPhaseInverse v q)
        (X + b * wPhaseInverse v q : ℤ) (Y + b * wPhaseInverse v q : ℤ) := by
  have he (t : ℤ) :
      ((b + (v : ℤ) * t : ℤ) : ZMod q) =
        (v : ZMod q) * ((t + b * wPhaseInverse v q : ℤ) : ZMod q) := by
    push_cast
    rw [iv3_wPhaseInverse_zmod hv]
    calc
      (b : ZMod q) + v * t = v * t + b * ((v : ZMod q) * (v : ZMod q)⁻¹) := by
        rw [ZMod.coe_mul_inv_eq_one v hv]
        ring
      _ = _ := by ring
  unfold reciprocalProgression reciprocalInterval
  simp only [Int.floor_intCast]
  simp_rw [he, reciprocalPhase_unit_mul hv]
  apply Finset.sum_bij (fun (t : ℤ) _ ↦ t + b * wPhaseInverse v q)
  · intro t ht
    simpa only [Finset.mem_Ioc, add_lt_add_iff_right, add_le_add_iff_right] using ht
  · intro t _ u _ h
    exact add_right_cancel h
  · intro t ht
    refine ⟨t - b * wPhaseInverse v q, ?_, by ring⟩
    simp only [Finset.mem_Ioc] at ht ⊢
    omega
  · intro t _
    rfl

/-- The same short-interval constant works uniformly in the start and step. -/
theorem reciprocalProgression_short_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d b : ℤ) (v : ℕ) (X Y : ℤ),
      v.Coprime q → X ≤ Y → Y - X ≤ q →
      ‖reciprocalProgression q d b v X Y‖ ≤
        C * Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocalInterval_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro q hq d b v X Y hv hXY hlen
  rw [reciprocalProgression_eq_reciprocalInterval hv]
  have hb := hbound q hq (d * wPhaseInverse v q)
    (X + b * wPhaseInverse v q : ℤ) (Y + b * wPhaseInverse v q : ℤ)
    (by
      push_cast
      have hh : (X : ℝ) ≤ Y := by exact_mod_cast hXY
      linarith)
    (by
      push_cast
      have hh : (Y : ℝ) - X ≤ q := by exact_mod_cast hlen
      linarith)
  rw [iv3_gcd_inverse_twist hv] at hb
  exact hb

/-- Exact adjacent-interval splitting, also for intervals longer than `q`. -/
theorem reciprocalProgression_add (q : ℕ) [NeZero q] (d b : ℤ) (v : ℕ)
    {X M Y : ℤ} (hXM : X ≤ M) (hMY : M ≤ Y) :
    reciprocalProgression q d b v X M + reciprocalProgression q d b v M Y =
      reciprocalProgression q d b v X Y := by
  have he : Finset.Ioc X Y = Finset.Ioc X M ∪ Finset.Ioc M Y := by
    ext t
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Ioc X M) (Finset.Ioc M Y) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    simp only [Finset.mem_Ioc] at ht ht'
    omega
  unfold reciprocalProgression
  rw [he, Finset.sum_union hd]

/-- Unconditional individual cancellation on an arbitrarily long AP.
The constant is precisely a short-interval Fouvry constant; there is no
additional constant loss. The length factor counts successive modulus-sized
blocks without identifying repeated residues. -/
theorem reciprocalProgression_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d b : ℤ) (v : ℕ) (X Y : ℤ),
      v.Coprime q → X ≤ Y →
      ‖reciprocalProgression q d b v X Y‖ ≤
        C * (1 + ((Y : ℝ) - X) / q) * Real.sqrt (q.gcd d.natAbs) *
          (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocalProgression_short_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro q hq d b v X Y hv hXY
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  let B : ℝ := C * Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have H (n : ℕ) : ∀ (U V : ℤ), U ≤ V → (V - U).toNat = n →
      ‖reciprocalProgression q d b v U V‖ ≤ (1 + ((V : ℝ) - U) / q) * B := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U V hUV hn
      by_cases hlen : V - U ≤ (q : ℤ)
      · have hb := hbound q hq d b v U V hv hUV hlen
        have hnonneg : 0 ≤ ((V : ℝ) - U) / q :=
          div_nonneg (sub_nonneg.mpr (by exact_mod_cast hUV)) hqr.le
        change ‖reciprocalProgression q d b v U V‖ ≤ (1 + ((V : ℝ) - U) / q) * B
        change ‖reciprocalProgression q d b v U V‖ ≤ B at hb
        nlinarith
      · have hUM : U ≤ U + (q : ℤ) := by omega
        have hMV : U + (q : ℤ) ≤ V := by omega
        have hlt : (V - (U + (q : ℤ))).toNat < n := by omega
        have ht := ih _ hlt (U + q) V hMV rfl
        have hb := hbound q hq d b v U (U + q) hv hUM (by omega)
        rw [← reciprocalProgression_add q d b v hUM hMV]
        calc
          _ ≤ ‖reciprocalProgression q d b v U (U + q)‖ +
              ‖reciprocalProgression q d b v (U + q) V‖ := norm_add_le _ _
          _ ≤ B + (1 + ((V : ℝ) - ((U + (q : ℤ) : ℤ) : ℝ)) / q) * B :=
            add_le_add hb ht
          _ = (1 + ((V : ℝ) - U) / q) * B := by
            push_cast
            field_simp
            ring
  calc
    _ ≤ (1 + ((Y : ℝ) - X) / q) * B := H _ X Y hXY rfl
    _ = _ := by dsimp [B]; ring

/-- Natural parameters use exactly the same integer AP, with no endpoint loss. -/
theorem reciprocalProgression_nat {q : ℕ} [NeZero q] (d : ℤ) (b v X Y : ℕ) :
    (∑ t ∈ Finset.Ioc X Y, reciprocalPhase q d ((b + v * t : ℕ) : ZMod q)) =
      reciprocalProgression q d b v X Y := by
  unfold reciprocalProgression
  apply Finset.sum_bij (fun (t : ℕ) _ ↦ (t : ℤ))
  · intro t ht
    simpa only [Finset.mem_Ioc, Nat.cast_lt, Nat.cast_le] using ht
  · intro t _ u _ he
    exact_mod_cast he
  · intro t ht
    simp only [Finset.mem_Ioc] at ht
    refine ⟨t.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
  · intro t _
    simp only [Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]

/-- The actual paired IV.3 phase on a natural-parameter AP, with only its
coprimality restriction. For positive step, every sampled natural is positive. -/
def iv3CorrelationProgression (D d₁ n n₂ n₂' r s s' : ℕ) (a h h' : ℤ)
    (b v X Y : ℕ) : ℂ :=
  ∑ t ∈ (Finset.Ioc X Y).filter (fun t ↦ (b + v * t).Coprime (n * r * s * s')),
    fourier h (iv3ReciprocalPhase D d₁ n n₂ (b + v * t) r s a) *
      star (fourier h' (iv3ReciprocalPhase D d₁ n n₂' (b + v * t) r s' a))

theorem iv3CorrelationProgression_eq_reciprocalProgression
    {D d₁ n n₂ n₂' r s s' : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s')
    (hB : (D * n₂ * n₂').Coprime (n * r * s * s')) (a h h' : ℤ)
    (b v X Y : ℕ) :
    letI : NeZero (n * r * s * s') := ⟨by positivity⟩
    iv3CorrelationProgression D d₁ n n₂ n₂' r s s' a h h' b v X Y =
      reciprocalProgression (n * r * s * s')
        (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' *
          wPhaseInverse (D * n₂ * n₂') (n * r * s * s')) b v X Y := by
  let : NeZero (n * r * s * s') := ⟨by positivity⟩
  rw [← reciprocalProgression_nat]
  unfold iv3CorrelationProgression
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : (b + v * t).Coprime (n * r * s * s')
  · rw [if_pos ht, iv3_reciprocal_correlation hn hr hs hs' (hB.mul_left ht),
      iv3ReciprocalCircle_eq_reciprocalPhase hB ht]
  · rw [if_neg ht]
    symm
    unfold reciprocalPhase
    rw [if_neg]
    intro hu
    exact ht ((ZMod.isUnit_iff_coprime (b + v * t) (n * r * s * s')).mp hu)

/-- Paired IV.3 cancellation after freezing a residue class, uniformly in its
start and unit step and in the signed residue/frequencies. No extra mask or
arbitrary coefficients are allowed. The parameter interval can be long. -/
theorem iv3CorrelationProgression_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D d₁ n n₂ n₂' r s s' : ℕ) (a h h' : ℤ) (b v X Y : ℕ),
        0 < n → 0 < r → 0 < s → 0 < s' →
        (D * n₂ * n₂').Coprime (n * r * s * s') →
        v.Coprime (n * r * s * s') → X ≤ Y →
        ‖iv3CorrelationProgression D d₁ n n₂ n₂' r s s' a h h' b v X Y‖ ≤
          C * (1 + ((Y : ℝ) - X) / (n * r * s * s' : ℕ)) *
            Real.sqrt ((n * r * s * s').gcd
              (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs) *
            (n * r * s * s' : ℕ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocalProgression_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro D d₁ n n₂ n₂' r s s' a h h' b v X Y hn hr hs hs' hB hv hXY
  let : NeZero (n * r * s * s') := ⟨by positivity⟩
  rw [iv3CorrelationProgression_eq_reciprocalProgression hn hr hs hs' hB]
  have he := hbound (n * r * s * s') inferInstance
    (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' *
      wPhaseInverse (D * n₂ * n₂') (n * r * s * s')) b v X Y hv
    (by exact_mod_cast hXY)
  rw [iv3_gcd_inverse_twist hB] at he
  simpa only [Int.cast_natCast] using he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
