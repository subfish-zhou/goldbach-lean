import MathlibNt.Wu2004MeanValue.PrincipalWeighted
import MathlibNt.Wu2004MeanValue.EndpointConsumers
import MathlibNt.SieveTheory.LiuPanCofactorReduction

/-!
# Actual AP errors at a common real moving profile

The finite character and cofactor algebra of Pan--Wang--Ding (1975), p. 601,
(2.4), is applied to the actual Wu count, not to a surrogate main term.
The profile and coefficients are common across moduli; the reduced residue
may be chosen separately for each modulus, but not for each source coordinate.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open MathlibNt.SieveTheory.LiuWeight

noncomputable section

def actualAPSum (S : Finset ℕ) (f r : ℕ → ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ S, if m.Coprime d then f m * ebar ((m : ℝ) * r m) d b m else 0

def actualAmplitude (S : Finset ℕ) (f r : ℕ → ℝ) (d : ℕ)
    (χ : DirichletCharacter ℂ d) : ℂ :=
  ∑ m ∈ S, if m.Coprime d then
    (f m : ℂ) * χ (m : ZMod d) * PanLow.coprimePrimePrefix χ ⌊r m⌋₊ d else 0

def actualNonprincipalMass (S : Finset ℕ) (f r : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ d), ‖actualAmplitude S f r d χ‖

private theorem count_characters (r : ℝ) (d b m : ℕ) (hm : 0 < m)
    (hd : 0 < d) (hb : IsUnit (b : ZMod d)) :
    (scaledPrimeCount ((m : ℝ) * r) d b m : ℂ) =
      (d.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ d,
        star (χ (b : ZMod d)) * χ (m : ZMod d) *
          PanLow.coprimePrimePrefix χ ⌊r⌋₊ d := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc : (scaledPrimeCount ((m : ℝ) * r) d b m : ℂ) =
      ∑ p ∈ range (⌊r⌋₊ + 1),
        if p.Prime ∧ m * p ≡ b [MOD d] then (1 : ℂ) else 0 := by
    simp [scaledPrimeCount, scaledPrimeSet, hmR]
  rw [hc]
  calc
    _ = ∑ p ∈ range (⌊r⌋₊ + 1), (d.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ d, star (χ (b : ZMod d)) *
          χ (m : ZMod d) *
            (if p.Prime ∧ p.Coprime d then χ (p : ZMod d) else 0) := by
      apply sum_congr rfl
      intro p _
      rw [show (if p.Prime ∧ m * p ≡ b [MOD d] then (1 : ℂ) else 0) =
          (if p.Prime then (1 : ℂ) else 0) *
            (if m * p ≡ b [MOD d] then (1 : ℂ) else 0) by
          split_ifs <;> simp_all]
      rw [charIndicator_ap hd hb (m * p)]
      simp only [Nat.cast_mul, map_mul, mul_sum]
      apply sum_congr rfl
      intro χ _
      by_cases hp : p.Prime
      · by_cases hpd : p.Coprime d
        · simp only [if_pos (show p.Prime ∧ p.Coprime d from ⟨hp, hpd⟩),
            if_pos hp, one_mul]
          ring
        · simp [hp, hpd, χ.map_nonunit ((ZMod.isUnit_iff_coprime p d).not.mpr hpd)]
      · simp [hp]
    _ = _ := by
      simp only [← mul_sum]
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro χ _
      simp only [PanLow.coprimePrimePrefix, mul_sum]

theorem actualCount_eq_characterMean (S : Finset ℕ) (f r : ℕ → ℝ)
    (d b : ℕ) (hS : ∀ m ∈ S, 0 < m)
    (hd : 0 < d) (hb : IsUnit (b : ZMod d)) :
    (∑ m ∈ S, if m.Coprime d then
      (f m : ℂ) * (scaledPrimeCount ((m : ℝ) * r m) d b m : ℂ) else 0) =
      (d.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ d,
        star (χ (b : ZMod d)) * actualAmplitude S f r d χ := by
  calc
    _ = ∑ m ∈ S, ∑ χ : DirichletCharacter ℂ d,
        (d.totient : ℂ)⁻¹ * star (χ (b : ZMod d)) *
          (if m.Coprime d then (f m : ℂ) * χ (m : ZMod d) *
            PanLow.coprimePrimePrefix χ ⌊r m⌋₊ d else 0) := by
      apply sum_congr rfl
      intro m hm
      by_cases hc : m.Coprime d
      · rw [if_pos hc, count_characters (r m) d b m (hS m hm) hd hb]
        simp only [mul_sum]
        apply sum_congr rfl
        intro χ _
        rw [if_pos hc]
        ring
      · simp [hc]
    _ = _ := by
      rw [sum_comm]
      simp only [actualAmplitude, mul_sum, mul_assoc]

private theorem actualAmplitude_one (S : Finset ℕ) (f r : ℕ → ℝ) (d : ℕ) :
    actualAmplitude S f r d 1 =
      ∑ m ∈ S, if m.Coprime d then
        (f m : ℂ) * (PanPrincipal.coprimePrimeCount ⌊r m⌋₊ d : ℂ) else 0 := by
  unfold actualAmplitude PanLow.coprimePrimePrefix PanPrincipal.coprimePrimeCount
  apply sum_congr rfl
  intro m _
  by_cases hc : m.Coprime d
  · rw [if_pos hc, if_pos hc, MulChar.one_apply ((ZMod.isUnit_iff_coprime m d).mpr hc),
      mul_one]
    congr 1
    simp only [Complex.ofReal_sum]
    apply sum_congr rfl
    intro p _
    by_cases hp : p.Prime ∧ p.Coprime d
    · simp only [if_pos hp,
        MulChar.one_apply ((ZMod.isUnit_iff_coprime p d).mpr hp.2), Complex.ofReal_one]
    · simp [hp]
  · simp [hc]

theorem actualAPSum_eq_characterExpansion (S : Finset ℕ) (f r : ℕ → ℝ)
    (d b : ℕ) (hS : ∀ m ∈ S, 0 < m)
    (hd : 0 < d) (hb : IsUnit (b : ZMod d)) :
    (actualAPSum S f r d b : ℂ) =
      ((∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ d),
          star (χ (b : ZMod d)) * actualAmplitude S f r d χ) +
        (coprimePrincipalSum (S.filter (fun m => m.Coprime d)) f r d : ℂ)) /
          (d.totient : ℂ) := by
  let M : ℂ := ∑ m ∈ S, if m.Coprime d then (f m : ℂ) * (wuLi (r m) : ℂ) else 0
  have herr : (actualAPSum S f r d b : ℂ) =
      (∑ m ∈ S, if m.Coprime d then
        (f m : ℂ) * (scaledPrimeCount ((m : ℝ) * r m) d b m : ℂ) else 0) -
        M / d.totient := by
    simp only [actualAPSum, Complex.ofReal_sum, M, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m hm
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (hS m hm).ne'
    by_cases hc : m.Coprime d
    · simp only [if_pos hc, ebar, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_div, Complex.ofReal_natCast, mul_div_cancel_left₀ _ hmR]
      ring
    · simp [hc]
  have hP : (coprimePrincipalSum (S.filter (fun m => m.Coprime d)) f r d : ℂ) =
      actualAmplitude S f r d 1 - M := by
    rw [actualAmplitude_one]
    simp only [coprimePrincipalSum, sum_filter, Complex.ofReal_sum, M, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    by_cases hc : m.Coprime d
    · simp only [if_pos hc, Complex.ofReal_mul, Complex.ofReal_sub]
      ring
    · simp [hc]
  rw [herr, actualCount_eq_characterMean S f r d b hS hd hb, hP]
  have hs := sum_erase_add (univ : Finset (DirichletCharacter ℂ d))
    (fun χ => star (χ (b : ZMod d)) * actualAmplitude S f r d χ)
    (mem_univ (1 : DirichletCharacter ℂ d))
  rw [← hs, MulChar.one_apply hb, star_one, one_mul]
  ring

theorem abs_actualAPSum_le_characterMass (S : Finset ℕ) (f r : ℕ → ℝ)
    (d b : ℕ) (hS : ∀ m ∈ S, 0 < m)
    (hd : 0 < d) (hb : IsUnit (b : ZMod d)) :
    |actualAPSum S f r d b| ≤
      (actualNonprincipalMass S f r d +
        |coprimePrincipalSum (S.filter (fun m => m.Coprime d)) f r d|) / d.totient := by
  have he := congrArg norm (actualAPSum_eq_characterExpansion S f r d b hS hd hb)
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_div, Complex.norm_natCast] at he
  rw [he]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add ?_ (by simp))
  refine (norm_sum_le _ _).trans_eq ?_
  unfold actualNonprincipalMass
  apply sum_congr rfl
  intro χ _
  rw [norm_mul, norm_star, dirichletChar_norm_unit χ hb, one_mul]

def cofactorAmplitude (S : Finset ℕ) (f r : ℕ → ℝ) (h : ℕ)
    {q : ℕ} (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ S, (if m.Coprime h then (f m : ℂ) else 0) * χ.1 (m : ZMod q) *
    ∑ p ∈ Icc 1 ⌊r m⌋₊,
      (if p.Prime ∧ p.Coprime h then (1 : ℂ) else 0) * χ.1 (p : ZMod q)

theorem actualAmplitude_eq_primitive_cofactor (S : Finset ℕ) (f r : ℕ → ℝ)
    (d : ℕ) (hd : 0 < d) (χ : DirichletCharacter ℂ d) :
    actualAmplitude S f r d χ =
      cofactorAmplitude S f r (d / χ.conductor) (conductorPrimitiveCharacter χ) := by
  let : NeZero d := ⟨hd.ne'⟩
  unfold actualAmplitude cofactorAmplitude
  apply sum_congr rfl
  intro m _
  rw [liuPan_coprimePrimePrefix_eq_primitive, PanLow.coprimePrimePrefix_eq_Icc]
  have hs := liuPan_screened_character_eq_primitive χ m
  have hmul := congrArg (fun z : ℂ => (f m : ℂ) * z *
    ∑ p ∈ Icc 1 ⌊r m⌋₊,
      (if p.Prime ∧ p.Coprime (d / χ.conductor) then (1 : ℂ) else 0) *
        χ.primitiveCharacter (p : ZMod χ.conductor)) hs
  simpa only [conductorPrimitiveCharacter_val, mul_ite, ite_mul, mul_zero, zero_mul] using hmul

theorem actualNonprincipalMass_eq_primitive_cofactor (S : Finset ℕ) (f r : ℕ → ℝ)
    (d : ℕ) (hd : 0 < d) :
    actualNonprincipalMass S f r d =
      ∑ q ∈ d.divisors, ∑ χ ∈ PanLow.nonprincipalPrimitiveCharacters q,
        ‖cofactorAmplitude S f r (d / q) χ‖ := by
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ :=
    fun q χ => ‖cofactorAmplitude S f r (d / q) χ‖
  change actualNonprincipalMass S f r d =
    ∑ q ∈ d.divisors, ∑ χ ∈ PanLow.nonprincipalPrimitiveCharacters q, F q χ
  calc
    _ = ∑ χ ∈ nonprincipalCharacters d, F χ.conductor (conductorPrimitiveCharacter χ) := by
      apply sum_congr rfl
      intro χ _
      exact congrArg norm (actualAmplitude_eq_primitive_cofactor S f r d hd χ)
    _ = ∑ q ∈ nonprincipalConductors d, ∑ χ : PrimitiveCharacter q, F q χ :=
      sum_nonprincipal_by_conductor hd F
    _ = ∑ q ∈ nonprincipalConductors d,
        ∑ χ ∈ PanLow.nonprincipalPrimitiveCharacters q, F q χ := by
      apply sum_congr rfl
      intro q hq
      rw [PanLow.nonprincipalPrimitiveCharacters_eq_univ (mem_filter.mp hq).2]
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro q hq hn
      have hq0 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hq).1 hd
      have hq2 : ¬ 2 ≤ q := fun h => hn (mem_filter.mpr ⟨hq, h⟩)
      have hq1 : q = 1 := by omega
      subst q
      simp

def cofactorLedger (S : Finset ℕ) (f r : ℕ → ℝ) (h Q : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, (q.totient : ℝ)⁻¹ *
    ∑ χ ∈ PanLow.nonprincipalPrimitiveCharacters q, ‖cofactorAmplitude S f r h χ‖

theorem actualNonprincipal_sum_le_cofactor (S : Finset ℕ) (f r : ℕ → ℝ) (Q : ℕ) :
    (∑ d ∈ Icc 1 Q, (d.totient : ℝ)⁻¹ * actualNonprincipalMass S f r d) ≤
      ∑ h ∈ Icc 1 Q, (h.totient : ℝ)⁻¹ * cofactorLedger S f r h Q := by
  let F : ℕ → ℕ → ℝ := fun h q =>
    ∑ χ ∈ PanLow.nonprincipalPrimitiveCharacters q, ‖cofactorAmplitude S f r h χ‖
  have hF : ∀ h q, 0 ≤ F h q := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  calc
    _ = ∑ d ∈ Icc 1 Q, (d.totient : ℝ)⁻¹ * ∑ q ∈ d.divisors, F (d / q) q := by
      apply sum_congr rfl
      intro d hd
      rw [actualNonprincipalMass_eq_primitive_cofactor S f r d (mem_Icc.mp hd).1]
    _ ≤ _ := PanCofactor.weighted_sum_divisors_le_rectangle F hF Q

theorem sum_abs_actualAP_le_principal_add_cofactor (S : Finset ℕ)
    (f r : ℕ → ℝ) (Q : ℕ) (b : ℕ → ℕ) (hS : ∀ m ∈ S, 0 < m)
    (hb : ∀ d ∈ Icc 1 Q, (b d).Coprime d) :
    (∑ d ∈ Icc 1 Q, |actualAPSum S f r d (b d)|) ≤
      (∑ d ∈ Icc 1 Q,
        |coprimePrincipalSum (S.filter (fun m => m.Coprime d)) f r d| / d.totient) +
      ∑ h ∈ Icc 1 Q, (h.totient : ℝ)⁻¹ * cofactorLedger S f r h Q := by
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, (actualNonprincipalMass S f r d +
        |coprimePrincipalSum (S.filter (fun m => m.Coprime d)) f r d|) / d.totient := by
      apply sum_le_sum
      intro d hd
      exact abs_actualAPSum_le_characterMass S f r d (b d) hS
        (mem_Icc.mp hd).1 ((ZMod.isUnit_iff_coprime (b d) d).mpr (hb d hd))
    _ = (∑ d ∈ Icc 1 Q,
        |coprimePrincipalSum (S.filter (fun m => m.Coprime d)) f r d| / d.totient) +
        ∑ d ∈ Icc 1 Q, (d.totient : ℝ)⁻¹ * actualNonprincipalMass S f r d := by
      simp only [div_eq_mul_inv, add_mul]
      rw [sum_add_distrib]
      simp only [mul_comm (actualNonprincipalMass S f r _) _, add_comm]
    _ ≤ _ := add_le_add_right (actualNonprincipal_sum_le_cofactor S f r Q) _

theorem cofactorAmplitude_interval (f r : ℕ → ℝ) (h L U : ℕ)
    {q : ℕ} (χ : PrimitiveCharacter q) :
    cofactorAmplitude (Ioc L U) f r h χ =
      realMovingAmplitude (panSourceG (fun m => (f m : ℂ)) h) (panSourceD h) r L U χ := by
  simp only [cofactorAmplitude, realMovingAmplitude, panSourceG, panSourceD, and_comm]

theorem cofactorLedger_interval (f r : ℕ → ℝ) (h Q L U : ℕ) :
    cofactorLedger (Ioc L U) f r h Q =
      ∑ q ∈ Icc 2 Q, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        ‖realMovingAmplitude (panSourceG (fun m => (f m : ℂ)) h)
          (panSourceD h) r L U χ‖ := by
  symm
  calc
    _ = ∑ q ∈ Icc 2 Q, (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ PanLow.nonprincipalPrimitiveCharacters q,
          ‖cofactorAmplitude (Ioc L U) f r h χ‖ := by
      apply sum_congr rfl
      intro q hq
      rw [PanLow.nonprincipalPrimitiveCharacters_eq_univ (mem_Icc.mp hq).1]
      simp only [cofactorAmplitude_interval]
    _ = _ := by
      apply sum_subset (Icc_subset_Icc (by omega) le_rfl)
      intro q hq hn
      have hq1 : q = 1 := by
        have := mem_Icc.mp hq
        simp only [mem_Icc, not_and] at hn
        omega
      subst q
      simp

end
end Wu2004MeanValue