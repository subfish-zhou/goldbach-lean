import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanWangDingSource
import AnalyticNumberTheory.LargeSieve.CharacterIndicators
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEarlySourceReduction

/-! Pan (2.4), first line only: actual prime counts, with the true principal
remainder retained. No analytic estimate or conductor decomposition is used. -/
noncomputable section
open scoped BigOperators
open Finset Classical
open AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
namespace MathlibNt.SieveTheory.LiuWeight

/-- Same-modulus complete amplitude; the whole source sum is inside the norm. -/
def liuPanActualCharacterAmplitude (N A₁ A₂ q : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
    (f a : ℂ) * χ (a : ZMod q) *
      ∑ p ∈ range (N / a + 1),
        if p.Prime ∧ p.Coprime q then χ (p : ZMod q) else 0
  else 0

/-- Raw principal remainder: not divided by phi, and not a free predicate. -/
def liuPanActualPrincipalRaw (main : ℝ → ℝ) (N A₁ A₂ q : ℕ)
    (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
    f a * ((∑ p ∈ range (N / a + 1),
      if p.Prime ∧ p.Coprime q then (1 : ℝ) else 0) - main ((N : ℝ) / a))
  else 0

/-- Every nonprincipal character of the SAME modulus, with no a-triangle. -/
def liuPanActualNonprincipalMass (N A₁ A₂ q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ χ ∈ (univ.erase (1 : DirichletCharacter ℂ q)),
    ‖liuPanActualCharacterAmplitude N A₁ A₂ q f χ‖

private theorem actual_count_range (N a q l : ℕ) (ha : 0 < a) :
    (primesInAPBelow N a q l : ℂ) =
      ∑ p ∈ range (N / a + 1), if p.Prime ∧ a * p ≡ l [MOD q]
        then (1 : ℂ) else 0 := by
  classical
  have hs : (range (N + 1)).filter
      (fun p => p.Prime ∧ a * p ≤ N ∧ a * p ≡ l [MOD q]) =
      (range (N / a + 1)).filter (fun p => p.Prime ∧ a * p ≡ l [MOD q]) := by
    ext p
    simp only [mem_filter, mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨_, hp, hle, hmod⟩
      exact ⟨(Nat.le_div_iff_mul_le ha).mpr (by simpa [mul_comm] using hle), hp, hmod⟩
    · rintro ⟨hle, hp, hmod⟩
      exact ⟨hle.trans (Nat.div_le_self _ _), hp,
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le ha).mp hle, hmod⟩
  rw [primesInAPBelow, hs]
  simp

private theorem actual_count_characters (N a q l : ℕ) (ha : 0 < a)
    (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    (primesInAPBelow N a q l : ℂ) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, star (χ (l : ZMod q)) *
        χ (a : ZMod q) * ∑ p ∈ range (N / a + 1),
          if p.Prime ∧ p.Coprime q then χ (p : ZMod q) else 0 := by
  classical
  rw [actual_count_range N a q l ha]
  calc
    _ = ∑ p ∈ range (N / a + 1), (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, star (χ (l : ZMod q)) *
          χ (a : ZMod q) * (if p.Prime ∧ p.Coprime q then χ (p : ZMod q) else 0) := by
      apply sum_congr rfl
      intro p hp
      rw [show (if p.Prime ∧ a * p ≡ l [MOD q] then (1 : ℂ) else 0) =
          (if p.Prime then (1 : ℂ) else 0) *
            (if a * p ≡ l [MOD q] then (1 : ℂ) else 0) by split_ifs <;> simp_all]
      rw [charIndicator_ap hq hl (a * p)]
      simp only [Nat.cast_mul, map_mul, mul_sum]
      apply sum_congr rfl
      intro χ hχ
      by_cases hprime : p.Prime
      · by_cases hcop : p.Coprime q
        · simp only [if_pos (show p.Prime ∧ p.Coprime q from ⟨hprime, hcop⟩), if_pos hprime, one_mul]
          ring
        · simp [hprime, hcop,
            χ.map_nonunit ((ZMod.isUnit_iff_coprime p q).not.mpr hcop)]
      · simp [hprime]
    _ = _ := by
      simp only [← mul_sum]
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro χ hχ
      rw [mul_sum]

theorem liuPanActualCount_eq_characterMean (N A₁ A₂ q l : ℕ)
    (f : ℕ → ℝ) (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    (∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
      (f a : ℂ) * (primesInAPBelow N a q l : ℂ) else 0) =
    (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      star (χ (l : ZMod q)) * liuPanActualCharacterAmplitude N A₁ A₂ q f χ := by
  classical
  calc
    _ = ∑ a ∈ Ioc A₁ A₂, ∑ χ : DirichletCharacter ℂ q,
        (q.totient : ℂ)⁻¹ * star (χ (l : ZMod q)) *
        (if a.Coprime q then (f a : ℂ) * χ (a : ZMod q) *
          ∑ p ∈ range (N / a + 1),
            if p.Prime ∧ p.Coprime q then χ (p : ZMod q) else 0 else 0) := by
      apply sum_congr rfl
      intro a ha
      by_cases hc : a.Coprime q
      · have ha_pos : 0 < a := (Nat.zero_le A₁).trans_lt (mem_Ioc.mp ha).1
        rw [if_pos hc, actual_count_characters N a q l ha_pos hq hl]
        rw [mul_sum, mul_sum]
        apply sum_congr rfl
        intro χ hχ
        rw [if_pos hc]
        -- Reassociate the complete prime sum without expanding its summands.
        ring
      · simp [hc]
    _ = _ := by
      rw [sum_comm]
      simp only [liuPanActualCharacterAmplitude, mul_sum, mul_assoc]

theorem liuPanActualCharacterAmplitude_one (N A₁ A₂ q : ℕ) (f : ℕ → ℝ) :
    liuPanActualCharacterAmplitude N A₁ A₂ q f 1 =
      ∑ a ∈ Ioc A₁ A₂, if a.Coprime q then (f a : ℂ) *
        ∑ p ∈ range (N / a + 1),
          if p.Prime ∧ p.Coprime q then (1 : ℂ) else 0 else 0 := by
  unfold liuPanActualCharacterAmplitude
  apply sum_congr rfl
  intro a ha
  by_cases hc : a.Coprime q
  · rw [if_pos hc, if_pos hc, MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr hc), mul_one]
    congr 1
    apply sum_congr rfl
    intro p hp
    by_cases h : p.Prime ∧ p.Coprime q
    · rw [if_pos h, if_pos h, MulChar.one_apply ((ZMod.isUnit_iff_coprime p q).mpr h.2)]
    · simp only [if_neg h]
  · simp only [if_neg hc]

/-- Exact complex error decomposition. The phase star(chi(l)) and chi(a)
remain coupled until AFTER the complete source summation. -/
theorem liuMainPanCoprimeIntervalSum_eq_actualCharacterExpansion
    (main : ℝ → ℝ) (N A₁ A₂ q l : ℕ) (f : ℕ → ℝ)
    (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    (liuMainPanCoprimeIntervalSum main N A₁ A₂ q l f : ℂ) =
      ((∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
          star (χ (l : ZMod q)) * liuPanActualCharacterAmplitude N A₁ A₂ q f χ) +
        (liuPanActualPrincipalRaw main N A₁ A₂ q f : ℂ)) / (q.totient : ℂ) := by
  classical
  let M : ℂ := ∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
    (f a : ℂ) * (main ((N : ℝ) / a) : ℂ) else 0
  have herr : (liuMainPanCoprimeIntervalSum main N A₁ A₂ q l f : ℂ) =
      (∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
        (f a : ℂ) * (primesInAPBelow N a q l : ℂ) else 0) - M / q.totient := by
    simp only [liuMainPanCoprimeIntervalSum, liuScaledAPError, Complex.ofReal_sum,
      M, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    by_cases hc : a.Coprime q
    · simp only [if_pos hc, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_div, Complex.ofReal_natCast]
      ring
    · simp [hc]
  have hP : (liuPanActualPrincipalRaw main N A₁ A₂ q f : ℂ) =
      liuPanActualCharacterAmplitude N A₁ A₂ q f 1 - M := by
    rw [liuPanActualCharacterAmplitude_one]
    simp only [liuPanActualPrincipalRaw, Complex.ofReal_sum, M, ← sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    by_cases hc : a.Coprime q
    · simp only [if_pos hc, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_sum,
        apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero]
      ring
    · simp [hc]
  rw [herr, liuPanActualCount_eq_characterMean N A₁ A₂ q l f hq hl, hP]
  have hs := sum_erase_add (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => star (χ (l : ZMod q)) * liuPanActualCharacterAmplitude N A₁ A₂ q f χ)
    (mem_univ (1 : DirichletCharacter ℂ q))
  rw [← hs, MulChar.one_apply hl, star_one, one_mul]
  ring

/-- Only the outer residue phase is removed; each full a-amplitude survives. -/
theorem abs_liuMainPanCoprimeIntervalSum_le_actualCharacterMass
    (main : ℝ → ℝ) (N A₁ A₂ q l : ℕ) (f : ℕ → ℝ)
    (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    |liuMainPanCoprimeIntervalSum main N A₁ A₂ q l f| ≤
      (liuPanActualNonprincipalMass N A₁ A₂ q f +
        |liuPanActualPrincipalRaw main N A₁ A₂ q f|) / q.totient := by
  have hnorm := congrArg norm
    (liuMainPanCoprimeIntervalSum_eq_actualCharacterExpansion main N A₁ A₂ q l f hq hl)
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_div, Complex.norm_natCast] at hnorm
  rw [hnorm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ‖∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
        star (χ (l : ZMod q)) * liuPanActualCharacterAmplitude N A₁ A₂ q f χ‖ +
        ‖(liuPanActualPrincipalRaw main N A₁ A₂ q f : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add
      · calc
          _ ≤ ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
              ‖star (χ (l : ZMod q)) * liuPanActualCharacterAmplitude N A₁ A₂ q f χ‖ :=
            norm_sum_le _ _
          _ = _ := by
            unfold liuPanActualNonprincipalMass
            apply sum_congr rfl
            intro χ hχ
            rw [norm_mul, norm_star, dirichletChar_norm_unit χ hl, one_mul]
      · simp only [Complex.norm_real, Real.norm_eq_abs, le_refl]

/-- Standard reduced-residue maximum, including q=1 and its residue zero. -/
theorem liuMainPanCoprimeIntervalMaxL_le_actualCharacterMass
    (main : ℝ → ℝ) (N A₁ A₂ q : ℕ) (f : ℕ → ℝ) (hq : 0 < q) :
    liuMainPanCoprimeIntervalMaxL main N A₁ A₂ q f ≤
      (liuPanActualNonprincipalMass N A₁ A₂ q f +
        |liuPanActualPrincipalRaw main N A₁ A₂ q f|) / q.totient := by
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  split
  · apply max'_le
    intro x hx
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
    exact abs_liuMainPanCoprimeIntervalSum_le_actualCharacterMass main N A₁ A₂ q l f hq
      ((ZMod.isUnit_iff_coprime l q).mpr (mem_filter.mp hl).2)
  · apply div_nonneg _ (Nat.cast_nonneg _)
    exact add_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) (abs_nonneg _)

/-- The required actual Liu specialization, with real N/a in Li and raw P. -/
theorem liuWeight_intervalMaxL_le_nonprincipal_add_principal
    (κ : ℝ) (N z10 y3 A₁ A₂ q : ℕ) (hq : 1 ≤ q) :
    liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ) N A₁ A₂ q
        (liuWeight N z10 y3) ≤
      (liuPanActualNonprincipalMass N A₁ A₂ q (liuWeight N z10 y3) +
        |liuPanActualPrincipalRaw (liuLogarithmicIntegral κ) N A₁ A₂ q
          (liuWeight N z10 y3)|) / q.totient :=
  liuMainPanCoprimeIntervalMaxL_le_actualCharacterMass _ _ _ _ _ _ hq

@[simp] theorem liuMainPanCoprimeIntervalMaxL_modulus_zero
    (main : ℝ → ℝ) (N A₁ A₂ : ℕ) (f : ℕ → ℝ) :
    liuMainPanCoprimeIntervalMaxL main N A₁ A₂ 0 f = 0 := by
  simp [liuMainPanCoprimeIntervalMaxL]

/-- On primitive inputs this is exactly the existing literal Pan amplitude,
with m=q in both coprimality screens. This is an identity, not a conductor step. -/
theorem liuPanActualCharacterAmplitude_eq_panSource
    (N A₁ A₂ q : ℕ) (f : ℕ → ℝ) (χ : PrimitiveCharacter q) :
    liuPanActualCharacterAmplitude N A₁ A₂ q f χ.1 =
      panSourceCharacterAmplitude
        (fun a => if a.Coprime q then (f a : ℂ) else 0)
        (fun p => if p.Prime ∧ p.Coprime q then (1 : ℂ) else 0)
        N A₁ A₂ χ := by
  unfold liuPanActualCharacterAmplitude panSourceCharacterAmplitude
  dsimp only
  apply sum_congr rfl
  intro a ha
  by_cases hc : a.Coprime q
  · rw [if_pos hc, if_pos hc]
    congr 1
    have hs : (Icc 1 (N / a)) ⊆ range (N / a + 1) := by
      intro p hp
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hp).2)
    calc
      _ = ∑ p ∈ Icc 1 (N / a), if p.Prime ∧ p.Coprime q then χ.1 (p : ZMod q) else 0 := by
        symm
        apply sum_subset hs
        intro p hp hn
        have hp0 : p = 0 := by
          have := mem_range.mp hp
          simp only [mem_Icc, not_and] at hn
          omega
        subst p
        simp [Nat.not_prime_zero]
      _ = _ := by
        apply sum_congr rfl
        intro p hp
        split_ifs <;> simp
  · simp only [if_neg hc, zero_mul]

private theorem characters_modulus_one :
    (univ : Finset (DirichletCharacter ℂ 1)) = {1} := by
  ext χ
  simp only [mem_univ, mem_singleton, true_iff]
  exact Subsingleton.elim _ _

/-- Modulus one has no nonprincipal mass; its canonical residue is zero. -/
@[simp] theorem liuPanActualNonprincipalMass_one
    (N A₁ A₂ : ℕ) (f : ℕ → ℝ) :
    liuPanActualNonprincipalMass N A₁ A₂ 1 f = 0 := by
  simp only [liuPanActualNonprincipalMass, characters_modulus_one, erase_singleton, sum_empty]

theorem liuMainPanCoprimeIntervalMaxL_one_eq_principal
    (main : ℝ → ℝ) (N A₁ A₂ : ℕ) (f : ℕ → ℝ) :
    liuMainPanCoprimeIntervalMaxL main N A₁ A₂ 1 f =
      |liuPanActualPrincipalRaw main N A₁ A₂ 1 f| := by
  have he := liuMainPanCoprimeIntervalSum_eq_actualCharacterExpansion main N A₁ A₂ 1 0 f
    (by omega) ((ZMod.isUnit_iff_coprime 0 1).mpr (by simp))
  simp only [characters_modulus_one, erase_singleton, sum_empty, Nat.totient_one, Nat.cast_one,
    zero_add, div_one] at he
  have hr := Complex.ofReal_injective he
  simp [liuMainPanCoprimeIntervalMaxL, hr]

end MathlibNt.SieveTheory.LiuWeight