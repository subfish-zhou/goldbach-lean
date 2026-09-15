import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanActualCountCharacters
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerLargeSieve
import MathlibNt.AnalyticNumberTheory.LargeSieve.ConductorChangeLevelLedger
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowCarrierCorrection

/-! Pan--Wang--Ding p.601: the primitive regrouping is (2.4), while
(2.5) is the principal PNT estimate.  The two cofactor screens are (2.6)--(2.8).
This file only supplies exact finite equalities, keeping the whole a-sum. -/
noncomputable section
open scoped BigOperators
open Classical Finset
open AnalyticNumberTheory.LargeSieve
namespace MathlibNt.SieveTheory.LiuWeight

/-- The old level screen becomes precisely the complementary-factor screen.
The conductor's own nonunit zeros are supplied by the primitive character. -/
theorem liuPan_screened_character_eq_primitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (if n.Coprime q then χ (n : ZMod q) else 0) =
      if n.Coprime (q / χ.conductor) then
        χ.primitiveCharacter (n : ZMod χ.conductor) else 0 := by
  have hs : (if n.Coprime q then χ (n : ZMod q) else 0) =
      χ (n : ZMod q) := by
    by_cases h : n.Coprime q
    · simp [h]
    · simp [h, χ.map_nonunit ((ZMod.isUnit_iff_coprime n q).not.mpr h)]
  rw [hs, dirichletCharacter_eq_primitive_mul_coprimeIndicator]
  split_ifs <;> simp

/-- Actual primes, not von Mangoldt: change conductor and keep the cofactor. -/
theorem liuPan_coprimePrimePrefix_eq_primitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (y : ℕ) :
    PanLow.coprimePrimePrefix χ y q =
      PanLow.coprimePrimePrefix χ.primitiveCharacter y (q / χ.conductor) := by
  unfold PanLow.coprimePrimePrefix
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simpa only [hp, true_and] using liuPan_screened_character_eq_primitive χ n
  · simp [hp]

/-- Exact induced complete-amplitude identity. Both complementary-factor
screens remain inside the complete source sum; no a-triangle is used. -/
theorem liuPanActualCharacterAmplitude_eq_primitive_cofactor
    (N A₁ A₂ q : ℕ) (f : ℕ → ℝ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) :
    liuPanActualCharacterAmplitude N A₁ A₂ q f χ =
      panSourceCharacterAmplitude
        (fun a => if a.Coprime (q / χ.conductor) then (f a : ℂ) else 0)
        (fun p => if p.Prime ∧ p.Coprime (q / χ.conductor) then 1 else 0)
        N A₁ A₂ (conductorPrimitiveCharacter χ) := by
  let : NeZero q := ⟨hq.ne'⟩
  unfold liuPanActualCharacterAmplitude panSourceCharacterAmplitude
  apply sum_congr rfl
  intro a _
  change (if a.Coprime q then (f a : ℂ) * χ (a : ZMod q) *
      PanLow.coprimePrimePrefix χ (N / a) q else 0) = _
  rw [liuPan_coprimePrimePrefix_eq_primitive,
    PanLow.coprimePrimePrefix_eq_Icc]
  have hscreen := liuPan_screened_character_eq_primitive χ a
  change (if a.Coprime q then (f a : ℂ) * χ (a : ZMod q) * _ else 0) =
    (if a.Coprime (q / χ.conductor) then (f a : ℂ) else 0) *
      χ.primitiveCharacter (a : ZMod χ.conductor) * _
  -- Weight the screened identity by the unchanged complete prime prefix.
  have hweighted := congrArg (fun z : ℂ => (f a : ℂ) * z *
    PanLow.coprimePrimePrefix χ.primitiveCharacter (N / a) (q / χ.conductor)) hscreen
  simpa only [PanLow.coprimePrimePrefix_eq_Icc, conductorPrimitiveCharacter_val,
    mul_ite, ite_mul, mul_zero, zero_mul] using hweighted

/-- Pan's exact same-modulus nonprincipal mass, indexed by the unique primitive
conductor. The conductor-one carrier is empty, and neither cofactor screen
nor cancellation across the full a-sum is discarded. -/
theorem liuPanActualNonprincipalMass_eq_primitive_cofactor
    (N A₁ A₂ q : ℕ) (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanActualNonprincipalMass N A₁ A₂ q f =
      ∑ d ∈ q.divisors, ∑ ψ ∈ PanLow.nonprincipalPrimitiveCharacters d,
        ‖panSourceCharacterAmplitude
          (fun a => if a.Coprime (q / d) then (f a : ℂ) else 0)
          (fun p => if p.Prime ∧ p.Coprime (q / d) then 1 else 0)
          N A₁ A₂ ψ‖ := by
  let F : (d : ℕ) → PrimitiveCharacter d → ℝ := fun d ψ =>
    ‖panSourceCharacterAmplitude
      (fun a => if a.Coprime (q / d) then (f a : ℂ) else 0)
      (fun p => if p.Prime ∧ p.Coprime (q / d) then 1 else 0)
      N A₁ A₂ ψ‖
  change liuPanActualNonprincipalMass N A₁ A₂ q f =
    ∑ d ∈ q.divisors, ∑ ψ ∈ PanLow.nonprincipalPrimitiveCharacters d, F d ψ
  calc
    _ = ∑ χ ∈ nonprincipalCharacters q,
        F χ.conductor (conductorPrimitiveCharacter χ) := by
      apply sum_congr rfl
      intro χ _
      exact congrArg norm (liuPanActualCharacterAmplitude_eq_primitive_cofactor
        N A₁ A₂ q f hq χ)
    _ = ∑ d ∈ nonprincipalConductors q, ∑ ψ : PrimitiveCharacter d, F d ψ :=
      sum_nonprincipal_by_conductor hq F
    _ = ∑ d ∈ nonprincipalConductors q,
        ∑ ψ ∈ PanLow.nonprincipalPrimitiveCharacters d, F d ψ := by
      apply sum_congr rfl
      intro d hd
      rw [PanLow.nonprincipalPrimitiveCharacters_eq_univ (mem_filter.mp hd).2]
    _ = ∑ d ∈ q.divisors,
        ∑ ψ ∈ PanLow.nonprincipalPrimitiveCharacters d, F d ψ := by
      apply sum_subset (filter_subset _ _)
      intro d hd hnot
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hq
      have hdlt : ¬ 2 ≤ d := by
        intro h
        exact hnot (mem_filter.mpr ⟨hd, h⟩)
      have hd1 : d = 1 := by omega
      subst d
      simp

end MathlibNt.SieveTheory.LiuWeight