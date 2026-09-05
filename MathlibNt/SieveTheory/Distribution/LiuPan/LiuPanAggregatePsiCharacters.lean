import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedAbel
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedAbelDeterministic
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerLargeSieve
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Character reduction for Liu's aggregate psi term

This module gives exact finite character identities for the aggregate
source-convolution psi discrepancy.  It separates the principal character
before any absolute value or character Cauchy--Schwarz inequality, and then
regroups the nonprincipal part by primitive conductor.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset ArithmeticFunction
open Filter
open AnalyticNumberTheory.Sieve
open AnalyticNumberTheory.LargeSieve

/-- The source prefix twisted by a Dirichlet character. -/
noncomputable def liuPanSourceCharacterPrefix
    (A q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ a ∈ Icc 1 A, (f a : ℂ) * χ (a : ZMod q)

/-- The von Mangoldt prefix twisted by a Dirichlet character. -/
noncomputable def liuPanLambdaCharacterPrefix
    (t q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ range (t + 1), (Λ n : ℂ) * χ (n : ZMod q)

/-- The logarithmically normalized von Mangoldt prefix twisted by a Dirichlet
character.  The totalized terms at `0` and `1` vanish. -/
noncomputable def liuPanLogLambdaCharacterPrefix
    (t q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ range (t + 1),
    ((Λ n / Real.log (n : ℝ) : ℝ) : ℂ) * χ (n : ZMod q)

/-- Exact discrete Abel summation for a twisted von Mangoldt prefix. -/
theorem liuPanLogLambdaCharacterPrefix_eq_discreteAbel
    (t q : ℕ) (χ : DirichletCharacter ℂ q) :
    liuPanLogLambdaCharacterPrefix t q χ =
      ((Real.log (t : ℝ))⁻¹ : ℂ) * liuPanLambdaCharacterPrefix t q χ +
        ∑ n ∈ range t, (liuPanInverseLogAbelWeight n : ℂ) *
          liuPanLambdaCharacterPrefix n q χ := by
  let c : ℕ → ℂ := fun n => (Λ n : ℂ) * χ (n : ZMod q)
  have h := Finset.sum_range_by_parts
    (fun n : ℕ => ((Real.log (n : ℝ))⁻¹ : ℂ)) c (t + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at h
  rw [show liuPanLogLambdaCharacterPrefix t q χ =
      ∑ n ∈ range (t + 1), ((Real.log (n : ℝ))⁻¹ : ℂ) * c n by
    unfold liuPanLogLambdaCharacterPrefix c
    apply sum_congr rfl
    intro n hn
    push_cast
    ring]
  rw [h]
  change
    ((Real.log (t : ℝ))⁻¹ : ℂ) * liuPanLambdaCharacterPrefix t q χ -
        ∑ n ∈ range t,
          (((Real.log (n + 1 : ℕ))⁻¹ : ℂ) -
            ((Real.log (n : ℝ))⁻¹ : ℂ)) *
            liuPanLambdaCharacterPrefix n q χ =
      _
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro n hn
  by_cases hn2 : 2 ≤ n
  · simp only [liuPanInverseLogAbelWeight, if_pos hn2]
    push_cast
    ring
  · interval_cases n
    · simp [liuPanInverseLogAbelWeight, liuPanLambdaCharacterPrefix]
    · have hsmall : liuPanLambdaCharacterPrefix 1 q χ = 0 := by
        norm_num [liuPanLambdaCharacterPrefix, Finset.sum_range_succ,
          ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
      simp [liuPanInverseLogAbelWeight, hsmall]

/-- A Dirichlet character kills exactly the nonunit source terms. -/
theorem liuPanSourceCharacterPrefix_eq_coprime
    (A q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) :
    liuPanSourceCharacterPrefix A q f χ =
      ∑ a ∈ Icc 1 A, if a.Coprime q then
        (f a : ℂ) * χ (a : ZMod q) else 0 := by
  unfold liuPanSourceCharacterPrefix
  apply sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · simp [hcop]
  · rw [if_neg hcop,
      χ.map_nonunit ((ZMod.isUnit_iff_coprime a q).not.mpr hcop), mul_zero]

/-- Complex character expansion of one complete AP psi sum. -/
theorem liuPanAPPsi_complex_eq_characterMean
    {t q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    (liuPanAPPsi t q l : ℂ) =
      (Nat.totient q : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          star (χ (l : ZMod q)) * liuPanLambdaCharacterPrefix t q χ := by
  unfold liuPanLambdaCharacterPrefix
  rw [← charSum_ap hq hl (fun n => (Λ n : ℂ)) t]
  unfold liuPanAPPsi
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  by_cases hmod : n ≡ l [MOD q] <;> simp [hmod]

/-- Moving the inverse source residue through conjugation produces the source
character and leaves the common residue phase outside. -/
theorem star_dirichletCharacter_natInvMod_mul
    {q a l : ℕ} (hcop : a.Coprime q) (χ : DirichletCharacter ℂ q) :
    star (χ ((natInvMod q a * l % q : ℕ) : ZMod q)) =
      χ (a : ZMod q) * star (χ (l : ZMod q)) := by
  have hprod : (a : ZMod q) * (natInvMod q a : ZMod q) = 1 := by
    rw [← Nat.cast_mul, ← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ q).mpr (natInvMod_congr hcop)
  have hinvunit : IsUnit (natInvMod q a : ZMod q) := by
    apply IsUnit.of_mul_eq_one (a : ZMod q)
    simpa [mul_comm] using hprod
  have hchar :
      χ (a : ZMod q) * χ (natInvMod q a : ZMod q) = 1 := by
    rw [← map_mul, hprod, map_one]
  rw [show ((natInvMod q a * l % q : ℕ) : ZMod q) =
      (natInvMod q a : ZMod q) * (l : ZMod q) by norm_num]
  rw [map_mul, star_mul']
  congr 1
  calc
    star (χ (natInvMod q a : ZMod q)) =
        (χ (natInvMod q a : ZMod q))⁻¹ :=
      conj_eq_inv_of_norm_eq_one (dirichletChar_norm_unit χ hinvunit)
    _ = χ (a : ZMod q) := (eq_inv_of_mul_eq_one_left hchar).symm

/-- The complex source aggregate before subtracting its uniform main term. -/
noncomputable def liuPanAggregateAPPsiComplex
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  ∑ a ∈ Icc 1 A, if a.Coprime q then
    (f a : ℂ) * (liuPanAPPsi t q (natInvMod q a * l % q) : ℂ)
  else 0

/-- The exact all-character mean for the source aggregate.  The source prefix
and von Mangoldt prefix remain multiplied before any absolute value. -/
noncomputable def liuPanAggregateAPPsiCharacterMean
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
        liuPanLambdaCharacterPrefix t q χ

/-- Exact complex character expansion of the source-aggregated AP psi sum. -/
theorem liuPanAggregateAPPsiComplex_eq_characterMean
    {t A q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q)
    (hl : IsUnit (l : ZMod q)) :
    liuPanAggregateAPPsiComplex t A q l f =
      liuPanAggregateAPPsiCharacterMean t A q l f := by
  classical
  unfold liuPanAggregateAPPsiComplex liuPanAggregateAPPsiCharacterMean
  calc
    _ = ∑ a ∈ Icc 1 A, if a.Coprime q then
          (f a : ℂ) * ((Nat.totient q : ℂ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q,
              star (χ ((natInvMod q a * l % q : ℕ) : ZMod q)) *
                liuPanLambdaCharacterPrefix t q χ)
        else 0 := by
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · rw [if_pos hcop, if_pos hcop,
          liuPanAPPsi_complex_eq_characterMean hq
            (isUnit_natInvMod_mul_residue hq hcop
              ((ZMod.isUnit_iff_coprime l q).mp hl))]
      · simp [hcop]
    _ = ∑ a ∈ Icc 1 A, ∑ χ : DirichletCharacter ℂ q,
          if a.Coprime q then
            (Nat.totient q : ℂ)⁻¹ * star (χ (l : ZMod q)) *
              ((f a : ℂ) * χ (a : ZMod q)) *
                liuPanLambdaCharacterPrefix t q χ
          else 0 := by
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop,
          star_dirichletCharacter_natInvMod_mul hcop, mul_sum]
        apply sum_congr rfl
        intro χ hχ
        ring
      · simp [hcop]
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ a ∈ Icc 1 A,
          if a.Coprime q then
            (Nat.totient q : ℂ)⁻¹ * star (χ (l : ZMod q)) *
              ((f a : ℂ) * χ (a : ZMod q)) *
                liuPanLambdaCharacterPrefix t q χ
          else 0 := by
      rw [sum_comm]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro χ hχ
      rw [liuPanSourceCharacterPrefix_eq_coprime]
      simp only [mul_sum, sum_mul]
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q <;> simp [hcop]
      ring_nf

/-- The principal source prefix is the source sum restricted to units modulo
`q`; in particular it is not generally the unrestricted source sum. -/
theorem liuPanSourceCharacterPrefix_one_eq_coprime
    (A q : ℕ) (f : ℕ → ℝ) :
    liuPanSourceCharacterPrefix A q f (1 : DirichletCharacter ℂ q) =
      ∑ a ∈ Icc 1 A, if a.Coprime q then (f a : ℂ) else 0 := by
  rw [liuPanSourceCharacterPrefix_eq_coprime]
  apply sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · rw [if_pos hcop, if_pos hcop,
      MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr hcop), mul_one]
  · simp [hcop]

/-- Complexification commutes with the source-aggregate AP psi sum. -/
theorem liuPanAggregateAPPsiComplex_eq_real
    (t A q l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateAPPsiComplex t A q l f =
      (∑ a ∈ Icc 1 A, if a.Coprime q then
        f a * liuPanAPPsi t q (natInvMod q a * l % q) else 0 : ℝ) := by
  unfold liuPanAggregateAPPsiComplex
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop, Complex.ofReal_mul]
  · simp [hcop]

/-- The real aggregate discrepancy is the complex AP aggregate minus the exact
principal source main term. -/
theorem liuPanAggregateAPPsiDiscrepancy_complex_eq
    (t A q l : ℕ) (f : ℕ → ℝ) :
    (liuPanAggregateAPPsiDiscrepancy t A q l f : ℂ) =
      liuPanAggregateAPPsiComplex t A q l f -
        liuPanSourceCharacterPrefix A q f
            (1 : DirichletCharacter ℂ q) *
          (t : ℂ) / (Nat.totient q : ℂ) := by
  unfold liuPanAggregateAPPsiDiscrepancy liuPanAPPsiDiscrepancy
  rw [Complex.ofReal_sum]
  calc
    _ = ∑ a ∈ Icc 1 A, if a.Coprime q then
          (f a : ℂ) *
            ((liuPanAPPsi t q (natInvMod q a * l % q) : ℂ) -
              (t : ℂ) / (Nat.totient q : ℂ))
        else 0 := by
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop, Complex.ofReal_mul]
        push_cast
        rfl
      · simp [hcop]
    _ = (∑ a ∈ Icc 1 A, if a.Coprime q then
          (f a : ℂ) *
            (liuPanAPPsi t q (natInvMod q a * l % q) : ℂ)
        else 0) -
        ∑ a ∈ Icc 1 A, if a.Coprime q then
          (f a : ℂ) * (t : ℂ) / (Nat.totient q : ℂ)
        else 0 := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop]
        ring
      · simp [hcop]
    _ = _ := by
      unfold liuPanAggregateAPPsiComplex
      rw [liuPanSourceCharacterPrefix_one_eq_coprime]
      apply congrArg (fun z => _ - z)
      rw [div_eq_mul_inv, sum_mul, sum_mul]
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · rw [if_pos hcop, if_pos hcop]
        ring
      · rw [if_neg hcop, if_neg hcop]
        simp

/-- The exact principal-character contribution to the aggregate discrepancy. -/
noncomputable def liuPanAggregatePrincipalPsiTerm
    (t A q : ℕ) (f : ℕ → ℝ) : ℂ :=
  liuPanSourceCharacterPrefix A q f (1 : DirichletCharacter ℂ q) *
    (liuPanLambdaCharacterPrefix t q (1 : DirichletCharacter ℂ q) - (t : ℂ)) /
      (Nat.totient q : ℂ)

/-- The exact nonprincipal character contribution, with the source and von
Mangoldt prefixes still paired character by character. -/
noncomputable def liuPanAggregateNonprincipalPsiTerm
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
      star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
        liuPanLambdaCharacterPrefix t q χ

/-- The canonical finite character expansion.  Modulus zero is assigned zero;
the positive-modulus theorem below identifies this with the actual aggregate
discrepancy. -/
noncomputable def liuPanAggregatePsiCharacterExpansion
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else liuPanAggregatePrincipalPsiTerm t A q f +
    liuPanAggregateNonprincipalPsiTerm t A q l f

@[simp] theorem liuPanAggregatePsiCharacterExpansion_zero
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiCharacterExpansion t A 0 l f = 0 := by
  simp [liuPanAggregatePsiCharacterExpansion]

/-- Exact principal/nonprincipal character expansion of the aggregate AP psi
discrepancy.  The principal term is
`F₁(A) * (Psi₁(t) - t) / phi(q)` and is not cancelled. -/
theorem liuPanAggregateAPPsiDiscrepancy_complex_eq_characterExpansion
    {t A q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q)
    (hl : IsUnit (l : ZMod q)) :
    (liuPanAggregateAPPsiDiscrepancy t A q l f : ℂ) =
      liuPanAggregatePsiCharacterExpansion t A q l f := by
  classical
  rw [liuPanAggregateAPPsiDiscrepancy_complex_eq,
    liuPanAggregateAPPsiComplex_eq_characterMean f hq hl]
  unfold liuPanAggregateAPPsiCharacterMean
    liuPanAggregatePsiCharacterExpansion
    liuPanAggregatePrincipalPsiTerm liuPanAggregateNonprincipalPsiTerm
    liuPanPrimePowerNonprincipalCharacters
  rw [if_neg hq.ne']
  let G : DirichletCharacter ℂ q → ℂ := fun χ =>
    star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
      liuPanLambdaCharacterPrefix t q χ
  have hsum :
      (∑ χ ∈ (univ.erase (1 : DirichletCharacter ℂ q)), G χ) +
          G (1 : DirichletCharacter ℂ q) =
        ∑ χ : DirichletCharacter ℂ q, G χ :=
    sum_erase_add _ _ (mem_univ _)
  rw [← hsum]
  have hone : (1 : DirichletCharacter ℂ q) (l : ZMod q) = 1 :=
    MulChar.one_apply hl
  dsimp only [G]
  rw [hone]
  simp only [star_one, one_mul]
  ring

/-! ## The exact principal correction -/

/-- The ordinary finite Chebyshev psi prefix. -/
noncomputable def liuPanPsiPrefix (t : ℕ) : ℝ :=
  ∑ n ∈ range (t + 1), Λ n

/-- The finite psi prefix is exactly Chebyshev's real-variable function at
the corresponding natural argument. -/
theorem liuPanPsiPrefix_eq_chebyshevPsi (t : ℕ) :
    liuPanPsiPrefix t = Chebyshev.psi (t : ℝ) := by
  unfold liuPanPsiPrefix
  rw [Chebyshev.psi_eq_sum_range]
  norm_num

/-- The ordinary Chebyshev PNT remainder at a natural argument. -/
noncomputable def liuPanPNTError (t : ℕ) : ℝ :=
  liuPanPsiPrefix t - t

/-- The totalized inverse-log Abel transform of the ordinary PNT remainder. -/
noncomputable def liuPanLogPNTError (t : ℕ) : ℝ :=
  (Real.log (t : ℝ))⁻¹ * liuPanPNTError t +
    ∑ n ∈ range t, liuPanInverseLogAbelWeight n * liuPanPNTError n

/-- The medium PNT supplies a natural, pointwise eventual bound for the
ordinary psi remainder.  The threshold includes all short arguments, where the
logarithmic expression need not be used. -/
theorem eventually_abs_liuPanPNTError_le_mediumPNT :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ t : ℕ, N0 ≤ t →
      |liuPanPNTError t| ≤
        C * t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, h⟩ := MediumPNT
  obtain ⟨C, hC⟩ := h.bound
  rcases (eventually_atTop.1 hC) with ⟨x0, hx⟩
  obtain ⟨N0, hN0⟩ := exists_nat_ge (max x0 1)
  refine ⟨c, hc, |C| + 1, by positivity, N0, ?_⟩
  intro t ht
  have htx0 : x0 ≤ (t : ℝ) :=
    le_trans (le_max_left _ _) (hN0.trans (by exact_mod_cast ht))
  have hg : 0 ≤ (t : ℝ) *
      Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) :=
    mul_nonneg (by positivity) (Real.exp_pos _).le
  have hbound := hx (t : ℝ) htx0
  rw [Real.norm_eq_abs] at hbound
  unfold liuPanPNTError
  rw [liuPanPsiPrefix_eq_chebyshevPsi]
  simp only [Pi.sub_apply, id_eq] at hbound
  calc
    |Chebyshev.psi (t : ℝ) - (t : ℝ)| ≤
        C * ‖(t : ℝ) *
          Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))‖ := hbound
    _ = C * ((t : ℝ) *
          Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hg]
    _ ≤ (|C| + 1) * ((t : ℝ) *
          Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) := by
      apply mul_le_mul_of_nonneg_right _ hg
      nlinarith [le_abs_self C]
    _ = (|C| + 1) * t *
          Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) := by ring

/-- Medium PNT gives every prescribed fixed logarithmic saving for the
ordinary natural psi remainder. -/
theorem eventually_abs_liuPanPNTError_le_div_log_rpow
    (A : ℝ) (_hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ t : ℕ, N0 ≤ t →
      |liuPanPNTError t| ≤ C * t / Real.log t ^ A := by
  obtain ⟨c, hc, hmedium⟩ := MediumPNT
  have ht : Tendsto (fun x : ℝ ↦ Real.log x ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp Real.tendsto_log_atTop
  have hdecay : (fun x : ℝ ↦ Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) =O[atTop]
      (fun x ↦ 1 / Real.log x ^ A) := by
    apply ((isLittleO_exp_neg_mul_rpow_atTop hc (-10 * A)).isBigO.comp_tendsto ht).congr'
    · aesop
    · filter_upwards [eventually_gt_atTop 1] with x hx
      dsimp
      rw [← Real.rpow_mul (Real.log_nonneg hx.le)]
      ring_nf
      rw [Real.rpow_neg (Real.log_nonneg hx.le) A]
  have hpnt : (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ ↦ x / Real.log x ^ A) := by
    have hmul := (Asymptotics.isBigO_refl (fun x : ℝ ↦ x) atTop).mul hdecay
    exact hmedium.trans (by simpa only [one_div, div_eq_mul_inv, one_mul] using hmul)
  obtain ⟨C, hC⟩ := hpnt.bound
  rcases eventually_atTop.1 hC with ⟨x0, hx0⟩
  obtain ⟨N0, hN0⟩ := exists_nat_ge (max x0 2)
  refine ⟨|C| + 1, by positivity, N0, ?_⟩
  intro t ht
  have hNt : (N0 : ℝ) ≤ t := by exact_mod_cast ht
  have ht2 : (2 : ℝ) ≤ t :=
    (le_max_right x0 2).trans (hN0.trans hNt)
  have h := hx0 (t : ℝ)
    ((le_max_left x0 2).trans (hN0.trans hNt))
  rw [Real.norm_eq_abs] at h
  unfold liuPanPNTError
  rw [liuPanPsiPrefix_eq_chebyshevPsi]
  simp only [Pi.sub_apply, id_eq] at h
  have hpos : 0 ≤ (t : ℝ) / Real.log t ^ A := by
    apply div_nonneg (by positivity)
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  calc
    |Chebyshev.psi (t : ℝ) - (t : ℝ)| ≤ C * ‖(t : ℝ) / Real.log t ^ A‖ := h
    _ = C * ((t : ℝ) / Real.log t ^ A) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    _ ≤ (|C| + 1) * ((t : ℝ) / Real.log t ^ A) := by
      apply mul_le_mul_of_nonneg_right _ hpos
      linarith [le_abs_self C]
    _ = (|C| + 1) * t / Real.log t ^ A := by ring

/-- A global linear bound for the ordinary PNT remainder, used only to dispose
of the finite initial segment in Abel summation. -/
theorem abs_liuPanPNTError_le_global_linear (t : ℕ) :
    |liuPanPNTError t| ≤ (Real.log 4 + 5) * t := by
  unfold liuPanPNTError
  rw [liuPanPsiPrefix_eq_chebyshevPsi]
  have hpsi : Chebyshev.psi (t : ℝ) ≤ (Real.log 4 + 4) * t :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  have hpsi0 : 0 ≤ Chebyshev.psi (t : ℝ) := Chebyshev.psi_nonneg _
  have ht0 : 0 ≤ (t : ℝ) := by positivity
  calc
    |Chebyshev.psi (t : ℝ) - (t : ℝ)| ≤
        |Chebyshev.psi (t : ℝ)| + |(t : ℝ)| :=
      by simpa [add_comm] using
        (abs_sub_le (Chebyshev.psi (t : ℝ) - (t : ℝ))
          (Chebyshev.psi (t : ℝ)) 0)
    _ = Chebyshev.psi (t : ℝ) + t := by
      rw [abs_of_nonneg hpsi0, abs_of_nonneg ht0]
    _ ≤ (Real.log 4 + 5) * t := by
      nlinarith

/-- The nonnegative finite Abel weights telescope, uniformly in their upper
endpoint. -/
theorem sum_liuPanInverseLogAbelWeight_le_inv_log_two (t : ℕ) :
    ∑ n ∈ range t, liuPanInverseLogAbelWeight n ≤ (Real.log 2)⁻¹ := by
  by_cases ht : t ≤ 2
  · have hzero : ∑ n ∈ range t, liuPanInverseLogAbelWeight n = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [liuPanInverseLogAbelWeight, if_neg]
      have hnt : n < t := mem_range.mp hn
      omega
    rw [hzero]
    exact inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  · have h2t : 2 ≤ t := by omega
    have hzero : ∑ n ∈ range 2, liuPanInverseLogAbelWeight n = 0 := by
      norm_num [Finset.sum_range_succ, liuPanInverseLogAbelWeight]
    calc
      ∑ n ∈ range t, liuPanInverseLogAbelWeight n =
          ∑ n ∈ range t, liuPanInverseLogAbelWeight n -
            ∑ n ∈ range 2, liuPanInverseLogAbelWeight n := by
        rw [hzero, sub_zero]
      _ = ∑ n ∈ Ico 2 t, liuPanInverseLogAbelWeight n := by
        rw [Finset.sum_Ico_eq_sub _ h2t]
      _ = ∑ n ∈ Ico 2 t,
          ((Real.log (n : ℝ))⁻¹ - (Real.log (n + 1 : ℕ))⁻¹) := by
        apply sum_congr rfl
        intro n hn
        rw [liuPanInverseLogAbelWeight, if_pos (mem_Ico.mp hn).1]
      _ = (Real.log 2)⁻¹ - (Real.log (t : ℝ))⁻¹ := by
        calc
          ∑ n ∈ Ico 2 t,
              ((Real.log (n : ℝ))⁻¹ - (Real.log (n + 1 : ℕ))⁻¹) =
            -(∑ n ∈ Ico 2 t,
              ((Real.log (n + 1 : ℕ))⁻¹ - (Real.log (n : ℝ))⁻¹)) := by
              rw [← Finset.sum_neg_distrib]
              apply sum_congr rfl
              intro n hn
              ring
          _ = -((Real.log (t : ℝ))⁻¹ - (Real.log 2)⁻¹) := by
            rw [Finset.sum_Ico_sub (fun n : ℕ => (Real.log (n : ℝ))⁻¹) h2t]
            norm_num
          _ = _ := by ring
      _ ≤ (Real.log 2)⁻¹ := by
        have hlogt : 0 < Real.log (t : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < t by omega))
        nlinarith [inv_nonneg.mpr hlogt.le]

/-- Away from the totalized exceptional indices, the Abel weight has the
expected logarithmic derivative majorant. -/
theorem liuPanInverseLogAbelWeight_le_div_mul_log_sq (n : ℕ) (hn : 2 ≤ n) :
    liuPanInverseLogAbelWeight n ≤
      1 / ((n : ℝ) * Real.log n ^ 2) := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hn1 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hL : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hM : 0 < Real.log (n + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
  have hLM : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℕ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa [Set.mem_Ioi] using hn0)
      (by simpa [Set.mem_Ioi] using hn1)
      (by exact_mod_cast (Nat.le_succ n))
  have hdiff : Real.log (n + 1 : ℕ) - Real.log (n : ℝ) ≤ (n : ℝ)⁻¹ := by
    rw [← Real.log_div
      (by exact_mod_cast (Nat.ne_of_gt (show 0 < n + 1 by omega)))
      (by exact_mod_cast (Nat.ne_of_gt (show 0 < n by omega)))]
    calc
      Real.log ((n + 1 : ℕ) / n) ≤ ((n + 1 : ℕ) / n) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ = (n : ℝ)⁻¹ := by
        push_cast
        field_simp
        norm_num
  rw [liuPanInverseLogAbelWeight, if_pos hn]
  calc
    (Real.log (n : ℝ))⁻¹ - (Real.log (n + 1 : ℕ))⁻¹ =
        (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) /
          (Real.log (n : ℝ) * Real.log (n + 1 : ℕ)) := by
      field_simp
    _ ≤ (n : ℝ)⁻¹ / (Real.log (n : ℝ) * Real.log (n : ℝ)) :=
      div_le_div₀ (inv_nonneg.mpr hn0.le) hdiff
        (mul_pos hL hL)
        (mul_le_mul_of_nonneg_left hLM hL.le)
    _ = 1 / ((n : ℝ) * Real.log n ^ 2) := by
      rw [show Real.log (n : ℝ) ^ 2 =
        Real.log (n : ℝ) * Real.log (n : ℝ) by ring]
      field_simp

/-- On any tail starting at `L ≥ 2`, the derivative bound for the Abel weights
turns an arbitrary fixed logarithmic PNT majorant into the endpoint scale. -/
theorem sum_Ico_liuPanInverseLogAbelWeight_mul_div_log_pow_le
    (D L t : ℕ) (hL : 2 ≤ L) :
    ∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n *
        ((n : ℝ) / Real.log n ^ D) ≤
      t / Real.log L ^ (D + 2) := by
  have hlogL : 0 < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hright : 0 ≤ (Real.log (L : ℝ)) ^ (D + 2) :=
    pow_nonneg hlogL.le _
  calc
    ∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n *
        ((n : ℝ) / Real.log n ^ D) ≤
      ∑ _n ∈ Ico L t, (Real.log (L : ℝ))⁻¹ ^ (D + 2) := by
        apply sum_le_sum
        intro n hn
        have hnL : L ≤ n := (mem_Ico.mp hn).1
        have hn2 : 2 ≤ n := hL.trans hnL
        have hn0 : 0 < (n : ℝ) := by positivity
        have hlogn : 0 < Real.log (n : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        have hlogLn : Real.log (L : ℝ) ≤ Real.log (n : ℝ) :=
          Real.strictMonoOn_log.monotoneOn
            (by simpa [Set.mem_Ioi] using
              (show (0 : ℝ) < L by positivity))
            (by simpa [Set.mem_Ioi] using hn0)
            (by exact_mod_cast hnL)
        have hpow : Real.log (L : ℝ) ^ (D + 2) ≤
            Real.log (n : ℝ) ^ (D + 2) :=
          pow_le_pow_left₀ hlogL.le hlogLn _
        calc
          liuPanInverseLogAbelWeight n *
              ((n : ℝ) / Real.log n ^ D) ≤
            (1 / ((n : ℝ) * Real.log n ^ 2)) *
              ((n : ℝ) / Real.log n ^ D) :=
            mul_le_mul_of_nonneg_right
              (liuPanInverseLogAbelWeight_le_div_mul_log_sq n hn2)
              (div_nonneg hn0.le (pow_nonneg hlogn.le _))
          _ = (Real.log (n : ℝ))⁻¹ ^ (D + 2) := by
            rw [show Real.log (n : ℝ) ^ 2 =
              Real.log (n : ℝ) * Real.log (n : ℝ) by ring]
            field_simp
            rw [one_div, inv_pow, ← pow_add]
            simp [Nat.add_comm, hlogn.ne']
          _ ≤ (Real.log (L : ℝ))⁻¹ ^ (D + 2) := by
            rw [inv_pow, inv_pow]
            exact inv_anti₀ (pow_pos hlogL _) hpow
    _ = ((t - L : ℕ) : ℝ) * (Real.log (L : ℝ))⁻¹ ^ (D + 2) := by
      simp [Nat.card_Ico]
    _ ≤ (t : ℝ) * (Real.log (L : ℝ))⁻¹ ^ (D + 2) := by
      gcongr
      exact_mod_cast Nat.sub_le t L
    _ = t / Real.log L ^ (D + 2) := by
      rw [inv_pow]
      ring

/-- A pointwise logarithmic PNT majorant transfers through any Abel tail with
the two extra logarithms supplied by the derivative of the Abel weight. -/
theorem sum_Ico_liuPanInverseLogAbelWeight_mul_absPNTError_le
    (D L t : ℕ) (C : ℝ) (hL : 2 ≤ L) (hC : 0 ≤ C)
    (hPNT : ∀ n : ℕ, L ≤ n →
      |liuPanPNTError n| ≤ C * n / Real.log n ^ D) :
    ∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n * |liuPanPNTError n| ≤
      C * t / Real.log L ^ (D + 2) := by
  calc
    ∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n * |liuPanPNTError n| ≤
      ∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n *
        (C * n / Real.log n ^ D) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        (hPNT n (mem_Ico.mp hn).1)
        (liuPanInverseLogAbelWeight_nonneg n)
    _ = C * ∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n *
        ((n : ℝ) / Real.log n ^ D) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ C * (t / Real.log L ^ (D + 2)) :=
      mul_le_mul_of_nonneg_left
        (sum_Ico_liuPanInverseLogAbelWeight_mul_div_log_pow_le D L t hL)
        hC
    _ = C * t / Real.log L ^ (D + 2) := by ring

/-- The totalized Abel transform of the PNT error has a global linear majorant.
This is the short-range input for the logarithmically saving tail estimate. -/
theorem abs_liuPanLogPNTError_le_global_linear (t : ℕ) :
    |liuPanLogPNTError t| ≤
      (2 * (Real.log 4 + 5) * (Real.log 2)⁻¹) * t := by
  by_cases ht : t ≤ 1
  · interval_cases t
    · simp [liuPanLogPNTError, liuPanPNTError, liuPanPsiPrefix,
        ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
    · simp [liuPanLogPNTError, liuPanPNTError, liuPanPsiPrefix,
        ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
      positivity
  · have ht2 : 2 ≤ t := by omega
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlogt : 0 < Real.log (t : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    have hinv : (Real.log (t : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ := by
      apply inv_anti₀ hlog2
      exact Real.strictMonoOn_log.monotoneOn
        (by norm_num)
        (by simpa [Set.mem_Ioi] using
          (show (0 : ℝ) < t by exact_mod_cast (show 0 < t by omega)))
        (by exact_mod_cast ht2)
    have hK : 0 ≤ Real.log 4 + 5 := by
      have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
      linarith
    have hE : |liuPanPNTError t| ≤ (Real.log 4 + 5) * t :=
      abs_liuPanPNTError_le_global_linear t
    have hsumE :
        |∑ n ∈ range t, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
          ((Real.log 4 + 5) * t) *
            ∑ n ∈ range t, liuPanInverseLogAbelWeight n := by
      calc
        |∑ n ∈ range t, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
            ∑ n ∈ range t,
              |liuPanInverseLogAbelWeight n * liuPanPNTError n| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ range t,
            liuPanInverseLogAbelWeight n * ((Real.log 4 + 5) * t) := by
          apply sum_le_sum
          intro n hn
          rw [abs_mul, abs_of_nonneg (liuPanInverseLogAbelWeight_nonneg n)]
          calc
            liuPanInverseLogAbelWeight n * |liuPanPNTError n| ≤
                liuPanInverseLogAbelWeight n * ((Real.log 4 + 5) * n) :=
              mul_le_mul_of_nonneg_left
                (abs_liuPanPNTError_le_global_linear n)
                (liuPanInverseLogAbelWeight_nonneg n)
            _ ≤ liuPanInverseLogAbelWeight n * ((Real.log 4 + 5) * t) := by
              apply mul_le_mul_of_nonneg_left _ (liuPanInverseLogAbelWeight_nonneg n)
              exact mul_le_mul_of_nonneg_left
                (by exact_mod_cast (Nat.le_of_lt (mem_range.mp hn))) hK
        _ = ((Real.log 4 + 5) * t) *
            ∑ n ∈ range t, liuPanInverseLogAbelWeight n := by
          rw [mul_sum]
          apply sum_congr rfl
          intro n hn
          ring
    unfold liuPanLogPNTError
    calc
      |(Real.log (t : ℝ))⁻¹ * liuPanPNTError t +
          ∑ n ∈ range t, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
        |(Real.log (t : ℝ))⁻¹ * liuPanPNTError t| +
          |∑ n ∈ range t, liuPanInverseLogAbelWeight n * liuPanPNTError n| :=
        abs_add_le _ _
      _ ≤ (Real.log 2)⁻¹ * ((Real.log 4 + 5) * t) +
          ((Real.log 4 + 5) * t) * (Real.log 2)⁻¹ := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hlogt.le)]
          exact mul_le_mul hinv hE (abs_nonneg _) (inv_nonneg.mpr hlog2.le)
        · exact hsumE.trans
            (mul_le_mul_of_nonneg_left
              (sum_liuPanInverseLogAbelWeight_le_inv_log_two t)
              (by positivity))
      _ = (2 * (Real.log 4 + 5) * (Real.log 2)⁻¹) * t := by ring

/-- Every fixed natural logarithmic saving eventually holds for the totalized
inverse-log Abel transform of the ordinary PNT remainder. -/
theorem eventually_abs_liuPanLogPNTError_le_div_log_pow (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ t : ℕ, N0 ≤ t →
      |liuPanLogPNTError t| ≤ C * t / Real.log t ^ A := by
  obtain ⟨C₁, hC₁, N₁, hN₁⟩ :=
    eventually_abs_liuPanPNTError_le_div_log_rpow ((A + 1 : ℕ) : ℝ)
      (by positivity)
  obtain ⟨C₂, hC₂, N₂, hN₂⟩ :=
    eventually_abs_liuPanPNTError_le_div_log_rpow ((A + 10 : ℕ) : ℝ)
      (by positivity)
  have hreal : ∀ᶠ x : ℝ in atTop, Real.log x ^ (A : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    have hbound := (isLittleO_log_rpow_rpow_atTop (A : ℝ)
      (by positivity : (0 : ℝ) < 1 / 2)).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) _), one_mul] at hx
    exact hx
  have hnat : ∀ᶠ t : ℕ in atTop, Real.log (t : ℝ) ^ A ≤ Real.sqrt t := by
    have hcast : Tendsto (fun t : ℕ => (t : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa [Real.sqrt_eq_rpow, Real.rpow_natCast] using hcast.eventually hreal
  rcases eventually_atTop.mp hnat with ⟨N₃, hN₃⟩
  let M : ℕ := max 3 (max N₁ (max N₂ N₃))
  let K : ℝ := (Real.log 4 + 5) * (Real.log 2)⁻¹
  refine ⟨C₁ + K + C₂ * (4 : ℝ) ^ (A + 12), by positivity, M ^ 2, ?_⟩
  intro t ht
  set L : ℕ := t.sqrt
  have hMt : M ^ 2 ≤ t := ht
  have hM3 : 3 ≤ M := by simp [M]
  have hN₁M : N₁ ≤ M := by simp [M]
  have hN₂M : N₂ ≤ M := by simp [M]
  have hN₃M : N₃ ≤ M := by simp [M]
  have hML : M ≤ L := by
    apply Nat.not_lt.mp
    intro hLM
    have hsq : (L + 1) ^ 2 ≤ M ^ 2 :=
      Nat.pow_le_pow_left (Nat.succ_le_of_lt hLM) 2
    have htlt : t < (L + 1) ^ 2 := by
      simpa [L] using Nat.lt_succ_sqrt' t
    exact not_le_of_gt htlt (le_trans hsq hMt)
  have hL3 : 3 ≤ L := hM3.trans hML
  have hL2 : 2 ≤ L := by omega
  have hLt : L ≤ t := by simpa [L] using Nat.sqrt_le_self t
  have hN₁t : N₁ ≤ t := hN₁M.trans <| hML.trans hLt
  have hN₃t : N₃ ≤ t := hN₃M.trans <| hML.trans hLt
  have hLpos : 0 < (L : ℝ) := by
    exact_mod_cast (show 0 < L by omega)
  have htpos : 0 < (t : ℝ) := by
    exact_mod_cast (show 0 < t by omega)
  have hlogL : 0 < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogt : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hlogt_ge_one : 1 ≤ Real.log (t : ℝ) := by
    rw [Real.le_log_iff_exp_le htpos]
    exact le_trans (le_of_lt Real.exp_one_lt_three)
      (by exact_mod_cast hL3.trans hLt)
  have hLscale : (L : ℝ) ≤ (t : ℝ) / Real.log t ^ A := by
    rw [le_div_iff₀ (pow_pos hlogt A)]
    calc
      (L : ℝ) * Real.log (t : ℝ) ^ A ≤ Real.sqrt t * Real.log (t : ℝ) ^ A := by
        gcongr
        simpa [L] using (Real.nat_sqrt_le_real_sqrt (a := t))
      _ ≤ Real.sqrt t * Real.sqrt t := by
        gcongr
        exact hN₃ t hN₃t
      _ = (t : ℝ) := by rw [Real.mul_self_sqrt (by positivity)]
  have htL4 : (t : ℝ) ≤ (L : ℝ) ^ 4 := by
    have htlt : (t : ℝ) < ((L : ℝ) + 1) ^ 2 := by
      exact_mod_cast (Nat.lt_succ_sqrt' t)
    have hsucc : (L : ℝ) + 1 ≤ (2 : ℝ) * L := by
      nlinarith [show (1 : ℝ) ≤ L by exact_mod_cast (show 1 ≤ L by omega)]
    have h2L : (2 : ℝ) * L ≤ (L : ℝ) ^ 2 := by
      nlinarith [show (2 : ℝ) ≤ L by exact_mod_cast hL2]
    calc
      (t : ℝ) ≤ ((L : ℝ) + 1) ^ 2 := le_of_lt htlt
      _ ≤ ((2 : ℝ) * L) ^ 2 := by gcongr
      _ ≤ ((L : ℝ) ^ 2) ^ 2 := by gcongr
      _ = (L : ℝ) ^ 4 := by ring
  have hlogt_le : Real.log (t : ℝ) ≤ 4 * Real.log (L : ℝ) := by
    calc
      Real.log (t : ℝ) ≤ Real.log ((L : ℝ) ^ 4) :=
        Real.strictMonoOn_log.monotoneOn htpos (pow_pos hLpos _) htL4
      _ = 4 * Real.log (L : ℝ) := by simp [Real.log_pow]
  have hrelax :
      ∀ {m : ℕ} {C : ℝ}, A ≤ m → 0 ≤ C →
        C * (t : ℝ) / Real.log t ^ m ≤ C * t / Real.log t ^ A := by
    intro m C hAm hC
    have hpow : Real.log (t : ℝ) ^ A ≤ Real.log (t : ℝ) ^ m :=
      pow_le_pow_right₀ hlogt_ge_one hAm
    have hinv : (Real.log (t : ℝ) ^ m)⁻¹ ≤ (Real.log (t : ℝ) ^ A)⁻¹ :=
      inv_anti₀ (pow_pos hlogt _) hpow
    calc
      C * (t : ℝ) / Real.log t ^ m =
          (C * (t : ℝ)) * (Real.log (t : ℝ) ^ m)⁻¹ := by ring
      _ ≤ (C * (t : ℝ)) * (Real.log (t : ℝ) ^ A)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = C * t / Real.log t ^ A := by ring
  have hendpoint_raw :
      |liuPanPNTError t| ≤ C₁ * t / Real.log t ^ (A + 1) := by
    rw [← Real.rpow_natCast]
    exact hN₁ t hN₁t
  have hendpoint :
      |(Real.log (t : ℝ))⁻¹ * liuPanPNTError t| ≤
        C₁ * t / Real.log t ^ A := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hlogt.le)]
    calc
      (Real.log (t : ℝ))⁻¹ * |liuPanPNTError t| ≤ 1 * |liuPanPNTError t| := by
        gcongr
        simpa using (inv_anti₀ (by norm_num : (0 : ℝ) < 1) hlogt_ge_one)
      _ = |liuPanPNTError t| := by ring
      _ ≤ C₁ * t / Real.log t ^ (A + 1) := hendpoint_raw
      _ ≤ C₁ * t / Real.log t ^ A := hrelax (Nat.le_succ A) hC₁.le
  have hshort_raw :
      |∑ n ∈ range L, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
        K * L := by
    have hK0 : 0 ≤ Real.log 4 + 5 := by
      have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
      linarith
    calc
      |∑ n ∈ range L, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
          ∑ n ∈ range L,
            |liuPanInverseLogAbelWeight n * liuPanPNTError n| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range L,
          liuPanInverseLogAbelWeight n * ((Real.log 4 + 5) * L) := by
        apply sum_le_sum
        intro n hn
        rw [abs_mul, abs_of_nonneg (liuPanInverseLogAbelWeight_nonneg n)]
        calc
          liuPanInverseLogAbelWeight n * |liuPanPNTError n| ≤
              liuPanInverseLogAbelWeight n * ((Real.log 4 + 5) * n) :=
            mul_le_mul_of_nonneg_left (abs_liuPanPNTError_le_global_linear n)
              (liuPanInverseLogAbelWeight_nonneg n)
          _ ≤ liuPanInverseLogAbelWeight n * ((Real.log 4 + 5) * L) := by
            apply mul_le_mul_of_nonneg_left _
              (liuPanInverseLogAbelWeight_nonneg n)
            exact mul_le_mul_of_nonneg_left
              (by exact_mod_cast (Nat.le_of_lt (mem_range.mp hn))) hK0
      _ = ((Real.log 4 + 5) * L) *
          ∑ n ∈ range L, liuPanInverseLogAbelWeight n := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        ring
      _ ≤ ((Real.log 4 + 5) * L) * (Real.log 2)⁻¹ := by
        gcongr
        exact sum_liuPanInverseLogAbelWeight_le_inv_log_two L
      _ = K * L := by
        simp [K]
        ring
  have hshort :
      |∑ n ∈ range L, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
        K * t / Real.log t ^ A := by
    refine hshort_raw.trans ?_
    have hK : 0 ≤ K := by positivity
    calc
      K * L ≤ K * ((t : ℝ) / Real.log t ^ A) :=
        mul_le_mul_of_nonneg_left hLscale hK
      _ = K * t / Real.log t ^ A := by ring
  have htail_abs :
      |∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
        C₂ * t / Real.log L ^ (A + 12) := by
    have htail_sum :
        ∑ n ∈ Ico L t,
            liuPanInverseLogAbelWeight n * |liuPanPNTError n| ≤
          C₂ * t / Real.log L ^ (A + 12) := by
      apply sum_Ico_liuPanInverseLogAbelWeight_mul_absPNTError_le
        (D := A + 10) (L := L) (t := t) (C := C₂) hL2 hC₂.le
      intro n hn
      have hN₂n : N₂ ≤ n := hN₂M.trans (hML.trans hn)
      rw [← Real.rpow_natCast]
      exact hN₂ n hN₂n
    calc
      |∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
          ∑ n ∈ Ico L t,
            |liuPanInverseLogAbelWeight n * liuPanPNTError n| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Ico L t,
          liuPanInverseLogAbelWeight n * |liuPanPNTError n| := by
        apply sum_congr rfl
        intro n hn
        rw [abs_mul, abs_of_nonneg (liuPanInverseLogAbelWeight_nonneg n)]
      _ ≤ C₂ * t / Real.log L ^ (A + 12) := htail_sum
  have htail_scale :
      C₂ * t / Real.log L ^ (A + 12) ≤
        (C₂ * (4 : ℝ) ^ (A + 12)) * t / Real.log t ^ (A + 12) := by
    have hpow :
        Real.log (t : ℝ) ^ (A + 12) ≤
          (4 * Real.log (L : ℝ)) ^ (A + 12) :=
      pow_le_pow_left₀ hlogt.le hlogt_le _
    rw [div_le_div_iff₀ (pow_pos hlogL _) (pow_pos hlogt _)]
    calc
      C₂ * (t : ℝ) * Real.log (t : ℝ) ^ (A + 12) ≤
          C₂ * (t : ℝ) * (4 * Real.log (L : ℝ)) ^ (A + 12) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = C₂ * 4 ^ (A + 12) * t * Real.log (L : ℝ) ^ (A + 12) := by
        rw [mul_pow]
        ring
  have htail :
      |∑ n ∈ Ico L t, liuPanInverseLogAbelWeight n * liuPanPNTError n| ≤
        (C₂ * (4 : ℝ) ^ (A + 12)) * t / Real.log t ^ A := by
    exact htail_abs.trans <| htail_scale.trans <|
      hrelax (Nat.le_add_right A 12) (by positivity)
  have hsplit :
      ∑ n ∈ range t, liuPanInverseLogAbelWeight n * liuPanPNTError n =
        (∑ n ∈ range L,
          liuPanInverseLogAbelWeight n * liuPanPNTError n) +
        ∑ n ∈ Ico L t,
          liuPanInverseLogAbelWeight n * liuPanPNTError n := by
    symm
    simpa [L] using
      (Finset.sum_range_add_sum_Ico
        (fun n => liuPanInverseLogAbelWeight n * liuPanPNTError n) hLt)
  unfold liuPanLogPNTError
  rw [hsplit]
  calc
    |(Real.log (t : ℝ))⁻¹ * liuPanPNTError t +
        ((∑ n ∈ range L,
          liuPanInverseLogAbelWeight n * liuPanPNTError n) +
        ∑ n ∈ Ico L t,
          liuPanInverseLogAbelWeight n * liuPanPNTError n)| ≤
      |(Real.log (t : ℝ))⁻¹ * liuPanPNTError t| +
        |(∑ n ∈ range L,
          liuPanInverseLogAbelWeight n * liuPanPNTError n) +
        ∑ n ∈ Ico L t,
          liuPanInverseLogAbelWeight n * liuPanPNTError n| :=
      abs_add_le _ _
    _ ≤ |(Real.log (t : ℝ))⁻¹ * liuPanPNTError t| +
        (|∑ n ∈ range L,
          liuPanInverseLogAbelWeight n * liuPanPNTError n| +
        |∑ n ∈ Ico L t,
          liuPanInverseLogAbelWeight n * liuPanPNTError n|) :=
      add_le_add le_rfl (abs_add_le _ _)
    _ ≤ C₁ * t / Real.log t ^ A +
        (K * t / Real.log t ^ A +
        (C₂ * (4 : ℝ) ^ (A + 12)) * t / Real.log t ^ A) :=
      add_le_add hendpoint (add_le_add hshort htail)
    _ = (C₁ + K + C₂ * (4 : ℝ) ^ (A + 12)) * t /
        Real.log t ^ A := by ring

/-- Every fixed positive real logarithmic saving eventually holds for the
totalized inverse-log Abel transform of the ordinary PNT remainder. -/
theorem eventually_abs_liuPanLogPNTError_le_div_log_rpow
    (A : ℝ) (_hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ t : ℕ, N0 ≤ t →
      |liuPanLogPNTError t| ≤ C * t / Real.log t ^ A := by
  obtain ⟨C, hC, N0, hN0⟩ :=
    eventually_abs_liuPanLogPNTError_le_div_log_pow (Nat.ceil A)
  refine ⟨C, hC, max N0 3, ?_⟩
  intro t ht
  have hN0t : N0 ≤ t := (le_max_left N0 3).trans ht
  have ht3 : 3 ≤ t := (le_max_right N0 3).trans ht
  have htpos : 0 < (t : ℝ) := by
    exact_mod_cast (show 0 < t by omega)
  have hlogt : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hlogt_ge_one : 1 ≤ Real.log (t : ℝ) := by
    rw [Real.le_log_iff_exp_le htpos]
    exact le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast ht3)
  have hAceil : A ≤ (Nat.ceil A : ℝ) := Nat.le_ceil A
  have hpow :
      Real.log (t : ℝ) ^ A ≤ Real.log (t : ℝ) ^ (Nat.ceil A : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogt_ge_one hAceil
  have hbound :
      |liuPanLogPNTError t| ≤
        C * t / Real.log t ^ (Nat.ceil A : ℝ) := by
    rw [Real.rpow_natCast]
    exact hN0 t hN0t
  calc
    |liuPanLogPNTError t| ≤
        C * t / Real.log t ^ (Nat.ceil A : ℝ) := hbound
    _ ≤ C * t / Real.log t ^ A := by
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogt _)
        (Real.rpow_pos_of_pos hlogt _)]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Totalized inverse-log Abel weights remove the exceptional argument zero. -/
@[simp] theorem liuPanLogPNTError_zero : liuPanLogPNTError 0 = 0 := by
  simp [liuPanLogPNTError, liuPanPNTError, liuPanPsiPrefix]

/-- Totalized inverse-log Abel weights remove the exceptional argument one. -/
@[simp] theorem liuPanLogPNTError_one : liuPanLogPNTError 1 = 0 := by
  simp [liuPanLogPNTError, liuPanPNTError, liuPanPsiPrefix,
    ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]

/-- The part of psi supported on integers not coprime to the modulus.  Since
von Mangoldt is supported on prime powers, these are exactly the prime-power
terms whose prime divides `q`. -/
noncomputable def liuPanPsiNoncoprimeCorrection (t q : ℕ) : ℝ :=
  ∑ n ∈ range (t + 1), if n.Coprime q then 0 else Λ n

/-- The logarithmically normalized noncoprime prime-power correction.  The
terms at `0` and `1` vanish, so this is a total finite sum. -/
noncomputable def liuPanLogNoncoprimeCorrection (t q : ℕ) : ℝ :=
  ∑ n ∈ range (t + 1), if n.Coprime q then 0
    else Λ n / Real.log (n : ℝ)

/-- Discrete Abel summation for the noncoprime prime-power correction. -/
theorem liuPanLogNoncoprimeCorrection_eq_discreteAbel (t q : ℕ) :
    liuPanLogNoncoprimeCorrection t q =
      (Real.log (t : ℝ))⁻¹ * liuPanPsiNoncoprimeCorrection t q +
        ∑ n ∈ range t, liuPanInverseLogAbelWeight n *
          liuPanPsiNoncoprimeCorrection n q := by
  let c : ℕ → ℝ := fun n => if n.Coprime q then 0 else Λ n
  have h := Finset.sum_range_by_parts
    (fun n : ℕ => (Real.log (n : ℝ))⁻¹) c (t + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at h
  rw [show liuPanLogNoncoprimeCorrection t q =
      ∑ n ∈ range (t + 1), (Real.log (n : ℝ))⁻¹ * c n by
    unfold liuPanLogNoncoprimeCorrection c
    apply sum_congr rfl
    intro n hn
    by_cases hcop : n.Coprime q <;>
      simp [hcop, div_eq_inv_mul]]
  rw [h]
  change
    (Real.log (t : ℝ))⁻¹ * liuPanPsiNoncoprimeCorrection t q -
        ∑ n ∈ range t,
          ((Real.log (n + 1 : ℕ))⁻¹ - (Real.log (n : ℝ))⁻¹) *
            liuPanPsiNoncoprimeCorrection n q =
      _
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro n hn
  by_cases hn2 : 2 ≤ n
  · simp only [liuPanInverseLogAbelWeight, if_pos hn2]
    ring
  · interval_cases n
    · simp [liuPanInverseLogAbelWeight, liuPanPsiNoncoprimeCorrection]
    · have hsmall : liuPanPsiNoncoprimeCorrection 1 q = 0 := by
        norm_num [liuPanPsiNoncoprimeCorrection, Finset.sum_range_succ,
          ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
      simp [liuPanInverseLogAbelWeight, hsmall]

/-- The finite number of relevant prime powers: exactly those whose prime
divides the modulus, expressed without choosing that prime. -/
def liuPanNoncoprimePrimePowerCount (t q : ℕ) : ℕ :=
  ((range (t + 1)).filter fun n => ¬n.Coprime q ∧ IsPrimePow n).card

/-- A noncoprime prime power is determined by its unique base prime dividing
the positive modulus and an exponent at most `log₂ N`. -/
theorem liuPanNoncoprimePrimePowerCount_le_primeFactors_mul_log
    (N t q : ℕ) (ht : t ≤ N) (hq : q ≠ 0) :
    liuPanNoncoprimePrimePowerCount t q ≤
      q.primeFactors.card * (1 + Nat.log 2 N) := by
  unfold liuPanNoncoprimePrimePowerCount
  let P := q.primeFactors ×ˢ range (1 + Nat.log 2 N)
  let g : ℕ × ℕ → ℕ := fun pk => pk.1 ^ pk.2
  have hsubset :
      (range (t + 1)).filter (fun n => ¬n.Coprime q ∧ IsPrimePow n) ⊆
        P.image g := by
    intro n hn
    rw [mem_filter, mem_range] at hn
    obtain ⟨k, hklog, hkpos, p, _hp_le, hnpow, hp⟩ :=
      (isPrimePow_nat_iff_bounded_log n).mp hn.2.2
    have hpn : p ∣ n := by
      rw [hnpow]
      exact dvd_pow_self p hkpos.ne'
    obtain ⟨r, hr, hrn, hrq⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hn.2.1
    obtain ⟨u, hu, huniq⟩ :=
      isPrimePow_iff_unique_prime_dvd.mp hn.2.2
    have hpr : p = r :=
      (huniq p ⟨hp, hpn⟩).trans (huniq r ⟨hr, hrn⟩).symm
    rw [mem_image]
    refine ⟨(p, k), ?_, hnpow.symm⟩
    rw [mem_product, mem_range]
    constructor
    · exact hp.mem_primeFactors (hpr ▸ hrq) hq
    · have hkN : k ≤ Nat.log 2 N :=
        hklog.trans
          (Nat.log_mono_right ((Nat.le_of_lt_succ hn.1).trans ht))
      omega
  calc
    ((range (t + 1)).filter fun n => ¬n.Coprime q ∧ IsPrimePow n).card ≤
        (P.image g).card := card_le_card hsubset
    _ ≤ P.card := card_image_le
    _ = q.primeFactors.card * (1 + Nat.log 2 N) := by simp [P]

/-- Prime-power support of von Mangoldt localizes the logarithmic correction
to the displayed finite count. -/
theorem liuPanLogNoncoprimeCorrection_eq_sum_primePowers (t q : ℕ) :
    liuPanLogNoncoprimeCorrection t q =
      ∑ n ∈ (range (t + 1)).filter fun n => ¬n.Coprime q ∧ IsPrimePow n,
        Λ n / Real.log (n : ℝ) := by
  unfold liuPanLogNoncoprimeCorrection
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hcop : n.Coprime q
  · simp [hcop]
  by_cases hpow : IsPrimePow n
  · simp [hcop, hpow]
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]
    simp [hcop, hpow]

/-- Each logarithmically normalized von Mangoldt term on prime-power support
is at most one. -/
theorem liuPanLogNoncoprimeCorrection_le_primePowerCount (t q : ℕ) :
    liuPanLogNoncoprimeCorrection t q ≤
      liuPanNoncoprimePrimePowerCount t q := by
  rw [liuPanLogNoncoprimeCorrection_eq_sum_primePowers]
  calc
    ∑ n ∈ (range (t + 1)).filter fun n => ¬n.Coprime q ∧ IsPrimePow n,
        Λ n / Real.log (n : ℝ) ≤
      ∑ _n ∈ (range (t + 1)).filter fun n => ¬n.Coprime q ∧ IsPrimePow n,
        (1 : ℝ) := by
          apply sum_le_sum
          intro n hn
          have hpow : IsPrimePow n := (mem_filter.mp hn).2.2
          have hlog : 0 < Real.log (n : ℝ) :=
            Real.log_pos (by exact_mod_cast hpow.one_lt)
          calc
            Λ n / Real.log (n : ℝ) ≤
                Real.log (n : ℝ) / Real.log (n : ℝ) :=
              div_le_div_of_nonneg_right
                ArithmeticFunction.vonMangoldt_le_log hlog.le
            _ = 1 := div_self hlog.ne'
    _ = liuPanNoncoprimePrimePowerCount t q := by
      simp [liuPanNoncoprimePrimePowerCount]

/-- The largest prime-power count needed by source quotients with `y ≤ N`. -/
noncomputable def liuPanNoncoprimePrimePowerCountMax (N q : ℕ) : ℝ :=
  ((range (N + 1)).image fun t =>
    (liuPanNoncoprimePrimePowerCount t q : ℝ)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The same prime-factor/exponent count controls every prefix up to `N`. -/
theorem liuPanNoncoprimePrimePowerCountMax_le_primeFactors_mul_log
    (N q : ℕ) (hq : q ≠ 0) :
    liuPanNoncoprimePrimePowerCountMax N q ≤
      (q.primeFactors.card * (1 + Nat.log 2 N) : ℕ) := by
  unfold liuPanNoncoprimePrimePowerCountMax
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨t, ht, rfl⟩
  exact_mod_cast
    liuPanNoncoprimePrimePowerCount_le_primeFactors_mul_log N t q
      (Nat.le_of_lt_succ (mem_range.mp ht)) hq

/-- Uniformly for positive `q ≤ N`, the finite prime-power count costs only
two logarithms. -/
theorem liuPanNoncoprimePrimePowerCountMax_le_log_sq
    (N q : ℕ) (hN : 3 ≤ N) (hq : 0 < q) (hqN : q ≤ N) :
    liuPanNoncoprimePrimePowerCountMax N q ≤
      ((1 / Real.log 2) * (1 + 1 / Real.log 2)) * Real.log N ^ 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < N := by positivity
  have hL : (1 : ℝ) ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hcount :=
    liuPanNoncoprimePrimePowerCountMax_le_primeFactors_mul_log N q hq.ne'
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcount
  by_cases hq1 : q = 1
  · subst q
    have hz : liuPanNoncoprimePrimePowerCountMax N 1 ≤ 0 := by
      simpa using hcount
    exact hz.trans (by positivity)
  · have hq2 : 2 ≤ q := by omega
    have hpf : (q.primeFactors.card : ℝ) ≤ Real.log N / Real.log 2 :=
      (primeFactors_card_cast_le_log hq2).trans
        (div_le_div_of_nonneg_right
          (Real.log_le_log (by positivity) (by exact_mod_cast hqN)) hlog2.le)
    have hnatlog :
        ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log N / Real.log 2 := by
      simpa [Real.log_div_log] using Real.natLog_le_logb N 2
    have hdyadic : (1 : ℝ) + Nat.log 2 N ≤
        (1 + 1 / Real.log 2) * Real.log N := by
      calc
        (1 : ℝ) + Nat.log 2 N ≤ 1 + Real.log N / Real.log 2 := by
          gcongr
        _ ≤ (1 + 1 / Real.log 2) * Real.log N := by
          field_simp
          nlinarith
    calc
      liuPanNoncoprimePrimePowerCountMax N q ≤
          (q.primeFactors.card : ℝ) * ((1 : ℝ) + Nat.log 2 N) := hcount
      _ ≤ (Real.log N / Real.log 2) *
          ((1 + 1 / Real.log 2) * Real.log N) := by gcongr
      _ = ((1 / Real.log 2) * (1 + 1 / Real.log 2)) *
          Real.log N ^ 2 := by ring

theorem liuPanNoncoprimePrimePowerCount_le_max
    {N t q : ℕ} (ht : t ≤ N) :
    liuPanNoncoprimePrimePowerCount t q ≤
      liuPanNoncoprimePrimePowerCountMax N q := by
  unfold liuPanNoncoprimePrimePowerCountMax
  apply le_max'
  exact mem_image.mpr ⟨t, mem_range.mpr (Nat.lt_succ_iff.mpr ht), rfl⟩

theorem liuPanLogNoncoprimeCorrection_le_primePowerCountMax
    {N t q : ℕ} (ht : t ≤ N) :
    liuPanLogNoncoprimeCorrection t q ≤
      liuPanNoncoprimePrimePowerCountMax N q :=
  (liuPanLogNoncoprimeCorrection_le_primePowerCount t q).trans
    (liuPanNoncoprimePrimePowerCount_le_max ht)

/-- Modulus one has no noncoprime prime-power correction. -/
@[simp] theorem liuPanLogNoncoprimeCorrection_one (t : ℕ) :
    liuPanLogNoncoprimeCorrection t 1 = 0 := by
  unfold liuPanLogNoncoprimeCorrection
  apply sum_eq_zero
  intro n hn
  simp

/-- The principal character selects psi minus the noncoprime prime-power
correction. -/
theorem liuPanLambdaCharacterPrefix_one_eq_psi_sub_noncoprime
    (t q : ℕ) :
    liuPanLambdaCharacterPrefix t q (1 : DirichletCharacter ℂ q) =
      (liuPanPsiPrefix t : ℂ) -
        (liuPanPsiNoncoprimeCorrection t q : ℂ) := by
  unfold liuPanLambdaCharacterPrefix liuPanPsiPrefix
    liuPanPsiNoncoprimeCorrection
  rw [Complex.ofReal_sum, Complex.ofReal_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  by_cases hcop : n.Coprime q
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hcop)]
    rw [if_pos hcop]
    simp
  · rw [(1 : DirichletCharacter ℂ q).map_nonunit
      ((ZMod.isUnit_iff_coprime n q).not.mpr hcop)]
    rw [if_neg hcop]
    simp

/-- The ordinary PNT-error part of the principal character contribution. -/
noncomputable def liuPanAggregatePrincipalPNTTerm
    (t A q : ℕ) (f : ℕ → ℝ) : ℂ :=
  liuPanSourceCharacterPrefix A q f (1 : DirichletCharacter ℂ q) *
    ((liuPanPsiPrefix t : ℂ) - (t : ℂ)) / (Nat.totient q : ℂ)

/-- The real source aggregate paired with the ordinary PNT remainder. -/
noncomputable def liuPanAggregatePNTError
    (t A q : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ a ∈ Icc 1 A, if a.Coprime q then f a else 0) * liuPanPNTError t

/-- The complex principal PNT term is the complexification of its real source
aggregate, followed by the totient normalization. -/
theorem liuPanAggregatePrincipalPNTTerm_eq_real
    (t A q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePrincipalPNTTerm t A q f =
      (liuPanAggregatePNTError t A q f : ℂ) / (Nat.totient q : ℂ) := by
  unfold liuPanAggregatePrincipalPNTTerm liuPanAggregatePNTError
    liuPanPNTError
  rw [liuPanSourceCharacterPrefix_one_eq_coprime]
  have hsource :
      (∑ a ∈ Icc 1 A, if a.Coprime q then (f a : ℂ) else 0) =
        (∑ a ∈ Icc 1 A, if a.Coprime q then f a else 0 : ℝ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro a ha
    split_ifs <;> rfl
  rw [hsource]
  push_cast
  ring

/-- The correction to the principal term from prime powers whose prime divides
the modulus. -/
noncomputable def liuPanAggregatePrincipalNoncoprimePsiTerm
    (t A q : ℕ) (f : ℕ → ℝ) : ℂ :=
  liuPanSourceCharacterPrefix A q f (1 : DirichletCharacter ℂ q) *
    (liuPanPsiNoncoprimeCorrection t q : ℂ) / (Nat.totient q : ℂ)

/-- The real source aggregate paired with the noncoprime psi correction. -/
noncomputable def liuPanAggregateNoncoprimePsiCorrection
    (t A q : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ a ∈ Icc 1 A, if a.Coprime q then f a else 0) *
    liuPanPsiNoncoprimeCorrection t q

/-- The complex principal correction is just the complexification of its real
source aggregate, followed by the totient normalization. -/
theorem liuPanAggregatePrincipalNoncoprimePsiTerm_eq_real
    (t A q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePrincipalNoncoprimePsiTerm t A q f =
      (liuPanAggregateNoncoprimePsiCorrection t A q f : ℂ) /
        (Nat.totient q : ℂ) := by
  unfold liuPanAggregatePrincipalNoncoprimePsiTerm
    liuPanAggregateNoncoprimePsiCorrection
  rw [liuPanSourceCharacterPrefix_one_eq_coprime]
  have hsource :
      (∑ a ∈ Icc 1 A, if a.Coprime q then (f a : ℂ) else 0) =
        (∑ a ∈ Icc 1 A, if a.Coprime q then f a else 0 : ℝ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro a ha
    split_ifs <;> rfl
  rw [hsource, ← Complex.ofReal_mul]

/-- The zero modulus is canonically killed by the totient normalization. -/
@[simp] theorem liuPanAggregatePrincipalNoncoprimePsiTerm_zero
    (t A : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePrincipalNoncoprimePsiTerm t A 0 f = 0 := by
  simp [liuPanAggregatePrincipalNoncoprimePsiTerm]

/-- The source-aggregated endpoint shell for a scalar noncoprime correction. -/
theorem liuPanAggregateNoncoprimePsiCorrection_endpoint_shell
    (y X q : ℕ) (f g : ℕ → ℝ) (hg0 : g 0 = 0) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * g (y / a) * liuPanPsiNoncoprimeCorrection (y / a) q
    else 0) =
      ∑ k ∈ Icc 1 y, g k *
        (liuPanAggregateNoncoprimePsiCorrection k
            (liuPanAbelSourceCutoff y X k) q f -
          liuPanAggregateNoncoprimePsiCorrection k
            (liuPanAbelSourceCutoff y X (k + 1)) q f) := by
  have hsum (k A : ℕ) :
      (∑ a ∈ Icc 1 A, if a.Coprime q then
        f a * liuPanPsiNoncoprimeCorrection k q
      else 0) = liuPanAggregateNoncoprimePsiCorrection k A q f := by
    unfold liuPanAggregateNoncoprimePsiCorrection
    rw [sum_mul]
    apply sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q <;> simp [hcop]
  calc
    _ = ∑ k ∈ Icc 1 y, g k *
        ((∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X k),
          if a.Coprime q then f a * liuPanPsiNoncoprimeCorrection k q else 0) -
        ∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (k + 1)),
          if a.Coprime q then f a * liuPanPsiNoncoprimeCorrection k q else 0) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm, mul_ite, mul_zero] using
        (sum_source_eq_sum_quotient_shells y X g
          (fun k a => if a.Coprime q then
            f a * liuPanPsiNoncoprimeCorrection k q
          else 0) hg0)
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [hsum, hsum]

/-- Swapping the source sum with scalar noncoprime correction prefixes retains
the shared Abel source cutoff. -/
theorem liuPanAggregateNoncoprimePsiCorrection_prefix_swap
    (y X q : ℕ) (f w : ℕ → ℝ) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * (∑ n ∈ range (y / a), w n *
        liuPanPsiNoncoprimeCorrection n q)
    else 0) =
      ∑ n ∈ range y, w n *
        liuPanAggregateNoncoprimePsiCorrection n
          (liuPanAbelSourceCutoff y X (n + 1)) q f := by
  calc
    _ = ∑ a ∈ Icc 1 X, ∑ n ∈ range (y / a), w n *
          (if a.Coprime q then
            f a * liuPanPsiNoncoprimeCorrection n q
          else 0) := by
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop, Finset.mul_sum]
        apply sum_congr rfl
        intro n hn
        ring
      · simp [hcop]
    _ = ∑ n ∈ range y, w n *
          ∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (n + 1)),
            (if a.Coprime q then
              f a * liuPanPsiNoncoprimeCorrection n q
            else 0) :=
      sum_source_prefix_eq_sum_aggregate_prefix y X w
        (fun n a => if a.Coprime q then
          f a * liuPanPsiNoncoprimeCorrection n q
        else 0)
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      unfold liuPanAggregateNoncoprimePsiCorrection
      rw [sum_mul]
      apply congrArg (fun z => w n * z)
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q <;> simp [hcop]

/-- Exact principal split into the ordinary PNT error and the modulus-
noncoprime correction. -/
theorem liuPanAggregatePrincipalPsiTerm_eq_pnt_sub_noncoprime
    (t A q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePrincipalPsiTerm t A q f =
      liuPanAggregatePrincipalPNTTerm t A q f -
        liuPanAggregatePrincipalNoncoprimePsiTerm t A q f := by
  unfold liuPanAggregatePrincipalPsiTerm
  rw [liuPanLambdaCharacterPrefix_one_eq_psi_sub_noncoprime]
  unfold liuPanAggregatePrincipalPNTTerm
    liuPanAggregatePrincipalNoncoprimePsiTerm
  ring

/-- At modulus one there are no nonprincipal characters. -/
@[simp] theorem liuPanPrimePowerNonprincipalCharacters_one :
    liuPanPrimePowerNonprincipalCharacters 1 = ∅ := by
  classical
  ext χ
  simp [liuPanPrimePowerNonprincipalCharacters, Subsingleton.elim χ 1]

/-- Modulus one consists only of the principal psi contribution. -/
@[simp] theorem liuPanAggregateNonprincipalPsiTerm_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateNonprincipalPsiTerm t A 1 l f = 0 := by
  simp [liuPanAggregateNonprincipalPsiTerm]

/-- At modulus one the canonical expansion is principal only. -/
@[simp] theorem liuPanAggregatePsiCharacterExpansion_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiCharacterExpansion t A 1 l f =
      liuPanAggregatePrincipalPsiTerm t A 1 f := by
  simp [liuPanAggregatePsiCharacterExpansion]

/-- The actual aggregate discrepancy at modulus one is principal only. -/
theorem liuPanAggregateAPPsiDiscrepancy_complex_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    (liuPanAggregateAPPsiDiscrepancy t A 1 l f : ℂ) =
      liuPanAggregatePrincipalPsiTerm t A 1 f := by
  have hl : IsUnit (l : ZMod 1) := by
    simpa only [Subsingleton.elim (l : ZMod 1) 1] using
      (isUnit_one : IsUnit (1 : ZMod 1))
  calc
    (liuPanAggregateAPPsiDiscrepancy t A 1 l f : ℂ) =
        liuPanAggregatePsiCharacterExpansion t A 1 l f :=
      liuPanAggregateAPPsiDiscrepancy_complex_eq_characterExpansion f
        (by omega) hl
    _ = liuPanAggregatePrincipalPsiTerm t A 1 f :=
      liuPanAggregatePsiCharacterExpansion_one t A l f

/-! ## Primitive dilation on the source and von Mangoldt sides -/

/-- The source sequence extended by zero at the excluded index `0`. -/
noncomputable def liuPanSourceZeroExtension (f : ℕ → ℝ) (a : ℕ) : ℂ :=
  if a = 0 then 0 else (f a : ℂ)

/-- The source prefix as a zero-extended range sum, in the form consumed by the
generic induced-character dilation identity. -/
theorem liuPanSourceCharacterPrefix_eq_zeroExtension
    (A q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) :
    liuPanSourceCharacterPrefix A q f χ =
      ∑ a ∈ range (A + 1),
        liuPanSourceZeroExtension f a * χ (a : ZMod q) := by
  have hrange : range (A + 1) = insert 0 (Icc 1 A) := by
    ext a
    simp
    omega
  rw [hrange, sum_insert (by simp)]
  simp only [liuPanSourceCharacterPrefix, liuPanSourceZeroExtension,
    if_pos, zero_mul, zero_add]
  apply sum_congr rfl
  intro a ha
  rw [if_neg (by
    have := (mem_Icc.mp ha).1
    omega)]

/-- Exact conductor-first primitive/Möbius-dilation transfer of the source
prefix for one induced character. -/
theorem liuPanSourceCharacterPrefix_eq_primitive_dilations
    {q : ℕ} [NeZero q] (A : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) :
    liuPanSourceCharacterPrefix A q f χ =
      ∑ e ∈ (q / χ.conductor).divisors,
        ((ArithmeticFunction.moebius e : ℂ) *
          χ.primitiveCharacter (e : ZMod χ.conductor)) *
          ∑ m ∈ range (A / e + 1),
            liuPanSourceZeroExtension f (e * m) *
              χ.primitiveCharacter (m : ZMod χ.conductor) := by
  rw [liuPanSourceCharacterPrefix_eq_zeroExtension]
  exact characterPrefixSum_eq_sum_primitive_dilations
    (liuPanSourceZeroExtension f) χ A

/-- Exact conductor-first primitive/Möbius-dilation transfer of the von
Mangoldt prefix for one induced character. -/
theorem liuPanLambdaCharacterPrefix_eq_primitive_dilations
    {q : ℕ} [NeZero q] (t : ℕ) (χ : DirichletCharacter ℂ q) :
    liuPanLambdaCharacterPrefix t q χ =
      ∑ e ∈ (q / χ.conductor).divisors,
        ((ArithmeticFunction.moebius e : ℂ) *
          χ.primitiveCharacter (e : ZMod χ.conductor)) *
          ∑ m ∈ range (t / e + 1),
            (Λ (e * m) : ℂ) *
              χ.primitiveCharacter (m : ZMod χ.conductor) := by
  unfold liuPanLambdaCharacterPrefix
  exact characterPrefixSum_eq_sum_primitive_dilations
    (fun n => (Λ n : ℂ)) χ t

/-- Both factors of the aggregate character product transfer to primitive
dilations before any absolute value or character Cauchy--Schwarz step. -/
theorem liuPanSource_mul_lambda_eq_primitive_dilations
    {q : ℕ} [NeZero q] (t A : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) :
    liuPanSourceCharacterPrefix A q f χ *
        liuPanLambdaCharacterPrefix t q χ =
      (∑ e ∈ (q / χ.conductor).divisors,
          ((ArithmeticFunction.moebius e : ℂ) *
            χ.primitiveCharacter (e : ZMod χ.conductor)) *
            ∑ m ∈ range (A / e + 1),
              liuPanSourceZeroExtension f (e * m) *
                χ.primitiveCharacter (m : ZMod χ.conductor)) *
        (∑ e ∈ (q / χ.conductor).divisors,
          ((ArithmeticFunction.moebius e : ℂ) *
            χ.primitiveCharacter (e : ZMod χ.conductor)) *
            ∑ m ∈ range (t / e + 1),
              (Λ (e * m) : ℂ) *
                χ.primitiveCharacter (m : ZMod χ.conductor)) := by
  rw [liuPanSourceCharacterPrefix_eq_primitive_dilations,
    liuPanLambdaCharacterPrefix_eq_primitive_dilations]

/-! ## Exact conductor-first regrouping -/

/-- The nonprincipal character product at one level. -/
noncomputable def liuPanAggregatePsiCharacterProduct
    (t A q l : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
    liuPanLambdaCharacterPrefix t q χ

/-- The nonprincipal sum regrouped by exact conductor.  Conductor one is absent
from the indexing interval. -/
noncomputable def liuPanAggregatePsiConductorSum
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ d ∈ Icc 2 q,
      ∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
          (fun χ => χ.conductor = d),
        liuPanAggregatePsiCharacterProduct t A q l f χ

@[simp] theorem liuPanAggregatePsiConductorSum_zero
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiConductorSum t A 0 l f = 0 := by
  simp [liuPanAggregatePsiConductorSum]

@[simp] theorem liuPanAggregatePsiConductorSum_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiConductorSum t A 1 l f = 0 := by
  simp [liuPanAggregatePsiConductorSum]

/-- Exact regrouping of the nonprincipal aggregate by conductor, before any
absolute value or Cauchy--Schwarz inequality. -/
theorem liuPanAggregateNonprincipalPsiTerm_eq_conductorSum
    {t A q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateNonprincipalPsiTerm t A q l f =
      liuPanAggregatePsiConductorSum t A q l f := by
  classical
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold liuPanAggregateNonprincipalPsiTerm
    liuPanAggregatePsiConductorSum liuPanAggregatePsiCharacterProduct
  congr 1
  calc
    (∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
        star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
          liuPanLambdaCharacterPrefix t q χ) =
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          ∑ d ∈ Icc 2 q, if χ.conductor = d then
            star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
              liuPanLambdaCharacterPrefix t q χ else 0 := by
      apply sum_congr rfl
      intro χ hχ
      have hχne : χ ≠ 1 := by
        simpa [liuPanPrimePowerNonprincipalCharacters] using hχ
      have hdne : χ.conductor ≠ 1 := fun hd =>
        hχne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
      have hdpos : 0 < χ.conductor :=
        Nat.pos_of_ne_zero χ.conductor_ne_zero
      have hdle : χ.conductor ≤ q :=
        Nat.le_of_dvd hq χ.conductor_dvd_level
      have hdmem : χ.conductor ∈ Icc 2 q := by
        rw [mem_Icc]
        omega
      simp [hdmem]
    _ = ∑ d ∈ Icc 2 q,
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          if χ.conductor = d then
            star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
              liuPanLambdaCharacterPrefix t q χ else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [sum_filter]

/-- The conductor sum reindexed by the unique primitive character inducing each
nonprincipal character. -/
noncomputable def liuPanAggregatePsiPrimitiveLiftSum
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ d ∈ Icc 2 q, if hdq : d ∣ q then
      ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
        liuPanAggregatePsiCharacterProduct t A q l f
          (DirichletCharacter.changeLevel hdq ψ)
    else 0

@[simp] theorem liuPanAggregatePsiPrimitiveLiftSum_zero
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiPrimitiveLiftSum t A 0 l f = 0 := by
  simp [liuPanAggregatePsiPrimitiveLiftSum]

@[simp] theorem liuPanAggregatePsiPrimitiveLiftSum_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiPrimitiveLiftSum t A 1 l f = 0 := by
  simp [liuPanAggregatePsiPrimitiveLiftSum]

/-- Exact primitive-character reindexing of the conductor-first aggregate. -/
theorem liuPanAggregatePsiConductorSum_eq_primitiveLiftSum
    {t A q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregatePsiConductorSum t A q l f =
      liuPanAggregatePsiPrimitiveLiftSum t A q l f := by
  classical
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold liuPanAggregatePsiConductorSum
    liuPanAggregatePsiPrimitiveLiftSum
  congr 1
  apply sum_congr rfl
  intro d hdmem
  have hd : 1 < d := (mem_Icc.mp hdmem).1
  by_cases hdq : d ∣ q
  · rw [dif_pos hdq,
      liuPanPrimePowerNonprincipalCharacters_filter_conductor_eq_lifts
        q d hdq hd]
    unfold liuPanPrimePowerPrimitiveCharacterLifts
    rw [sum_image]
    exact Set.injOn_of_injective
      (DirichletCharacter.changeLevel_injective hdq)
  · rw [dif_neg hdq]
    have hempty :
        (liuPanPrimePowerNonprincipalCharacters q).filter
            (fun χ => χ.conductor = d) = ∅ := by
      rw [filter_eq_empty_iff]
      intro χ hχ hcond
      exact hdq (hcond ▸ χ.conductor_dvd_level)
    rw [hempty]
    simp

/-! ## Substitution into the aggregate Abel term -/

/-- The exact character expansion substituted into both shared-`y` Abel sums. -/
noncomputable def liuPanAggregateInverseLogPsiCharacterTerm
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregatePsiCharacterExpansion k
        (liuPanAbelSourceCutoff y X k) q l f -
      liuPanAggregatePsiCharacterExpansion k
        (liuPanAbelSourceCutoff y X (k + 1)) q l f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregatePsiCharacterExpansion n
      (liuPanAbelSourceCutoff y X (n + 1)) q l f

@[simp] theorem liuPanAggregateInverseLogPsiCharacterTerm_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPsiCharacterTerm y X 0 l f = 0 := by
  simp [liuPanAggregateInverseLogPsiCharacterTerm]

/-- Exact substitution into `liuPanAggregateInverseLogPsiTerm`; all source
cutoffs, shell differences, and common `y` parameters are unchanged. -/
theorem liuPanAggregateInverseLogPsiTerm_complex_eq_characterTerm
    {y X q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q)
    (hl : IsUnit (l : ZMod q)) :
    (liuPanAggregateInverseLogPsiTerm y X q l f : ℂ) =
      liuPanAggregateInverseLogPsiCharacterTerm y X q l f := by
  unfold liuPanAggregateInverseLogPsiTerm
    liuPanAggregateInverseLogPsiCharacterTerm
  push_cast
  simp_rw [liuPanAggregateAPPsiDiscrepancy_complex_eq_characterExpansion
    f hq hl]

/-- The principal contribution after substitution into the shared-`y` Abel
shell and prefix sums. -/
noncomputable def liuPanAggregateInverseLogPrincipalPsiTerm
    (y X q : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregatePrincipalPsiTerm k
        (liuPanAbelSourceCutoff y X k) q f -
      liuPanAggregatePrincipalPsiTerm k
        (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregatePrincipalPsiTerm n
      (liuPanAbelSourceCutoff y X (n + 1)) q f

/-- The ordinary PNT-error part of the principal shared-`y` Abel term. -/
noncomputable def liuPanAggregateInverseLogPrincipalPNTTerm
    (y X q : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregatePrincipalPNTTerm k
        (liuPanAbelSourceCutoff y X k) q f -
      liuPanAggregatePrincipalPNTTerm k
        (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregatePrincipalPNTTerm n
      (liuPanAbelSourceCutoff y X (n + 1)) q f

/-- The real shared-`y` Abel aggregation of the ordinary PNT remainder. -/
noncomputable def liuPanAggregateInverseLogPNTError
    (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ))⁻¹ *
    (liuPanAggregatePNTError k
        (liuPanAbelSourceCutoff y X k) q f -
      liuPanAggregatePNTError k
        (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
  ∑ n ∈ range y, liuPanInverseLogAbelWeight n *
    liuPanAggregatePNTError n
      (liuPanAbelSourceCutoff y X (n + 1)) q f

/-- The source-aggregated endpoint shell for the scalar ordinary PNT
remainder. -/
theorem liuPanAggregatePNTError_endpoint_shell
    (y X q : ℕ) (f g : ℕ → ℝ) (hg0 : g 0 = 0) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * g (y / a) * liuPanPNTError (y / a)
    else 0) =
      ∑ k ∈ Icc 1 y, g k *
        (liuPanAggregatePNTError k
            (liuPanAbelSourceCutoff y X k) q f -
          liuPanAggregatePNTError k
            (liuPanAbelSourceCutoff y X (k + 1)) q f) := by
  have hsum (k A : ℕ) :
      (∑ a ∈ Icc 1 A, if a.Coprime q then
        f a * liuPanPNTError k
      else 0) = liuPanAggregatePNTError k A q f := by
    unfold liuPanAggregatePNTError
    rw [sum_mul]
    apply sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q <;> simp [hcop]
  calc
    _ = ∑ k ∈ Icc 1 y, g k *
        ((∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X k),
          if a.Coprime q then f a * liuPanPNTError k else 0) -
        ∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (k + 1)),
          if a.Coprime q then f a * liuPanPNTError k else 0) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm, mul_ite, mul_zero] using
        (sum_source_eq_sum_quotient_shells y X g
          (fun k a => if a.Coprime q then f a * liuPanPNTError k else 0) hg0)
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [hsum, hsum]

/-- Swapping source summation with ordinary PNT prefixes retains the shared
Abel source cutoff. -/
theorem liuPanAggregatePNTError_prefix_swap
    (y X q : ℕ) (f w : ℕ → ℝ) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * (∑ n ∈ range (y / a), w n * liuPanPNTError n)
    else 0) =
      ∑ n ∈ range y, w n *
        liuPanAggregatePNTError n
          (liuPanAbelSourceCutoff y X (n + 1)) q f := by
  calc
    _ = ∑ a ∈ Icc 1 X, ∑ n ∈ range (y / a), w n *
          (if a.Coprime q then f a * liuPanPNTError n else 0) := by
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop, Finset.mul_sum]
        apply sum_congr rfl
        intro n hn
        ring
      · simp [hcop]
    _ = ∑ n ∈ range y, w n *
        ∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (n + 1)),
          (if a.Coprime q then f a * liuPanPNTError n else 0) :=
      sum_source_prefix_eq_sum_aggregate_prefix y X w
        (fun n a => if a.Coprime q then f a * liuPanPNTError n else 0)
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      unfold liuPanAggregatePNTError
      rw [sum_mul]
      apply congrArg (fun z => w n * z)
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q <;> simp [hcop]

/-- The ordinary PNT Abel aggregate is exactly the source convolution with the
totalized inverse-log PNT remainder. -/
theorem liuPanAggregateInverseLogPNTError_eq_source
    (y X q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPNTError y X q f =
      ∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * liuPanLogPNTError (y / a)
      else 0 := by
  symm
  unfold liuPanLogPNTError
  calc
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * ((Real.log (y / a : ℕ))⁻¹ * liuPanPNTError (y / a) +
        ∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
          liuPanPNTError n)
    else 0) =
      (∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * (Real.log (y / a : ℕ))⁻¹ * liuPanPNTError (y / a)
      else 0) +
      ∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * (∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
          liuPanPNTError n)
      else 0 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro a ha
        by_cases hcop : a.Coprime q
        · simp only [if_pos hcop]
          ring
        · simp [hcop]
    _ = liuPanAggregateInverseLogPNTError y X q f := by
      rw [liuPanAggregatePNTError_endpoint_shell y X q f
        (fun k => (Real.log (k : ℝ))⁻¹) (by simp),
        liuPanAggregatePNTError_prefix_swap y X q f
          liuPanInverseLogAbelWeight]
      rfl

/-- Complexification and the totient factor commute with the complete
ordinary-PNT shared-`y` Abel aggregation. -/
theorem liuPanAggregateInverseLogPrincipalPNTTerm_eq_real
    (y X q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPrincipalPNTTerm y X q f =
      (liuPanAggregateInverseLogPNTError y X q f : ℂ) /
        (Nat.totient q : ℂ) := by
  unfold liuPanAggregateInverseLogPrincipalPNTTerm
    liuPanAggregateInverseLogPNTError
  simp_rw [liuPanAggregatePrincipalPNTTerm_eq_real]
  push_cast
  ring_nf
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply sum_congr rfl
    intro n hn
    ring
  · apply sum_congr rfl
    intro n hn
    ring

/-- Exact real source form of the ordinary principal/PNT term.  In particular,
the same `y / a` quotient remains inside the totalized Abel remainder. -/
theorem liuPanAggregateInverseLogPrincipalPNTTerm_eq_source
    (y X q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPrincipalPNTTerm y X q f =
      ((∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * liuPanLogPNTError (y / a)
      else 0 : ℝ) : ℂ) / (Nat.totient q : ℂ) := by
  rw [liuPanAggregateInverseLogPrincipalPNTTerm_eq_real,
    liuPanAggregateInverseLogPNTError_eq_source]

/-- The exact Liu source is an indicator, so replacing it by one is permitted
only through this explicit pointwise upper bound. -/
theorem liuWeight_le_one (N z y a : ℕ) : liuWeight N z y a ≤ 1 := by
  unfold liuWeight
  split <;> simp

/-- The reciprocal mass of the actual Liu source is bounded by the harmonic
sum; this is the source factor used for the long-quotient PNT range. -/
theorem sum_liuWeight_div_le_liuHarmonic (N : ℕ) :
    ∑ a ∈ Icc 1 N,
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a ≤
        liuHarmonic N := by
  rw [liuHarmonic]
  apply sum_le_sum
  intro a ha
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (mem_Icc.mp ha).1
  rw [div_eq_mul_inv]
  simpa using mul_le_mul_of_nonneg_right
    (liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a)
    (inv_nonneg.mpr ha0.le)

/-- The reciprocal Liu-source mass costs at most one logarithm. -/
theorem sum_liuWeight_div_le_one_add_log (N : ℕ) :
    ∑ a ∈ Icc 1 N,
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a ≤
        1 + Real.log N :=
  (sum_liuWeight_div_le_liuHarmonic N).trans (liuHarmonic_le_one_add_log N)

/-- The global linear Abel bound, summed against the reciprocal Liu source.
This is the short-`y` input in the principal source-family estimate. -/
theorem abs_liuPanPrincipalPNTSourceSum_le_global
    (N y q : ℕ) :
    |∑ a ∈ Icc 1 N, if a.Coprime q then
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          liuPanLogPNTError (y / a)
      else 0| ≤
      (2 * (Real.log 4 + 5) * (Real.log 2)⁻¹) * y *
        (1 + Real.log N) := by
  let K : ℝ := 2 * (Real.log 4 + 5) * (Real.log 2)⁻¹
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  calc
    |∑ a ∈ Icc 1 N, if a.Coprime q then
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          liuPanLogPNTError (y / a)
      else 0| ≤
        ∑ a ∈ Icc 1 N, |if a.Coprime q then
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
            liuPanLogPNTError (y / a)
        else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 N,
        (K * y) *
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a) := by
      apply sum_le_sum
      intro a ha
      have ha0 : 0 < (a : ℝ) := by exact_mod_cast (mem_Icc.mp ha).1
      by_cases hcop : a.Coprime q
      · rw [if_pos hcop, abs_mul,
          abs_of_nonneg (liuWeight_nonneg _ _ _ _)]
        calc
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              |liuPanLogPNTError (y / a)| ≤
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              (K * (y / a : ℕ)) :=
            mul_le_mul_of_nonneg_left
              (abs_liuPanLogPNTError_le_global_linear (y / a))
              (liuWeight_nonneg _ _ _ _)
          _ ≤ liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              (K * ((y : ℝ) / a)) := by
            apply mul_le_mul_of_nonneg_left _ (liuWeight_nonneg _ _ _ _)
            exact mul_le_mul_of_nonneg_left
              (Nat.cast_div_le (α := ℝ)) hK
          _ = (K * y) *
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a) := by
            field_simp
      · rw [if_neg hcop, abs_zero]
        exact mul_nonneg (mul_nonneg hK (Nat.cast_nonneg y))
          (div_nonneg (liuWeight_nonneg _ _ _ _) ha0.le)
    _ = (K * y) * ∑ a ∈ Icc 1 N,
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a := by
      rw [mul_sum]
    _ ≤ (K * y) * (1 + Real.log N) :=
      mul_le_mul_of_nonneg_left (sum_liuWeight_div_le_one_add_log N)
        (by positivity)
    _ = _ := by rfl

/-- Once `y` reaches the five-sixths scale, every nonzero Liu source produces
a quotient at least at the one-ninth scale.  The weaker exponent absorbs the
integer division uniformly. -/
theorem eventually_liuWeight_quotient_ge_rpow_one_ninth :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ y : ℕ, (N : ℝ) ^ (5 / 6 : ℝ) ≤ y →
      ∀ a ∈ Icc 1 N,
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a ≠ 0 →
          (N : ℝ) ^ (1 / 9 : ℝ) ≤ (y / a : ℕ) := by
  have hreal : ∀ᶠ x : ℝ in atTop, 2 < x ^ (1 / 18 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 18)).eventually
      (eventually_gt_atTop 2)
  have hnat : ∀ᶠ N : ℕ in atTop, 2 < (N : ℝ) ^ (1 / 18 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  rcases eventually_atTop.mp hnat with ⟨N0, hN0⟩
  refine ⟨max N0 1, ?_⟩
  intro N hN y hy a ha hwa
  have hN0' : N0 ≤ N := (le_max_left N0 1).trans hN
  have hN1 : 1 ≤ N := (le_max_right N0 1).trans hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hpow1 : 1 ≤ (N : ℝ) ^ (1 / 9 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
  have hgap :
      2 * (N : ℝ) ^ (7 / 9 : ℝ) <
        (N : ℝ) ^ (5 / 6 : ℝ) := by
    rw [show (5 / 6 : ℝ) = 7 / 9 + 1 / 18 by norm_num,
      Real.rpow_add hNpos]
    have hpowpos : 0 < (N : ℝ) ^ (7 / 9 : ℝ) :=
      Real.rpow_pos_of_pos hNpos _
    nlinarith [hN0 N hN0']
  have hs :
      LiuWeightSupport N (liuSourceZ10 N) (liuSourceY3 N) a := by
    by_contra h
    exact hwa (liuWeight_eq_zero_iff.mpr h)
  have haUpper : (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
    liuWeightSupport_le_rpow_two_thirds hs
  have haPos : 0 < a := (mem_Icc.mp ha).1
  by_contra hquot
  have hquot' : ((y / a : ℕ) : ℝ) < (N : ℝ) ^ (1 / 9 : ℝ) :=
    lt_of_not_ge hquot
  have hsucc :
      ((y / a : ℕ) : ℝ) + 1 <
        2 * (N : ℝ) ^ (1 / 9 : ℝ) := by
    nlinarith
  have hylt : y < a * (y / a + 1) := Nat.lt_mul_div_succ y haPos
  have hyltR :
      (y : ℝ) <
        (N : ℝ) ^ (2 / 3 : ℝ) *
          (2 * (N : ℝ) ^ (1 / 9 : ℝ)) := by
    calc
      (y : ℝ) < (a : ℝ) * (((y / a : ℕ) : ℝ) + 1) := by
        exact_mod_cast hylt
      _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) *
          (((y / a : ℕ) : ℝ) + 1) := by
        gcongr
      _ < (N : ℝ) ^ (2 / 3 : ℝ) *
          (2 * (N : ℝ) ^ (1 / 9 : ℝ)) := by
        gcongr
  have hpows :
      (N : ℝ) ^ (2 / 3 : ℝ) *
          (2 * (N : ℝ) ^ (1 / 9 : ℝ)) =
        2 * (N : ℝ) ^ (7 / 9 : ℝ) := by
    rw [show (7 / 9 : ℝ) = 2 / 3 + 1 / 9 by norm_num,
      Real.rpow_add hNpos]
    ring
  rw [hpows] at hyltR
  exact (not_lt_of_ge hy) (hyltR.trans hgap)

/-- On the large-`y` range, a scalar logarithmic PNT bound may be applied
uniformly to every nonzero Liu source quotient. -/
theorem abs_liuPanPrincipalPNTSourceSum_le_large
    (D C : ℝ) (hD : 0 < D) (hC : 0 ≤ C) (T0 : ℕ)
    (hscalar : ∀ t : ℕ, T0 ≤ t →
      |liuPanLogPNTError t| ≤ C * t / Real.log t ^ D)
    {N y q : ℕ} (hN : 3 ≤ N)
    (hT0 : (T0 : ℝ) ≤ (N : ℝ) ^ (1 / 9 : ℝ))
    (hquot : ∀ a ∈ Icc 1 N,
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a ≠ 0 →
        (N : ℝ) ^ (1 / 9 : ℝ) ≤ (y / a : ℕ)) :
    |∑ a ∈ Icc 1 N, if a.Coprime q then
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          liuPanLogPNTError (y / a)
      else 0| ≤
      (C * (9 : ℝ) ^ D * y / Real.log N ^ D) *
        (1 + Real.log N) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbase : 0 < Real.log (N : ℝ) / 9 := by positivity
  have hpow9 : 0 < (9 : ℝ) ^ D := Real.rpow_pos_of_pos (by norm_num) _
  have hdenom : 0 < Real.log (N : ℝ) ^ D :=
    Real.rpow_pos_of_pos hlogN _
  calc
    |∑ a ∈ Icc 1 N, if a.Coprime q then
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          liuPanLogPNTError (y / a)
      else 0| ≤
        ∑ a ∈ Icc 1 N, |if a.Coprime q then
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
            liuPanLogPNTError (y / a)
        else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 N,
        (C * (9 : ℝ) ^ D * y / Real.log N ^ D) *
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a) := by
      apply sum_le_sum
      intro a ha
      have haR : 0 < (a : ℝ) := by exact_mod_cast (mem_Icc.mp ha).1
      by_cases hcop : a.Coprime q
      · rw [if_pos hcop, abs_mul,
          abs_of_nonneg (liuWeight_nonneg _ _ _ _)]
        by_cases hwa :
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a = 0
        · simp [hwa]
        · have hquot' := hquot a ha hwa
          have htpos : 0 < (y / a : ℕ) := by
            have hpow1 : 1 ≤ (N : ℝ) ^ (1 / 9 : ℝ) :=
              Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega))
                (by norm_num)
            exact_mod_cast hpow1.trans hquot'
          have hT0' : T0 ≤ y / a := by
            exact_mod_cast hT0.trans hquot'
          have hlogt : 0 < Real.log (y / a : ℕ) :=
            Real.log_pos (by
              exact_mod_cast (show 1 < y / a by
                have hNpow :
                    1 < (N : ℝ) ^ (1 / 9 : ℝ) :=
                  Real.one_lt_rpow
                    (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
                exact_mod_cast hNpow.trans_le hquot'))
          have hlogCompare :
              Real.log (N : ℝ) / 9 ≤ Real.log (y / a : ℕ) := by
            calc
              Real.log (N : ℝ) / 9 =
                  Real.log ((N : ℝ) ^ (1 / 9 : ℝ)) := by
                rw [Real.log_rpow hNpos]
                ring
              _ ≤ Real.log (y / a : ℕ) :=
                Real.strictMonoOn_log.monotoneOn
                  (Real.rpow_pos_of_pos hNpos _)
                  (by
                    simpa only [Set.mem_Ioi] using
                      (show (0 : ℝ) < (y / a : ℕ) by exact_mod_cast htpos))
                  hquot'
          have hdenomCompare :
              (Real.log (N : ℝ) / 9) ^ D ≤
                Real.log (y / a : ℕ) ^ D :=
            Real.rpow_le_rpow hbase.le hlogCompare hD.le
          have hnum :
              C * (y / a : ℕ) ≤ C * ((y : ℝ) / a) :=
            mul_le_mul_of_nonneg_left (Nat.cast_div_le (α := ℝ)) hC
          have hpoint :
              |liuPanLogPNTError (y / a)| ≤
                C * (9 : ℝ) ^ D * ((y : ℝ) / a) /
                  Real.log N ^ D := by
            calc
              |liuPanLogPNTError (y / a)| ≤
                  C * (y / a : ℕ) / Real.log (y / a : ℕ) ^ D :=
                hscalar (y / a) hT0'
              _ ≤ C * ((y : ℝ) / a) /
                  (Real.log (N : ℝ) / 9) ^ D :=
                div_le_div₀ (by positivity) hnum
                  (Real.rpow_pos_of_pos hbase _)
                  hdenomCompare
              _ = C * (9 : ℝ) ^ D * ((y : ℝ) / a) /
                  Real.log N ^ D := by
                rw [Real.div_rpow hlogN.le (by norm_num : (0 : ℝ) ≤ 9)]
                field_simp
          calc
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
                |liuPanLogPNTError (y / a)| ≤
              liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
                (C * (9 : ℝ) ^ D * ((y : ℝ) / a) /
                  Real.log N ^ D) :=
              mul_le_mul_of_nonneg_left hpoint
                (liuWeight_nonneg _ _ _ _)
            _ = (C * (9 : ℝ) ^ D * y / Real.log N ^ D) *
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a) := by
              field_simp
      · rw [if_neg hcop, abs_zero]
        exact mul_nonneg
          (div_nonneg
            (mul_nonneg (mul_nonneg hC hpow9.le) (Nat.cast_nonneg y))
            hdenom.le)
          (div_nonneg (liuWeight_nonneg _ _ _ _) haR.le)
    _ = (C * (9 : ℝ) ^ D * y / Real.log N ^ D) *
        ∑ a ∈ Icc 1 N,
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a := by
      rw [mul_sum]
    _ ≤ (C * (9 : ℝ) ^ D * y / Real.log N ^ D) *
        (1 + Real.log N) :=
      mul_le_mul_of_nonneg_left (sum_liuWeight_div_le_one_add_log N)
        (by positivity)

/-- The modulus-noncoprime correction in the same shared-`y` Abel shell and
prefix aggregation. -/
noncomputable def liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm
    (y X q : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregatePrincipalNoncoprimePsiTerm k
        (liuPanAbelSourceCutoff y X k) q f -
      liuPanAggregatePrincipalNoncoprimePsiTerm k
        (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregatePrincipalNoncoprimePsiTerm n
      (liuPanAbelSourceCutoff y X (n + 1)) q f

/-- The real shared-`y` Abel aggregation of the noncoprime correction. -/
noncomputable def liuPanAggregateInverseLogNoncoprimeCorrection
    (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ))⁻¹ *
    (liuPanAggregateNoncoprimePsiCorrection k
        (liuPanAbelSourceCutoff y X k) q f -
      liuPanAggregateNoncoprimePsiCorrection k
        (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
  ∑ n ∈ range y, liuPanInverseLogAbelWeight n *
    liuPanAggregateNoncoprimePsiCorrection n
      (liuPanAbelSourceCutoff y X (n + 1)) q f

/-- The aggregate correction is exactly the source sum of the logarithmically
normalized noncoprime prime-power correction; the same shared `y` and source
cutoffs are retained. -/
theorem liuPanAggregateInverseLogNoncoprimeCorrection_eq_source
    (y X q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNoncoprimeCorrection y X q f =
      ∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * liuPanLogNoncoprimeCorrection (y / a) q
      else 0 := by
  symm
  simp_rw [liuPanLogNoncoprimeCorrection_eq_discreteAbel]
  calc
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * ((Real.log (y / a : ℕ))⁻¹ *
        liuPanPsiNoncoprimeCorrection (y / a) q +
        ∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
          liuPanPsiNoncoprimeCorrection n q)
    else 0) =
      (∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * (Real.log (y / a : ℕ))⁻¹ *
          liuPanPsiNoncoprimeCorrection (y / a) q
      else 0) +
      ∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * (∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
          liuPanPsiNoncoprimeCorrection n q)
      else 0 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro a ha
        by_cases hcop : a.Coprime q
        · simp only [if_pos hcop]
          ring
        · simp [hcop]
    _ = (∑ k ∈ Icc 1 y, (Real.log (k : ℝ))⁻¹ *
        (liuPanAggregateNoncoprimePsiCorrection k
            (liuPanAbelSourceCutoff y X k) q f -
          liuPanAggregateNoncoprimePsiCorrection k
            (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
        ∑ n ∈ range y, liuPanInverseLogAbelWeight n *
          liuPanAggregateNoncoprimePsiCorrection n
            (liuPanAbelSourceCutoff y X (n + 1)) q f := by
      rw [liuPanAggregateNoncoprimePsiCorrection_endpoint_shell y X q f
        (fun k => (Real.log (k : ℝ))⁻¹) (by simp),
        liuPanAggregateNoncoprimePsiCorrection_prefix_swap y X q f
          liuPanInverseLogAbelWeight]
    _ = _ := rfl

/-- Complexification and the totient factor commute with the complete
shared-`y` noncoprime Abel aggregation. -/
theorem liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm_eq_real
    (y X q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm y X q f =
      (liuPanAggregateInverseLogNoncoprimeCorrection y X q f : ℂ) /
        (Nat.totient q : ℂ) := by
  unfold liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm
    liuPanAggregateInverseLogNoncoprimeCorrection
  simp_rw [liuPanAggregatePrincipalNoncoprimePsiTerm_eq_real]
  push_cast
  ring_nf
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply sum_congr rfl
    intro n hn
    ring
  · apply sum_congr rfl
    intro n hn
    ring

/-- The shared-`y` principal noncoprime term also vanishes canonically at
modulus zero. -/
@[simp] theorem liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm_zero
    (y X : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm y X 0 f = 0 := by
  simp [liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm]

/-- At modulus one the source form is exactly zero, not merely bounded. -/
@[simp] theorem liuPanAggregateInverseLogNoncoprimeCorrection_one
    (y X : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNoncoprimeCorrection y X 1 f = 0 := by
  rw [liuPanAggregateInverseLogNoncoprimeCorrection_eq_source]
  apply sum_eq_zero
  intro a ha
  simp

/-- Product-cube source support gives the exact `N^(2/3)` factor in the
noncoprime correction.  The remaining factor is only the finite count of
prime powers at primes dividing the modulus. -/
theorem liuPanAggregateInverseLogNoncoprimeCorrection_source_le
    (N y q : ℕ) (hy : y ≤ N) (hN : 1 ≤ N) :
    liuPanAggregateInverseLogNoncoprimeCorrection y N q
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      3 * (N : ℝ) ^ (2 / 3 : ℝ) *
        liuPanNoncoprimePrimePowerCountMax N q := by
  let f := liuWeight N (liuSourceZ10 N) (liuSourceY3 N)
  let M := liuPanNoncoprimePrimePowerCountMax N q
  have hM : 0 ≤ M := by
    have hmax := liuPanNoncoprimePrimePowerCount_le_max
      (N := N) (t := 0) (q := q) (Nat.zero_le N)
    exact (Nat.cast_nonneg _).trans hmax
  calc
    liuPanAggregateInverseLogNoncoprimeCorrection y N q f =
        ∑ a ∈ Icc 1 N, if a.Coprime q then
          f a * liuPanLogNoncoprimeCorrection (y / a) q
        else 0 :=
      liuPanAggregateInverseLogNoncoprimeCorrection_eq_source y N q f
    _ ≤ ∑ a ∈ Icc 1 N, f a * M := by
      apply sum_le_sum
      intro a ha
      by_cases hcop : a.Coprime q
      · rw [if_pos hcop]
        apply mul_le_mul_of_nonneg_left _ (liuWeight_nonneg _ _ _ _)
        exact liuPanLogNoncoprimeCorrection_le_primePowerCountMax
          ((Nat.div_le_self y a).trans hy)
      · rw [if_neg hcop]
        exact mul_nonneg (liuWeight_nonneg _ _ _ _) hM
    _ = M * ∑ a ∈ Icc 1 N, f a := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      ring
    _ ≤ M * (3 * (N : ℝ) ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_liuWeight_Icc_le_three_mul_rpow_two_thirds N
          (liuSourceZ10 N) (liuSourceY3 N) hN) hM
    _ = _ := by ring

/-- Canonical maximum of the real noncoprime correction over the shared
parameter `y ≤ N`. -/
noncomputable def liuPanAggregateInverseLogNoncoprimeCorrectionMaxY
    (N q : ℕ) : ℝ :=
  ((range (N + 1)).image fun y =>
    liuPanAggregateInverseLogNoncoprimeCorrection y N q
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The source-support bound is uniform through the canonical `y` maximum. -/
theorem liuPanAggregateInverseLogNoncoprimeCorrectionMaxY_source_le
    (N q : ℕ) (hN : 1 ≤ N) :
    liuPanAggregateInverseLogNoncoprimeCorrectionMaxY N q ≤
      3 * (N : ℝ) ^ (2 / 3 : ℝ) *
        liuPanNoncoprimePrimePowerCountMax N q := by
  unfold liuPanAggregateInverseLogNoncoprimeCorrectionMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  exact liuPanAggregateInverseLogNoncoprimeCorrection_source_le N y q
    (Nat.le_of_lt_succ (mem_range.mp hy)) hN

/-- A uniform finite prime-power count over moduli up to `Q`. -/
noncomputable def liuPanNoncoprimePrimePowerCountMaxModulus (N Q : ℕ) : ℝ :=
  ((range (Q + 1)).image fun q =>
    liuPanNoncoprimePrimePowerCountMax N q).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

theorem liuPanNoncoprimePrimePowerCountMax_le_maxModulus
    {N Q q : ℕ} (hq : q ≤ Q) :
    liuPanNoncoprimePrimePowerCountMax N q ≤
      liuPanNoncoprimePrimePowerCountMaxModulus N Q := by
  unfold liuPanNoncoprimePrimePowerCountMaxModulus
  apply le_max'
  exact mem_image.mpr ⟨q, mem_range.mpr (Nat.lt_succ_iff.mpr hq), rfl⟩

/-- The modulus-weighted noncoprime correction average; its weight is precisely
the squarefree weight used by `H₃`. -/
noncomputable def liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage
    (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q *
      (liuPanAggregateInverseLogNoncoprimeCorrectionMaxY N q /
        Nat.totient q)

/-- Lifting the source estimate through the squarefree modulus average costs
exactly `H₃`; no full-psi or square-root correction is introduced. -/
theorem liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage_source_le
    (N : ℕ) (B : ℝ) (hN : 1 ≤ N) :
    liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage N B ≤
      (3 * (N : ℝ) ^ (2 / 3 : ℝ) *
        liuPanNoncoprimePrimePowerCountMaxModulus N
          (panModulusCutoff N B)) *
        liuPanPrimePowerH3Mass (panModulusCutoff N B) := by
  let Q := panModulusCutoff N B
  let R : ℝ := 3 * (N : ℝ) ^ (2 / 3 : ℝ)
  let M := liuPanNoncoprimePrimePowerCountMaxModulus N Q
  have hM : 0 ≤ M := by
    have hmax := liuPanNoncoprimePrimePowerCountMax_le_maxModulus
      (N := N) (Q := Q) (q := 0) (Nat.zero_le Q)
    have hzero : 0 ≤ liuPanNoncoprimePrimePowerCountMax N 0 := by
      have hcount := liuPanNoncoprimePrimePowerCount_le_max
        (N := N) (t := 0) (q := 0) (Nat.zero_le N)
      exact (Nat.cast_nonneg _).trans hcount
    exact hzero.trans hmax
  unfold liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage
  change (∑ q ∈ range (Q + 1),
    liuPanPrimePowerModulusWeight q *
      (liuPanAggregateInverseLogNoncoprimeCorrectionMaxY N q /
        Nat.totient q)) ≤ _
  calc
    _ ≤ ∑ q ∈ range (Q + 1),
        liuPanPrimePowerModulusWeight q * (R * M / Nat.totient q) := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply div_le_div_of_nonneg_right
        · exact (liuPanAggregateInverseLogNoncoprimeCorrectionMaxY_source_le
            N q hN).trans
            (mul_le_mul_of_nonneg_left
              (liuPanNoncoprimePrimePowerCountMax_le_maxModulus
                (Nat.le_of_lt_succ (mem_range.mp hq)))
              (by positivity))
        · exact Nat.cast_nonneg _
      · exact liuPanPrimePowerModulusWeight_nonneg q
    _ = (R * M) * liuPanPrimePowerH3Mass Q := by
      unfold liuPanPrimePowerH3Mass
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      ring
    _ = _ := by rfl

/-- The sharp prime-factor/exponent count removes the auxiliary maximum:
uniformly in `B ≥ 0`, only two logarithms remain before the `H₃` mass. -/
theorem liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage_source_le_log_sq
    (N : ℕ) (B : ℝ) (hN : 3 ≤ N) (hB : 0 ≤ B) :
    liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage N B ≤
      (3 * (N : ℝ) ^ (2 / 3 : ℝ) *
        (((1 / Real.log 2) * (1 + 1 / Real.log 2)) * Real.log N ^ 2)) *
        liuPanPrimePowerH3Mass (panModulusCutoff N B) := by
  let Q := panModulusCutoff N B
  let D : ℝ := (1 / Real.log 2) * (1 + 1 / Real.log 2)
  let R : ℝ := 3 * (N : ℝ) ^ (2 / 3 : ℝ)
  have hQsq := panModulusCutoff_sq_le N B hN hB
  have hQle : Q ≤ N := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · calc
        Q ≤ Q * Q := le_mul_of_one_le_right' (Nat.one_le_iff_ne_zero.mpr hQ)
        _ = Q ^ 2 := by ring
        _ ≤ N := hQsq
  unfold liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage
  change (∑ q ∈ range (Q + 1),
    liuPanPrimePowerModulusWeight q *
      (liuPanAggregateInverseLogNoncoprimeCorrectionMaxY N q /
        Nat.totient q)) ≤ _
  calc
    _ ≤ ∑ q ∈ range (Q + 1),
        liuPanPrimePowerModulusWeight q *
          (R * (D * Real.log N ^ 2) / Nat.totient q) := by
      apply sum_le_sum
      intro q hq
      by_cases hq0 : q = 0
      · subst q
        simp [liuPanPrimePowerModulusWeight_zero]
      · apply mul_le_mul_of_nonneg_left
        · apply div_le_div_of_nonneg_right
          · exact
              (liuPanAggregateInverseLogNoncoprimeCorrectionMaxY_source_le
                N q (by omega)).trans
                (mul_le_mul_of_nonneg_left
                  (liuPanNoncoprimePrimePowerCountMax_le_log_sq N q hN
                    (Nat.pos_of_ne_zero hq0)
                    ((Nat.le_of_lt_succ (mem_range.mp hq)).trans hQle))
                  (by positivity))
          · exact Nat.cast_nonneg _
        · exact liuPanPrimePowerModulusWeight_nonneg q
    _ = (R * (D * Real.log N ^ 2)) * liuPanPrimePowerH3Mass Q := by
      unfold liuPanPrimePowerH3Mass
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      ring
    _ = _ := by rfl

/-- The modulus-noncoprime correction has the unconditional
`N^(2/3) log(N)^8` scale, uniformly in the Pan parameter `B ≥ 0`. -/
theorem
    liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage_le_rpow_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ), 3 ≤ N → 0 ≤ B →
      liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage N B ≤
        C * (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (8 : ℝ) := by
  obtain ⟨C₃, hC₃, hH₃⟩ := liuPanPrimePowerH3Mass_le_polylog
  let D : ℝ := (1 / Real.log 2) * (1 + 1 / Real.log 2)
  let C : ℝ := 3 * D * (64 * C₃)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨C, by positivity, ?_⟩
  intro N B hN hB
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hH :
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ≤
        (64 * C₃) * Real.log N ^ (6 : ℝ) := by
    calc
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ≤
          C₃ * Real.log (panModulusCutoff N B + 2 : ℕ) ^ (6 : ℝ) :=
        by simpa only [Nat.cast_add, Nat.cast_ofNat] using
          hH₃ (panModulusCutoff N B)
      _ ≤ C₃ * (2 * Real.log N) ^ (6 : ℝ) := by
        have hlogQ0 :
            0 ≤ Real.log (panModulusCutoff N B + 2 : ℕ) :=
          Real.log_nonneg (by
            exact_mod_cast
              (show 1 ≤ panModulusCutoff N B + 2 by omega))
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hlogQ0
            (liuPanPrimePower_cutoff_log_add_two_le_two_mul_log N B hN hB)
            (by norm_num)) hC₃.le
      _ = (64 * C₃) * Real.log N ^ (6 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  calc
    liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage N B ≤
        (3 * (N : ℝ) ^ (2 / 3 : ℝ) *
          (D * Real.log N ^ 2)) *
          liuPanPrimePowerH3Mass (panModulusCutoff N B) := by
      simpa [D] using
        liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage_source_le_log_sq
          N B hN hB
    _ ≤ (3 * (N : ℝ) ^ (2 / 3 : ℝ) *
          (D * Real.log N ^ 2)) *
          ((64 * C₃) * Real.log N ^ (6 : ℝ)) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = C * (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (8 : ℝ) := by
      rw [show (8 : ℝ) = 2 + 6 by norm_num, Real.rpow_add hlogpos]
      simp only [Real.rpow_ofNat]
      dsimp [C]
      ring

/-- Every fixed logarithmic saving eventually dominates the unconditional
noncoprime correction, uniformly for all `B ≥ 0`. -/
theorem eventually_liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage_le
    (A : ℝ) (_hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ B : ℝ, 0 ≤ B →
        liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage N B ≤
          C * N / Real.log N ^ A := by
  obtain ⟨C, hC, hpoly⟩ :=
    liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage_le_rpow_polylog
  have hreal : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (A + 8) ≤ x ^ (1 / 3 : ℝ) := by
    have hbound := (isLittleO_log_rpow_rpow_atTop (A + 8)
      (by norm_num : (0 : ℝ) < 1 / 3)).bound (show 0 < (1 : ℝ) by norm_num)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) _),
      one_mul] at hx
    exact hx
  have hnat : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (A + 8) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  rcases eventually_atTop.mp hnat with ⟨N0, hN0⟩
  refine ⟨C, hC, max N0 3, ?_⟩
  intro N hN B hB
  have hN0' : N0 ≤ N := (le_max_left N0 3).trans hN
  have hN3 : 3 ≤ N := (le_max_right N0 3).trans hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale :
      (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (8 : ℝ) ≤
        (N : ℝ) / Real.log N ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogpos A)]
    calc
      ((N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (8 : ℝ)) *
          Real.log N ^ A =
          (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (A + 8) := by
        rw [Real.rpow_add hlogpos]
        ring
      _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left (hN0 N hN0')
          (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
  calc
    liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage N B ≤
        C * (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (8 : ℝ) :=
      hpoly N B hN3 hB
    _ = C * ((N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ (8 : ℝ)) := by
      ring
    _ ≤ C * ((N : ℝ) / Real.log N ^ A) :=
      mul_le_mul_of_nonneg_left hscale hC.le
    _ = C * N / Real.log N ^ A := by ring

/-- The exact principal Abel term is ordinary PNT error minus the noncoprime
prime-power correction.  The source cutoffs and the common `y` are unchanged. -/
theorem liuPanAggregateInverseLogPrincipalPsiTerm_eq_pnt_sub_noncoprime
    (y X q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPrincipalPsiTerm y X q f =
      liuPanAggregateInverseLogPrincipalPNTTerm y X q f -
        liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm y X q f := by
  unfold liuPanAggregateInverseLogPrincipalPsiTerm
    liuPanAggregateInverseLogPrincipalPNTTerm
    liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm
  simp_rw [liuPanAggregatePrincipalPsiTerm_eq_pnt_sub_noncoprime]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- The nonprincipal contribution after substitution into the same Abel shell
and prefix sums. -/
noncomputable def liuPanAggregateInverseLogNonprincipalPsiTerm
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregateNonprincipalPsiTerm k
        (liuPanAbelSourceCutoff y X k) q l f -
      liuPanAggregateNonprincipalPsiTerm k
        (liuPanAbelSourceCutoff y X (k + 1)) q l f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregateNonprincipalPsiTerm n
      (liuPanAbelSourceCutoff y X (n + 1)) q l f

@[simp] theorem liuPanAggregateInverseLogNonprincipalPsiTerm_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNonprincipalPsiTerm y X 0 l f = 0 := by
  simp [liuPanAggregateInverseLogNonprincipalPsiTerm,
    liuPanAggregateNonprincipalPsiTerm]

@[simp] theorem liuPanAggregateInverseLogNonprincipalPsiTerm_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNonprincipalPsiTerm y X 1 l f = 0 := by
  simp [liuPanAggregateInverseLogNonprincipalPsiTerm]

/-- One character's exact inverse-log hyperbola convolution.  The source and
von Mangoldt factors remain paired before any norm is taken. -/
noncomputable def liuPanSourceLogLambdaCharacterHyperbola
    (y X q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ a ∈ Icc 1 X, ((f a : ℂ) * χ (a : ZMod q)) *
    liuPanLogLambdaCharacterPrefix (y / a) q χ

/-- For one character, the shared-`y` Abel shell is exactly the original
source/Lambda hyperbola convolution. -/
theorem liuPanSourceLogLambdaCharacterHyperbola_eq_abel
    (y X q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) :
    liuPanSourceLogLambdaCharacterHyperbola y X q f χ =
      (∑ k ∈ Icc 1 y, ((Real.log (k : ℝ))⁻¹ : ℂ) *
        (liuPanSourceCharacterPrefix
              (liuPanAbelSourceCutoff y X k) q f χ *
            liuPanLambdaCharacterPrefix k q χ -
          liuPanSourceCharacterPrefix
              (liuPanAbelSourceCutoff y X (k + 1)) q f χ *
            liuPanLambdaCharacterPrefix k q χ)) +
      ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
        (liuPanSourceCharacterPrefix
            (liuPanAbelSourceCutoff y X (n + 1)) q f χ *
          liuPanLambdaCharacterPrefix n q χ) := by
  let F : ℕ → ℕ → ℂ := fun t a =>
    ((f a : ℂ) * χ (a : ZMod q)) * liuPanLambdaCharacterPrefix t q χ
  have hsource (t A : ℕ) :
      (∑ a ∈ Icc 1 A, F t a) =
        liuPanSourceCharacterPrefix A q f χ *
          liuPanLambdaCharacterPrefix t q χ := by
    unfold F liuPanSourceCharacterPrefix
    rw [sum_mul]
  have hend := sum_source_eq_sum_quotient_shells
    (R := ℂ) y X (fun k => ((Real.log (k : ℝ))⁻¹ : ℂ)) F (by simp)
  have hprefix := sum_source_prefix_eq_sum_aggregate_prefix
    (R := ℂ) y X (fun n => (liuPanInverseLogAbelWeight n : ℂ)) F
  unfold liuPanSourceLogLambdaCharacterHyperbola
  simp_rw [liuPanLogLambdaCharacterPrefix_eq_discreteAbel, mul_add]
  rw [sum_add_distrib]
  calc
    (∑ a ∈ Icc 1 X,
        ((f a : ℂ) * χ (a : ZMod q)) *
          (((Real.log (y / a : ℕ))⁻¹ : ℂ) *
            liuPanLambdaCharacterPrefix (y / a) q χ)) +
        ∑ a ∈ Icc 1 X,
          ((f a : ℂ) * χ (a : ZMod q)) *
            ∑ n ∈ range (y / a), (liuPanInverseLogAbelWeight n : ℂ) *
              liuPanLambdaCharacterPrefix n q χ =
      (∑ a ∈ Icc 1 X,
          ((Real.log (y / a : ℕ))⁻¹ : ℂ) * F (y / a) a) +
        ∑ a ∈ Icc 1 X, ∑ n ∈ range (y / a),
          (liuPanInverseLogAbelWeight n : ℂ) * F n a := by
      congr 1
      · apply sum_congr rfl
        intro a ha
        unfold F
        ring
      · apply sum_congr rfl
        intro a ha
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        unfold F
        ring
    _ = _ := by
      rw [hend, hprefix]
      simp_rw [hsource]

/-- The nonprincipal inverse-log term in its exact character-by-character
hyperbola form.  Modulus zero is assigned zero canonically. -/
noncomputable def liuPanAggregateNonprincipalLogLambdaHyperbola
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
        star (χ (l : ZMod q)) *
          liuPanSourceLogLambdaCharacterHyperbola y X q f χ

@[simp] theorem liuPanAggregateNonprincipalLogLambdaHyperbola_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateNonprincipalLogLambdaHyperbola y X 0 l f = 0 := by
  simp [liuPanAggregateNonprincipalLogLambdaHyperbola]

@[simp] theorem liuPanAggregateNonprincipalLogLambdaHyperbola_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateNonprincipalLogLambdaHyperbola y X 1 l f = 0 := by
  simp [liuPanAggregateNonprincipalLogLambdaHyperbola]

/-- Exact pre-norm hyperbola identity for the nonprincipal part of the aggregate
inverse-log discrepancy.  The source coefficient and Lambda prefix stay coupled
inside each character summand. -/
theorem liuPanAggregateInverseLogNonprincipalPsiTerm_eq_logLambdaHyperbola
    {y X q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateInverseLogNonprincipalPsiTerm y X q l f =
      liuPanAggregateNonprincipalLogLambdaHyperbola y X q l f := by
  classical
  have hswapIcc (G : ℕ → DirichletCharacter ℂ q → ℂ) :
      (∑ k ∈ Icc 1 y, ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          G k χ) =
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          ∑ k ∈ Icc 1 y, G k χ := by
    rw [sum_comm]
  have hswapRange (G : ℕ → DirichletCharacter ℂ q → ℂ) :
      (∑ n ∈ range y, ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          G n χ) =
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          ∑ n ∈ range y, G n χ := by
    rw [sum_comm]
  unfold liuPanAggregateInverseLogNonprincipalPsiTerm
    liuPanAggregateNonprincipalLogLambdaHyperbola
    liuPanAggregateNonprincipalPsiTerm
  rw [if_neg hq.ne']
  simp_rw [liuPanSourceLogLambdaCharacterHyperbola_eq_abel]
  simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, mul_sum]
  rw [hswapIcc, hswapIcc, hswapRange]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· - ·)
    · apply sum_congr rfl
      intro χ hχ
      apply sum_congr rfl
      intro k hk
      ring
    · apply sum_congr rfl
      intro χ hχ
      apply sum_congr rfl
      intro k hk
      ring
  · apply sum_congr rfl
    intro χ hχ
    apply sum_congr rfl
    intro n hn
    ring

/-- Expanded form of the nonprincipal hyperbola identity, displaying both
finite source and Lambda sums explicitly. -/
theorem liuPanAggregateInverseLogNonprincipalPsiTerm_eq_character_hyperbola
    {y X q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateInverseLogNonprincipalPsiTerm y X q l f =
      (Nat.totient q : ℂ)⁻¹ *
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          star (χ (l : ZMod q)) *
            ∑ a ∈ Icc 1 X, ((f a : ℂ) * χ (a : ZMod q)) *
              ∑ m ∈ range (y / a + 1),
                ((Λ m / Real.log (m : ℝ) : ℝ) : ℂ) *
                  χ (m : ZMod q) := by
  rw [liuPanAggregateInverseLogNonprincipalPsiTerm_eq_logLambdaHyperbola f hq]
  simp [liuPanAggregateNonprincipalLogLambdaHyperbola,
    liuPanSourceLogLambdaCharacterHyperbola,
    liuPanLogLambdaCharacterPrefix, hq.ne']

/-- The logarithmic hyperbola sum regrouped by exact conductor. -/
noncomputable def liuPanAggregateLogLambdaConductorSum
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q,
        ∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
            (fun χ => χ.conductor = d),
          star (χ (l : ZMod q)) *
            liuPanSourceLogLambdaCharacterHyperbola y X q f χ

@[simp] theorem liuPanAggregateLogLambdaConductorSum_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaConductorSum y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaConductorSum]

@[simp] theorem liuPanAggregateLogLambdaConductorSum_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaConductorSum y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaConductorSum]

/-- Regrouping the logarithmic hyperbola by conductor is exact and precedes
every norm or Cauchy--Schwarz inequality. -/
theorem liuPanAggregateNonprincipalLogLambdaHyperbola_eq_conductorSum
    {y X q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateNonprincipalLogLambdaHyperbola y X q l f =
      liuPanAggregateLogLambdaConductorSum y X q l f := by
  classical
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold liuPanAggregateNonprincipalLogLambdaHyperbola
    liuPanAggregateLogLambdaConductorSum
  rw [if_neg hq.ne', if_neg hq.ne']
  congr 1
  calc
    (∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
        star (χ (l : ZMod q)) *
          liuPanSourceLogLambdaCharacterHyperbola y X q f χ) =
      ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
        ∑ d ∈ Icc 2 q, if χ.conductor = d then
          star (χ (l : ZMod q)) *
            liuPanSourceLogLambdaCharacterHyperbola y X q f χ
        else 0 := by
          apply sum_congr rfl
          intro χ hχ
          have hχne : χ ≠ 1 := by
            simpa [liuPanPrimePowerNonprincipalCharacters] using hχ
          have hdne : χ.conductor ≠ 1 := fun hd =>
            hχne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
          have hdmem : χ.conductor ∈ Icc 2 q := by
            rw [mem_Icc]
            exact ⟨by
              have := Nat.pos_of_ne_zero χ.conductor_ne_zero
              omega,
              Nat.le_of_dvd hq χ.conductor_dvd_level⟩
          simp [hdmem]
    _ = ∑ d ∈ Icc 2 q,
        ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
          if χ.conductor = d then
            star (χ (l : ZMod q)) *
              liuPanSourceLogLambdaCharacterHyperbola y X q f χ
          else 0 := by
            rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [sum_filter]

/-- The conductor-grouped logarithmic hyperbola reindexed by primitive
characters and their unique lifts to level `q`. -/
noncomputable def liuPanAggregateLogLambdaPrimitiveLiftSum
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q, if hdq : d ∣ q then
        ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
          star ((DirichletCharacter.changeLevel hdq ψ) (l : ZMod q)) *
            liuPanSourceLogLambdaCharacterHyperbola y X q f
              (DirichletCharacter.changeLevel hdq ψ)
      else 0

@[simp] theorem liuPanAggregateLogLambdaPrimitiveLiftSum_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaPrimitiveLiftSum y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaPrimitiveLiftSum]

@[simp] theorem liuPanAggregateLogLambdaPrimitiveLiftSum_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaPrimitiveLiftSum y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaPrimitiveLiftSum]

/-- Exact primitive-character reindexing of the logarithmic hyperbola. -/
theorem liuPanAggregateLogLambdaConductorSum_eq_primitiveLiftSum
    {y X q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateLogLambdaConductorSum y X q l f =
      liuPanAggregateLogLambdaPrimitiveLiftSum y X q l f := by
  classical
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold liuPanAggregateLogLambdaConductorSum
    liuPanAggregateLogLambdaPrimitiveLiftSum
  rw [if_neg hq.ne', if_neg hq.ne']
  congr 1
  apply sum_congr rfl
  intro d hdmem
  have hd : 1 < d := (mem_Icc.mp hdmem).1
  by_cases hdq : d ∣ q
  · rw [dif_pos hdq,
      liuPanPrimePowerNonprincipalCharacters_filter_conductor_eq_lifts
        q d hdq hd]
    unfold liuPanPrimePowerPrimitiveCharacterLifts
    rw [sum_image]
    exact Set.injOn_of_injective
      (DirichletCharacter.changeLevel_injective hdq)
  · rw [dif_neg hdq]
    have hempty :
        (liuPanPrimePowerNonprincipalCharacters q).filter
            (fun χ => χ.conductor = d) = ∅ := by
      rw [filter_eq_empty_iff]
      intro χ hχ hcond
      exact hdq (hcond ▸ χ.conductor_dvd_level)
    rw [hempty]
    simp

/-- Primitive conductors at most `D₀`, retained in their exact lifted hyperbola
form. -/
noncomputable def liuPanAggregateLogLambdaLowConductorSum
    (D₀ y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q, if d ≤ D₀ then
        if hdq : d ∣ q then
          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
            star ((DirichletCharacter.changeLevel hdq ψ) (l : ZMod q)) *
              liuPanSourceLogLambdaCharacterHyperbola y X q f
                (DirichletCharacter.changeLevel hdq ψ)
        else 0
      else 0

/-- Primitive conductors above `D₀`, the medium/high bilinear family. -/
noncomputable def liuPanAggregateLogLambdaMediumHighConductorSum
    (D₀ y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q, if D₀ < d then
        if hdq : d ∣ q then
          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
            star ((DirichletCharacter.changeLevel hdq ψ) (l : ZMod q)) *
              liuPanSourceLogLambdaCharacterHyperbola y X q f
                (DirichletCharacter.changeLevel hdq ψ)
        else 0
      else 0

@[simp] theorem liuPanAggregateLogLambdaLowConductorSum_zero
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorSum D₀ y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaLowConductorSum]

@[simp] theorem liuPanAggregateLogLambdaMediumHighConductorSum_zero
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaMediumHighConductorSum D₀ y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaMediumHighConductorSum]

@[simp] theorem liuPanAggregateLogLambdaLowConductorSum_one
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorSum D₀ y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaLowConductorSum]

@[simp] theorem liuPanAggregateLogLambdaMediumHighConductorSum_one
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaMediumHighConductorSum D₀ y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaMediumHighConductorSum]

/-- Exact low/medium-high conductor partition at an arbitrary threshold `D₀`. -/
theorem liuPanAggregateLogLambdaPrimitiveLiftSum_eq_low_add_mediumHigh
    {y X q l : ℕ} (D₀ : ℕ) (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateLogLambdaPrimitiveLiftSum y X q l f =
      liuPanAggregateLogLambdaLowConductorSum D₀ y X q l f +
        liuPanAggregateLogLambdaMediumHighConductorSum D₀ y X q l f := by
  classical
  unfold liuPanAggregateLogLambdaPrimitiveLiftSum
    liuPanAggregateLogLambdaLowConductorSum
    liuPanAggregateLogLambdaMediumHighConductorSum
  rw [if_neg hq.ne', if_neg hq.ne', if_neg hq.ne', ← mul_add]
  congr 1
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  by_cases hdD : d ≤ D₀
  · simp [hdD, Nat.not_lt.mpr hdD]
  · simp [hdD, Nat.lt_of_not_ge hdD]

/-- The nonprincipal Abel term is exactly the low-conductor plus medium/high
primitive hyperbola families. -/
theorem liuPanAggregateInverseLogNonprincipalPsiTerm_eq_low_add_mediumHigh
    {y X q l : ℕ} (D₀ : ℕ) (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateInverseLogNonprincipalPsiTerm y X q l f =
      liuPanAggregateLogLambdaLowConductorSum D₀ y X q l f +
        liuPanAggregateLogLambdaMediumHighConductorSum D₀ y X q l f := by
  rw [liuPanAggregateInverseLogNonprincipalPsiTerm_eq_logLambdaHyperbola f hq,
    liuPanAggregateNonprincipalLogLambdaHyperbola_eq_conductorSum f hq,
    liuPanAggregateLogLambdaConductorSum_eq_primitiveLiftSum f hq,
    liuPanAggregateLogLambdaPrimitiveLiftSum_eq_low_add_mediumHigh D₀ f hq]

/-- The substituted Abel term splits exactly into principal and nonprincipal
parts, still before taking an absolute value. -/
theorem liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_nonprincipal
    {y X q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateInverseLogPsiCharacterTerm y X q l f =
      liuPanAggregateInverseLogPrincipalPsiTerm y X q f +
        liuPanAggregateInverseLogNonprincipalPsiTerm y X q l f := by
  unfold liuPanAggregateInverseLogPsiCharacterTerm
    liuPanAggregateInverseLogPrincipalPsiTerm
    liuPanAggregateInverseLogNonprincipalPsiTerm
    liuPanAggregatePsiCharacterExpansion
  simp only [if_neg hq.ne', mul_add, mul_sub, sum_add_distrib,
    sum_sub_distrib]
  ring

/-- At modulus one the substituted Abel character term is principal only. -/
@[simp] theorem liuPanAggregateInverseLogPsiCharacterTerm_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPsiCharacterTerm y X 1 l f =
      liuPanAggregateInverseLogPrincipalPsiTerm y X 1 f := by
  rw [liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_nonprincipal
    f (by omega)]
  simp

/-- The actual inverse-log aggregate psi term at modulus one is principal only. -/
theorem liuPanAggregateInverseLogPsiTerm_complex_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    (liuPanAggregateInverseLogPsiTerm y X 1 l f : ℂ) =
      liuPanAggregateInverseLogPrincipalPsiTerm y X 1 f := by
  have hl : IsUnit (l : ZMod 1) := by
    simpa only [Subsingleton.elim (l : ZMod 1) 1] using
      (isUnit_one : IsUnit (1 : ZMod 1))
  calc
    (liuPanAggregateInverseLogPsiTerm y X 1 l f : ℂ) =
        liuPanAggregateInverseLogPsiCharacterTerm y X 1 l f :=
      liuPanAggregateInverseLogPsiTerm_complex_eq_characterTerm f
        (by omega) hl
    _ = liuPanAggregateInverseLogPrincipalPsiTerm y X 1 f :=
      liuPanAggregateInverseLogPsiCharacterTerm_one y X l f

/-- The complete exact character reduction after Abel substitution: the
principal term remains separate, while the nonprincipal part is one coupled
source/Lambda hyperbola sum. -/
theorem liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_hyperbola
    {y X q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateInverseLogPsiCharacterTerm y X q l f =
      liuPanAggregateInverseLogPrincipalPsiTerm y X q f +
        liuPanAggregateNonprincipalLogLambdaHyperbola y X q l f := by
  rw [liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_nonprincipal
      f hq,
    liuPanAggregateInverseLogNonprincipalPsiTerm_eq_logLambdaHyperbola f hq]

/-- The exact three-way analytic split at conductor threshold `D₀`. -/
theorem
    liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_low_add_mediumHigh
    {y X q l : ℕ} (D₀ : ℕ) (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateInverseLogPsiCharacterTerm y X q l f =
      liuPanAggregateInverseLogPrincipalPsiTerm y X q f +
        liuPanAggregateLogLambdaLowConductorSum D₀ y X q l f +
        liuPanAggregateLogLambdaMediumHighConductorSum D₀ y X q l f := by
  rw [liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_nonprincipal
      f hq,
    liuPanAggregateInverseLogNonprincipalPsiTerm_eq_low_add_mediumHigh
      D₀ f hq]
  ring

/-! ## Source-family decomposition -/

/-- Canonical `y ≤ N` maximum of the ordinary principal PNT-error term. -/
noncomputable def liuPanAggregateInverseLogPrincipalPNTMaxY
    (N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (N + 1)).image fun y =>
    ‖liuPanAggregateInverseLogPrincipalPNTTerm y N q f‖).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Canonical reduced-residue maximum of the nonprincipal character term. -/
noncomputable def liuPanAggregateInverseLogNonprincipalPsiMaxL
    (y N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image fun l =>
      ‖liuPanAggregateInverseLogNonprincipalPsiTerm y N q l f‖).max'
        (Finset.image_nonempty.mpr h)
  else 0

/-- Canonical `y ≤ N` maximum of the nonprincipal character term. -/
noncomputable def liuPanAggregateInverseLogNonprincipalPsiMaxY
    (N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (N + 1)).image fun y =>
    liuPanAggregateInverseLogNonprincipalPsiMaxL y N q f).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Reduced-residue maximum of the low-conductor primitive hyperbola family. -/
noncomputable def liuPanAggregateLogLambdaLowConductorMaxL
    (D₀ y N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image fun l =>
      ‖liuPanAggregateLogLambdaLowConductorSum D₀ y N q l f‖).max'
        (Finset.image_nonempty.mpr h)
  else 0

/-- Reduced-residue maximum of the medium/high primitive hyperbola family. -/
noncomputable def liuPanAggregateLogLambdaMediumHighConductorMaxL
    (D₀ y N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image fun l =>
      ‖liuPanAggregateLogLambdaMediumHighConductorSum D₀ y N q l f‖).max'
        (Finset.image_nonempty.mpr h)
  else 0

/-- Shared-`y` maximum of the low-conductor primitive hyperbola family. -/
noncomputable def liuPanAggregateLogLambdaLowConductorMaxY
    (D₀ N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (N + 1)).image fun y =>
    liuPanAggregateLogLambdaLowConductorMaxL D₀ y N q f).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Shared-`y` maximum of the medium/high primitive hyperbola family. -/
noncomputable def liuPanAggregateLogLambdaMediumHighConductorMaxY
    (D₀ N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (N + 1)).image fun y =>
    liuPanAggregateLogLambdaMediumHighConductorMaxL D₀ y N q f).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Modulus-weighted ordinary principal PNT-error average. -/
noncomputable def liuMainPanAggregateInverseLogPrincipalPNTAverage
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q *
      liuPanAggregateInverseLogPrincipalPNTMaxY N q f

/-- Modulus-weighted nonprincipal character average, still before any
all-character Cauchy--Schwarz estimate. -/
noncomputable def liuMainPanAggregateInverseLogNonprincipalPsiAverage
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q *
      liuPanAggregateInverseLogNonprincipalPsiMaxY N q f

/-- Modulus-weighted low-conductor family, retaining the original
squarefree-`3^omega` weights. -/
noncomputable def liuMainPanAggregateLogLambdaLowConductorAverage
    (D₀ N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q *
      liuPanAggregateLogLambdaLowConductorMaxY D₀ N q f

/-- Modulus-weighted medium/high primitive bilinear hyperbola family. -/
noncomputable def liuMainPanAggregateLogLambdaMediumHighConductorAverage
    (D₀ N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q *
      liuPanAggregateLogLambdaMediumHighConductorMaxY D₀ N q f

/-- The exact conductor partition passes through the reduced-residue maximum
using only the final two-term triangle inequality. -/
theorem liuPanAggregateInverseLogNonprincipalPsiMaxL_le_low_add_mediumHigh
    (D₀ N y q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNonprincipalPsiMaxL y N q f ≤
      liuPanAggregateLogLambdaLowConductorMaxL D₀ y N q f +
        liuPanAggregateLogLambdaMediumHighConductorMaxL D₀ y N q f := by
  by_cases hq0 : q = 0
  · subst q
    simp [liuPanAggregateInverseLogNonprincipalPsiMaxL,
      liuPanAggregateLogLambdaLowConductorMaxL,
      liuPanAggregateLogLambdaMediumHighConductorMaxL]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    have hS : (unitResidues q).Nonempty := by
      by_cases hq1 : q = 1
      · subst q
        simp
      · refine ⟨1, ?_⟩
        rw [unitResidues, mem_filter, mem_range]
        exact ⟨by omega, by simp⟩
    unfold liuPanAggregateInverseLogNonprincipalPsiMaxL
      liuPanAggregateLogLambdaLowConductorMaxL
      liuPanAggregateLogLambdaMediumHighConductorMaxL
    dsimp only
    rw [dif_pos hS, dif_pos hS, dif_pos hS]
    apply max'_le
    intro z hz
    rcases mem_image.mp hz with ⟨l, hl, rfl⟩
    calc
      ‖liuPanAggregateInverseLogNonprincipalPsiTerm y N q l f‖ =
          ‖liuPanAggregateLogLambdaLowConductorSum D₀ y N q l f +
            liuPanAggregateLogLambdaMediumHighConductorSum
              D₀ y N q l f‖ := by
        rw [liuPanAggregateInverseLogNonprincipalPsiTerm_eq_low_add_mediumHigh
          D₀ f hq]
      _ ≤ ‖liuPanAggregateLogLambdaLowConductorSum D₀ y N q l f‖ +
          ‖liuPanAggregateLogLambdaMediumHighConductorSum
            D₀ y N q l f‖ := norm_add_le _ _
      _ ≤ _ := add_le_add
        (le_max'
          ((unitResidues q).image fun r =>
            ‖liuPanAggregateLogLambdaLowConductorSum D₀ y N q r f‖)
          ‖liuPanAggregateLogLambdaLowConductorSum D₀ y N q l f‖
          (mem_image.mpr ⟨l, hl, rfl⟩))
        (le_max'
          ((unitResidues q).image fun r =>
            ‖liuPanAggregateLogLambdaMediumHighConductorSum D₀ y N q r f‖)
          ‖liuPanAggregateLogLambdaMediumHighConductorSum D₀ y N q l f‖
          (mem_image.mpr ⟨l, hl, rfl⟩))

/-- The exact conductor partition passes through the shared-`y` maximum. -/
theorem liuPanAggregateInverseLogNonprincipalPsiMaxY_le_low_add_mediumHigh
    (D₀ N q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNonprincipalPsiMaxY N q f ≤
      liuPanAggregateLogLambdaLowConductorMaxY D₀ N q f +
        liuPanAggregateLogLambdaMediumHighConductorMaxY D₀ N q f := by
  unfold liuPanAggregateInverseLogNonprincipalPsiMaxY
    liuPanAggregateLogLambdaLowConductorMaxY
    liuPanAggregateLogLambdaMediumHighConductorMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  exact
    (liuPanAggregateInverseLogNonprincipalPsiMaxL_le_low_add_mediumHigh
      D₀ N y q f).trans
      (add_le_add
        (le_max'
          ((range (N + 1)).image fun t =>
            liuPanAggregateLogLambdaLowConductorMaxL D₀ t N q f)
          (liuPanAggregateLogLambdaLowConductorMaxL D₀ y N q f)
          (mem_image.mpr ⟨y, hy, rfl⟩))
        (le_max'
          ((range (N + 1)).image fun t =>
            liuPanAggregateLogLambdaMediumHighConductorMaxL D₀ t N q f)
          (liuPanAggregateLogLambdaMediumHighConductorMaxL D₀ y N q f)
          (mem_image.mpr ⟨y, hy, rfl⟩)))

/-- The modulus-weighted nonprincipal average is bounded by the two exact
conductor families, with no all-character Cauchy step. -/
theorem liuMainPanAggregateInverseLogNonprincipalPsiAverage_le_low_add_mediumHigh
    (D₀ N : ℕ) (f : ℕ → ℝ) (B : ℝ) :
    liuMainPanAggregateInverseLogNonprincipalPsiAverage N f B ≤
      liuMainPanAggregateLogLambdaLowConductorAverage D₀ N f B +
        liuMainPanAggregateLogLambdaMediumHighConductorAverage D₀ N f B := by
  unfold liuMainPanAggregateInverseLogNonprincipalPsiAverage
    liuMainPanAggregateLogLambdaLowConductorAverage
    liuMainPanAggregateLogLambdaMediumHighConductorAverage
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (liuPanAggregateInverseLogNonprincipalPsiMaxY_le_low_add_mediumHigh
      D₀ N q f)
    (liuPanPrimePowerModulusWeight_nonneg q)

/-- For Liu's source, the real noncoprime correction is nonnegative. -/
theorem liuPanAggregateInverseLogNoncoprimeCorrection_nonneg
    (N y q : ℕ) :
    0 ≤ liuPanAggregateInverseLogNoncoprimeCorrection y N q
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
  rw [liuPanAggregateInverseLogNoncoprimeCorrection_eq_source]
  apply sum_nonneg
  intro a ha
  by_cases hcop : a.Coprime q
  · rw [if_pos hcop]
    apply mul_nonneg (liuWeight_nonneg _ _ _ _)
    unfold liuPanLogNoncoprimeCorrection
    apply sum_nonneg
    intro n hn
    by_cases hncop : n.Coprime q
    · rw [if_pos hncop]
    · rw [if_neg hncop]
      apply div_nonneg vonMangoldt_nonneg
      rcases n with _ | n
      · simp
      · exact Real.log_nonneg (by norm_num)
  · simp [hcop]

/-- Pointwise, the aggregate psi term has exactly the ordinary principal PNT
error, the positive noncoprime correction, and the nonprincipal character term. -/
theorem abs_liuPanAggregateInverseLogPsiTerm_le_pnt_add_noncoprime_add_nonprincipal
    {N y q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    |liuPanAggregateInverseLogPsiTerm y N q l
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
      ‖liuPanAggregateInverseLogPrincipalPNTTerm y N q
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))‖ +
      liuPanAggregateInverseLogNoncoprimeCorrection y N q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) /
        Nat.totient q +
      ‖liuPanAggregateInverseLogNonprincipalPsiTerm y N q l
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))‖ := by
  let f := liuWeight N (liuSourceZ10 N) (liuSourceY3 N)
  have heq :
      (liuPanAggregateInverseLogPsiTerm y N q l f : ℂ) =
        liuPanAggregateInverseLogPrincipalPNTTerm y N q f -
          liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm y N q f +
          liuPanAggregateInverseLogNonprincipalPsiTerm y N q l f := by
    calc
      (liuPanAggregateInverseLogPsiTerm y N q l f : ℂ) =
          liuPanAggregateInverseLogPsiCharacterTerm y N q l f :=
        liuPanAggregateInverseLogPsiTerm_complex_eq_characterTerm f hq hl
      _ = liuPanAggregateInverseLogPrincipalPsiTerm y N q f +
          liuPanAggregateInverseLogNonprincipalPsiTerm y N q l f :=
        liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_nonprincipal
          f hq
      _ = _ := by
        rw [liuPanAggregateInverseLogPrincipalPsiTerm_eq_pnt_sub_noncoprime]
  calc
    |liuPanAggregateInverseLogPsiTerm y N q l f| =
        ‖(liuPanAggregateInverseLogPsiTerm y N q l f : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖liuPanAggregateInverseLogPrincipalPNTTerm y N q f -
          liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm y N q f +
          liuPanAggregateInverseLogNonprincipalPsiTerm y N q l f‖ := by
      rw [heq]
    _ ≤ ‖liuPanAggregateInverseLogPrincipalPNTTerm y N q f‖ +
          ‖liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm y N q f‖ +
          ‖liuPanAggregateInverseLogNonprincipalPsiTerm y N q l f‖ :=
      (norm_add_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
    _ = _ := by
      rw [liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm_eq_real,
        norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (liuPanAggregateInverseLogNoncoprimeCorrection_nonneg N y q)]
      norm_cast

/-- The pointwise split passes through the reduced-residue maximum without
mixing the principal and nonprincipal families. -/
theorem liuPanAggregateInverseLogPsiMaxL_le_pnt_add_noncoprime_add_nonprincipal
    (N y q : ℕ) :
    liuPanAggregateInverseLogPsiMaxL y N q
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      ‖liuPanAggregateInverseLogPrincipalPNTTerm y N q
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))‖ +
      liuPanAggregateInverseLogNoncoprimeCorrection y N q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) /
        Nat.totient q +
      liuPanAggregateInverseLogNonprincipalPsiMaxL y N q
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
  by_cases hq0 : q = 0
  · subst q
    simp [liuPanAggregateInverseLogNonprincipalPsiMaxL]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    have hS : (unitResidues q).Nonempty := by
      by_cases hq1 : q = 1
      · subst q
        simp
      · refine ⟨1, ?_⟩
        rw [unitResidues, mem_filter, mem_range]
        exact ⟨by omega, by simp⟩
    unfold liuPanAggregateInverseLogPsiMaxL
      liuPanAggregateInverseLogNonprincipalPsiMaxL
    dsimp only
    rw [dif_pos hS, dif_pos hS]
    apply max'_le
    intro z hz
    rcases mem_image.mp hz with ⟨l, hl, rfl⟩
    have hlunit : IsUnit (l : ZMod q) :=
      (ZMod.isUnit_iff_coprime l q).mpr (mem_filter.mp hl).2
    exact
      (abs_liuPanAggregateInverseLogPsiTerm_le_pnt_add_noncoprime_add_nonprincipal
        hq hlunit).trans
        (add_le_add le_rfl
          (le_max'
            ((unitResidues q).image fun r =>
              ‖liuPanAggregateInverseLogNonprincipalPsiTerm y N q r
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))‖)
            _
            (mem_image.mpr ⟨l, hl, rfl⟩)))

/-- The three-term split passes through the shared `y ≤ N` maximum. -/
theorem liuPanAggregateInverseLogPsiMaxY_le_pnt_add_noncoprime_add_nonprincipal
    (N q : ℕ) :
    liuPanAggregateInverseLogPsiMaxY N q N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      liuPanAggregateInverseLogPrincipalPNTMaxY N q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) +
        liuPanAggregateInverseLogNoncoprimeCorrectionMaxY N q /
          Nat.totient q +
        liuPanAggregateInverseLogNonprincipalPsiMaxY N q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
  unfold liuPanAggregateInverseLogPsiMaxY
    liuPanAggregateInverseLogPrincipalPNTMaxY
    liuPanAggregateInverseLogNoncoprimeCorrectionMaxY
    liuPanAggregateInverseLogNonprincipalPsiMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  apply
    (liuPanAggregateInverseLogPsiMaxL_le_pnt_add_noncoprime_add_nonprincipal
      N y q).trans
  apply add_le_add
  · apply add_le_add
    · apply le_max'
      exact mem_image.mpr ⟨y, hy, rfl⟩
    · apply div_le_div_of_nonneg_right
      · apply le_max'
        exact mem_image.mpr ⟨y, hy, rfl⟩
      · exact Nat.cast_nonneg _
  · apply le_max'
    exact mem_image.mpr ⟨y, hy, rfl⟩

/-- Exact source-family bookkeeping: the original aggregate psi average is
bounded by the ordinary principal PNT family, the now-unconditional noncoprime
correction, and the still-conductor-grouped nonprincipal family. -/
theorem liuMainPanAggregateInverseLogPsiAverage_le_decomposition
    (N : ℕ) (B : ℝ) :
    liuMainPanAggregateInverseLogPsiAverage N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      liuMainPanAggregateInverseLogPrincipalPNTAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B +
        liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage N B +
        liuMainPanAggregateInverseLogNonprincipalPsiAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B := by
  unfold liuMainPanAggregateInverseLogPsiAverage
    liuMainPanAggregateInverseLogPrincipalPNTAverage
    liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage
    liuMainPanAggregateInverseLogNonprincipalPsiAverage
    liuPanPrimePowerModulusWeight
  calc
    _ ≤ ∑ q ∈ range (panModulusCutoff N B + 1),
        ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card) *
          (liuPanAggregateInverseLogPrincipalPNTMaxY N q
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) +
            liuPanAggregateInverseLogNoncoprimeCorrectionMaxY N q /
              Nat.totient q +
            liuPanAggregateInverseLogNonprincipalPsiMaxY N q
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact
          liuPanAggregateInverseLogPsiMaxY_le_pnt_add_noncoprime_add_nonprincipal
            N q
      · positivity
    _ = _ := by
      simp_rw [mul_add]
      rw [sum_add_distrib, sum_add_distrib]

/-- Uniform principal/PNT maximum obtained by splitting
`y < N^(5/6)` from the complementary range. -/
theorem liuPanAggregateInverseLogPrincipalPNTMaxY_le_split
    (D C : ℝ) (hD : 0 < D) (hC : 0 ≤ C) (T0 Ngeom : ℕ)
    (hscalar : ∀ t : ℕ, T0 ≤ t →
      |liuPanLogPNTError t| ≤ C * t / Real.log t ^ D)
    (hgeom : ∀ N : ℕ, Ngeom ≤ N →
      ∀ y : ℕ, (N : ℝ) ^ (5 / 6 : ℝ) ≤ y →
      ∀ a ∈ Icc 1 N,
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a ≠ 0 →
          (N : ℝ) ^ (1 / 9 : ℝ) ≤ (y / a : ℕ))
    {N q : ℕ} (hN : 3 ≤ N) (hNgeom : Ngeom ≤ N)
    (hT0 : (T0 : ℝ) ≤ (N : ℝ) ^ (1 / 9 : ℝ)) :
    liuPanAggregateInverseLogPrincipalPNTMaxY N q
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      (((2 * (Real.log 4 + 5) * (Real.log 2)⁻¹) *
          (N : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log N)) +
        (C * (9 : ℝ) ^ D * N / Real.log N ^ D) *
          (1 + Real.log N)) / Nat.totient q := by
  let K : ℝ := 2 * (Real.log 4 + 5) * (Real.log 2)⁻¹
  let S : ℝ := K * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log N)
  let L : ℝ := (C * (9 : ℝ) ^ D * N / Real.log N ^ D) *
    (1 + Real.log N)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hS : 0 ≤ S := by
    dsimp [S, K]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  unfold liuPanAggregateInverseLogPrincipalPNTMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (mem_range.mp hy)
  rw [liuPanAggregateInverseLogPrincipalPNTTerm_eq_source,
    norm_div, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right
  · by_cases hsmall : (y : ℝ) < (N : ℝ) ^ (5 / 6 : ℝ)
    · calc
        |∑ a ∈ Icc 1 N, if a.Coprime q then
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              liuPanLogPNTError (y / a)
          else 0| ≤
            K * y * (1 + Real.log N) := by
          simpa [K] using abs_liuPanPrincipalPNTSourceSum_le_global N y q
        _ ≤ S := by
          dsimp [S]
          gcongr
        _ ≤ S + L := le_add_of_nonneg_right hL
    · have hlarge :
          (N : ℝ) ^ (5 / 6 : ℝ) ≤ (y : ℝ) := le_of_not_gt hsmall
      calc
        |∑ a ∈ Icc 1 N, if a.Coprime q then
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              liuPanLogPNTError (y / a)
          else 0| ≤
            (C * (9 : ℝ) ^ D * y / Real.log N ^ D) *
              (1 + Real.log N) :=
          abs_liuPanPrincipalPNTSourceSum_le_large D C hD hC T0 hscalar
            hN hT0 (hgeom N hNgeom y hlarge)
        _ ≤ L := by
          dsimp [L]
          gcongr
        _ ≤ S + L := le_add_of_nonneg_left hS
  · exact Nat.cast_nonneg _

/-- The split source estimate lifts through exactly the existing `H₃` modulus
mass, including the totalized zero modulus. -/
theorem liuMainPanAggregateInverseLogPrincipalPNTAverage_le_split_mul_H3
    (D C : ℝ) (hD : 0 < D) (hC : 0 ≤ C) (T0 Ngeom : ℕ)
    (hscalar : ∀ t : ℕ, T0 ≤ t →
      |liuPanLogPNTError t| ≤ C * t / Real.log t ^ D)
    (hgeom : ∀ N : ℕ, Ngeom ≤ N →
      ∀ y : ℕ, (N : ℝ) ^ (5 / 6 : ℝ) ≤ y →
      ∀ a ∈ Icc 1 N,
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a ≠ 0 →
          (N : ℝ) ^ (1 / 9 : ℝ) ≤ (y / a : ℕ))
    {N : ℕ} (B : ℝ) (hN : 3 ≤ N) (hNgeom : Ngeom ≤ N)
    (hT0 : (T0 : ℝ) ≤ (N : ℝ) ^ (1 / 9 : ℝ)) :
    liuMainPanAggregateInverseLogPrincipalPNTAverage N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      (((2 * (Real.log 4 + 5) * (Real.log 2)⁻¹) *
          (N : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log N)) +
        (C * (9 : ℝ) ^ D * N / Real.log N ^ D) *
          (1 + Real.log N)) *
        liuPanPrimePowerH3Mass (panModulusCutoff N B) := by
  let M : ℝ :=
    ((2 * (Real.log 4 + 5) * (Real.log 2)⁻¹) *
        (N : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log N)) +
      (C * (9 : ℝ) ^ D * N / Real.log N ^ D) *
        (1 + Real.log N)
  unfold liuMainPanAggregateInverseLogPrincipalPNTAverage
  calc
    _ ≤ ∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q * (M / Nat.totient q) := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact liuPanAggregateInverseLogPrincipalPNTMaxY_le_split
          D C hD hC T0 Ngeom hscalar hgeom hN hNgeom hT0
      · exact liuPanPrimePowerModulusWeight_nonneg q
    _ = M * liuPanPrimePowerH3Mass (panModulusCutoff N B) := by
      unfold liuPanPrimePowerH3Mass
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      ring
    _ = _ := by rfl

/-- Minimal varying-source hypothesis for the ordinary PNT part of the
principal character.  No pointwise `psi(x) ∼ x` statement is promoted to this
uniform aggregate estimate. -/
def LiuMainPanAggregateInverseLogPrincipalPNTSourceFamilyBound : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      liuMainPanAggregateInverseLogPrincipalPNTAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
        C * N / Real.log N ^ A

/-- The ordinary principal source family is unconditional.  The estimate is
uniform in every nonnegative Pan cutoff parameter, which lets it be combined
with either nonprincipal conductor regime without changing cutoffs. -/
theorem eventually_liuMainPanAggregateInverseLogPrincipalPNTAverage_le
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ B : ℝ, 0 ≤ B →
        liuMainPanAggregateInverseLogPrincipalPNTAverage N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
          C * N / Real.log N ^ A := by
  let D : ℝ := A + 8
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨C₁, hC₁, T0, hscalar⟩ :=
    eventually_abs_liuPanLogPNTError_le_div_log_rpow D hD
  obtain ⟨Ngeom, hgeom⟩ :=
    eventually_liuWeight_quotient_ge_rpow_one_ninth
  obtain ⟨C₃, hC₃, hH₃⟩ := liuPanPrimePowerH3Mass_le_polylog
  let K : ℝ := 2 * (Real.log 4 + 5) * (Real.log 2)⁻¹
  let C : ℝ := 128 * C₃ * (K + C₁ * (9 : ℝ) ^ D)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hgrowthReal : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (A + 7) ≤ x ^ (1 / 6 : ℝ) := by
    have hbound := (isLittleO_log_rpow_rpow_atTop (A + 7)
      (by norm_num : (0 : ℝ) < 1 / 6)).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) _),
      one_mul] at hx
    exact hx
  have hgrowthNat : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (A + 7) ≤ (N : ℝ) ^ (1 / 6 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hgrowthReal
  rcases eventually_atTop.mp hgrowthNat with ⟨Ngrowth, hgrowth⟩
  have hTReal : ∀ᶠ x : ℝ in atTop,
      (T0 : ℝ) ≤ x ^ (1 / 9 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).eventually
      (eventually_ge_atTop (T0 : ℝ))
  have hTNat : ∀ᶠ N : ℕ in atTop,
      (T0 : ℝ) ≤ (N : ℝ) ^ (1 / 9 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hTReal
  rcases eventually_atTop.mp hTNat with ⟨NT, hT⟩
  refine ⟨C, by
    dsimp [C]
    positivity, max 3 (max Ngeom (max Ngrowth NT)), ?_⟩
  intro N hN B hB
  have hN3 : 3 ≤ N := (le_max_left 3 _).trans hN
  have hNgeom : Ngeom ≤ N :=
    (le_max_of_le_right (le_max_left Ngeom _)).trans hN
  have hNgrowth : Ngrowth ≤ N :=
    (le_max_of_le_right (le_max_of_le_right (le_max_left Ngrowth NT))).trans hN
  have hNT : NT ≤ N :=
    (le_max_of_le_right (le_max_of_le_right (le_max_right Ngrowth NT))).trans hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogOne : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast hN3)
  have hH :
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ≤
        (64 * C₃) * Real.log N ^ (6 : ℝ) := by
    calc
      liuPanPrimePowerH3Mass (panModulusCutoff N B) ≤
          C₃ * Real.log (panModulusCutoff N B + 2 : ℕ) ^ (6 : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          hH₃ (panModulusCutoff N B)
      _ ≤ C₃ * (2 * Real.log N) ^ (6 : ℝ) := by
        have hlogQ0 :
            0 ≤ Real.log (panModulusCutoff N B + 2 : ℕ) :=
          Real.log_nonneg (by
            exact_mod_cast
              (show 1 ≤ panModulusCutoff N B + 2 by omega))
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hlogQ0
            (liuPanPrimePower_cutoff_log_add_two_le_two_mul_log N B hN3 hB)
            (by norm_num)) hC₃.le
      _ = (64 * C₃) * Real.log N ^ (6 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  have hsmallScale :
      (N : ℝ) ^ (5 / 6 : ℝ) * Real.log N ^ (7 : ℝ) ≤
        (N : ℝ) / Real.log N ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogN A)]
    calc
      ((N : ℝ) ^ (5 / 6 : ℝ) * Real.log N ^ (7 : ℝ)) *
          Real.log N ^ A =
          (N : ℝ) ^ (5 / 6 : ℝ) * Real.log N ^ (A + 7) := by
        rw [Real.rpow_add hlogN]
        ring
      _ ≤ (N : ℝ) ^ (5 / 6 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_left (hgrowth N hNgrowth)
          (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
  have hlargeScale :
      (N : ℝ) * Real.log N ^ (7 : ℝ) / Real.log N ^ D ≤
        (N : ℝ) / Real.log N ^ A := by
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogN D)
      (Real.rpow_pos_of_pos hlogN A)]
    calc
      ((N : ℝ) * Real.log N ^ (7 : ℝ)) * Real.log N ^ A =
          (N : ℝ) * Real.log N ^ (A + 7) := by
        rw [Real.rpow_add hlogN]
        ring
      _ ≤ (N : ℝ) * Real.log N ^ (A + 8) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
        exact Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
      _ = (N : ℝ) * Real.log N ^ D := by rfl
  have hbase :=
    liuMainPanAggregateInverseLogPrincipalPNTAverage_le_split_mul_H3
      D C₁ hD hC₁.le T0 Ngeom hscalar hgeom B hN3 hNgeom (hT N hNT)
  calc
    liuMainPanAggregateInverseLogPrincipalPNTAverage N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      ((K * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log N)) +
        (C₁ * (9 : ℝ) ^ D * N / Real.log N ^ D) *
          (1 + Real.log N)) *
        liuPanPrimePowerH3Mass (panModulusCutoff N B) := by
      simpa [K] using hbase
    _ ≤ ((K * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log N)) +
          (C₁ * (9 : ℝ) ^ D * N / Real.log N ^ D) *
            (1 + Real.log N)) *
        ((64 * C₃) * Real.log N ^ (6 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hH
      positivity
    _ ≤ (128 * C₃ * K) *
          ((N : ℝ) ^ (5 / 6 : ℝ) * Real.log N ^ (7 : ℝ)) +
        (128 * C₃ * (C₁ * (9 : ℝ) ^ D)) *
          ((N : ℝ) * Real.log N ^ (7 : ℝ) / Real.log N ^ D) := by
      have hone : 1 + Real.log (N : ℝ) ≤ 2 * Real.log N := by linarith
      rw [add_mul]
      apply add_le_add
      · calc
          (K * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log N)) *
              ((64 * C₃) * Real.log N ^ (6 : ℝ)) ≤
            (K * (N : ℝ) ^ (5 / 6 : ℝ) * (2 * Real.log N)) *
              ((64 * C₃) * Real.log N ^ (6 : ℝ)) := by
            gcongr
          _ = (128 * C₃ * K) *
              ((N : ℝ) ^ (5 / 6 : ℝ) * Real.log N ^ (7 : ℝ)) := by
            norm_num [Real.rpow_ofNat]
            ring
      · calc
          ((C₁ * (9 : ℝ) ^ D * N / Real.log N ^ D) *
              (1 + Real.log N)) *
              ((64 * C₃) * Real.log N ^ (6 : ℝ)) ≤
            ((C₁ * (9 : ℝ) ^ D * N / Real.log N ^ D) *
              (2 * Real.log N)) *
              ((64 * C₃) * Real.log N ^ (6 : ℝ)) := by
            gcongr
          _ = (128 * C₃ * (C₁ * (9 : ℝ) ^ D)) *
              ((N : ℝ) * Real.log N ^ (7 : ℝ) /
                Real.log N ^ D) := by
            norm_num [Real.rpow_ofNat]
            ring
    _ ≤ (128 * C₃ * K) * ((N : ℝ) / Real.log N ^ A) +
        (128 * C₃ * (C₁ * (9 : ℝ) ^ D)) *
          ((N : ℝ) / Real.log N ^ A) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hsmallScale (by positivity))
        (mul_le_mul_of_nonneg_left hlargeScale (by positivity))
    _ = C * N / Real.log N ^ A := by
      dsimp [C]
      ring

/-- The named principal/PNT source-family contract is therefore inhabited
without an additional analytic assumption. -/
theorem liuMainPanAggregateInverseLogPrincipalPNTSourceFamilyBound :
    LiuMainPanAggregateInverseLogPrincipalPNTSourceFamilyBound := by
  intro A hA
  obtain ⟨C, hC, N0, hbound⟩ :=
    eventually_liuMainPanAggregateInverseLogPrincipalPNTAverage_le A hA
  exact ⟨C, hC, 0, le_rfl, N0, fun N hN => hbound N hN 0 le_rfl⟩

/-- A shared-cutoff principal/PNT source-family estimate. -/
def LiuMainPanAggregatePrincipalPNTBoundAt
    (A C B : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N →
    liuMainPanAggregateInverseLogPrincipalPNTAverage N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      C * N / Real.log N ^ A

/-- The low-conductor Siegel--Walfisz input at a chosen conductor threshold. -/
def LiuMainPanAggregateLowConductorSiegelWalfiszBoundAt
    (D₀ : ℕ → ℕ) (A C B : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N →
    liuMainPanAggregateLogLambdaLowConductorAverage (D₀ N) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      C * N / Real.log N ^ A

/-- The medium/high-conductor weighted primitive bilinear hyperbola maximal
input at the same conductor threshold and modulus cutoff. -/
def LiuMainPanAggregateMediumHighConductorBilinearBoundAt
    (D₀ : ℕ → ℕ) (A C B : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N →
    liuMainPanAggregateLogLambdaMediumHighConductorAverage (D₀ N) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      C * N / Real.log N ^ A

/-- The earlier three-part packaging with one shared modulus cutoff and one
conductor threshold function.  Its principal component is now unconditional;
the predicate is retained as a convenient bundled interface. -/
def LiuMainPanAggregateInverseLogPsiConductorSplitSourceFamilyBound : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ D₀ : ℕ → ℕ,
    ∃ Cpnt : ℝ, 0 < Cpnt ∧
    ∃ Clow : ℝ, 0 < Clow ∧
    ∃ Chigh : ℝ, 0 < Chigh ∧
    ∃ B : ℝ, 0 ≤ B ∧
    ∃ N0 : ℕ,
      LiuMainPanAggregatePrincipalPNTBoundAt A Cpnt B N0 ∧
      LiuMainPanAggregateLowConductorSiegelWalfiszBoundAt
        D₀ A Clow B N0 ∧
      LiuMainPanAggregateMediumHighConductorBilinearBoundAt
        D₀ A Chigh B N0

/-- The only source-family inputs still open: low primitive conductors and the
medium/high primitive bilinear family, at one shared cutoff. -/
def LiuMainPanAggregateInverseLogPsiNonprincipalConductorSourceFamilyBound :
    Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ D₀ : ℕ → ℕ,
    ∃ Clow : ℝ, 0 < Clow ∧
    ∃ Chigh : ℝ, 0 < Chigh ∧
    ∃ B : ℝ, 0 ≤ B ∧
    ∃ N0 : ℕ,
      LiuMainPanAggregateLowConductorSiegelWalfiszBoundAt
        D₀ A Clow B N0 ∧
      LiuMainPanAggregateMediumHighConductorBilinearBoundAt
        D₀ A Chigh B N0

/-- The two genuinely analytic source-family inputs, stated with one shared
modulus cutoff: ordinary PNT for the principal family and the conductor-first
nonprincipal estimate.  The noncoprime correction is intentionally absent. -/
def LiuMainPanAggregateInverseLogPsiRemainingSourceFamilyBound : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ Cpnt : ℝ, 0 < Cpnt ∧ ∃ Cnonprincipal : ℝ, 0 < Cnonprincipal ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      liuMainPanAggregateInverseLogPrincipalPNTAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
          Cpnt * N / Real.log N ^ A ∧
        liuMainPanAggregateInverseLogNonprincipalPsiAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
          Cnonprincipal * N / Real.log N ^ A

/-- The principal/PNT, low-conductor Siegel--Walfisz, and medium/high weighted
primitive bilinear predicates imply the remaining two-family psi predicate. -/
theorem
    LiuMainPanAggregateInverseLogPsiConductorSplitSourceFamilyBound.to_remaining
    (h : LiuMainPanAggregateInverseLogPsiConductorSplitSourceFamilyBound) :
    LiuMainPanAggregateInverseLogPsiRemainingSourceFamilyBound := by
  intro A hA
  rcases h A hA with
    ⟨D₀, Cpnt, hCpnt, Clow, hClow, Chigh, hChigh, B, hB, N0,
      hpnt, hlow, hhigh⟩
  refine ⟨Cpnt, hCpnt, Clow + Chigh, by positivity, B, hB, N0, ?_⟩
  intro N hN
  constructor
  · exact hpnt N hN
  · calc
      liuMainPanAggregateInverseLogNonprincipalPsiAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
        liuMainPanAggregateLogLambdaLowConductorAverage (D₀ N) N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B +
          liuMainPanAggregateLogLambdaMediumHighConductorAverage (D₀ N) N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B :=
        liuMainPanAggregateInverseLogNonprincipalPsiAverage_le_low_add_mediumHigh
          (D₀ N) N (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B
      _ ≤ Clow * N / Real.log N ^ A +
          Chigh * N / Real.log N ^ A :=
        add_le_add (hlow N hN) (hhigh N hN)
      _ = (Clow + Chigh) * N / Real.log N ^ A := by ring

/-- The unconditional principal theorem reduces the remaining two-family
predicate to the low and medium/high nonprincipal conductor estimates alone. -/
theorem
    LiuMainPanAggregateInverseLogPsiNonprincipalConductorSourceFamilyBound.to_remaining
    (h :
      LiuMainPanAggregateInverseLogPsiNonprincipalConductorSourceFamilyBound) :
    LiuMainPanAggregateInverseLogPsiRemainingSourceFamilyBound := by
  intro A hA
  rcases h A hA with
    ⟨D₀, Clow, hClow, Chigh, hChigh, B, hB, Nnonprincipal, hlow, hhigh⟩
  obtain ⟨Cpnt, hCpnt, Npnt, hpnt⟩ :=
    eventually_liuMainPanAggregateInverseLogPrincipalPNTAverage_le A hA
  refine
    ⟨Cpnt, hCpnt, Clow + Chigh, by positivity, B, hB,
      max Npnt Nnonprincipal, ?_⟩
  intro N hN
  have hNpnt : Npnt ≤ N := (le_max_left _ _).trans hN
  have hNnonprincipal : Nnonprincipal ≤ N := (le_max_right _ _).trans hN
  constructor
  · exact hpnt N hNpnt B hB
  · calc
      liuMainPanAggregateInverseLogNonprincipalPsiAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
        liuMainPanAggregateLogLambdaLowConductorAverage (D₀ N) N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B +
          liuMainPanAggregateLogLambdaMediumHighConductorAverage (D₀ N) N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B :=
        liuMainPanAggregateInverseLogNonprincipalPsiAverage_le_low_add_mediumHigh
          (D₀ N) N (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B
      _ ≤ Clow * N / Real.log N ^ A +
          Chigh * N / Real.log N ^ A :=
        add_le_add (hlow N hNnonprincipal) (hhigh N hNnonprincipal)
      _ = (Clow + Chigh) * N / Real.log N ^ A := by ring

/-- The remaining PNT/nonprincipal source-family inputs imply the original
aggregate psi contract because the noncoprime family is unconditional. -/
theorem LiuMainPanAggregateInverseLogPsiRemainingSourceFamilyBound.to_psi
    (h : LiuMainPanAggregateInverseLogPsiRemainingSourceFamilyBound) :
    LiuMainPanAggregateInverseLogPsiSourceFamilyBound := by
  intro A hA
  rcases h A hA with
    ⟨Cpnt, hCpnt, Cnonprincipal, hCnonprincipal, B, hB, Nanalytic, hanalytic⟩
  rcases
      eventually_liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage_le
        A hA with
    ⟨Cnoncoprime, hCnoncoprime, Nnoncoprime, hnoncoprime⟩
  refine
    ⟨Cpnt + Cnoncoprime + Cnonprincipal, by positivity, B, hB,
      max Nanalytic Nnoncoprime, ?_⟩
  intro N hN
  have hNa : Nanalytic ≤ N := (le_max_left _ _).trans hN
  have hNnc : Nnoncoprime ≤ N := (le_max_right _ _).trans hN
  rcases hanalytic N hNa with ⟨hpnt, hnonprincipal⟩
  have hnc := hnoncoprime N hNnc B hB
  unfold LiuMainPanAggregateInverseLogPsiBoundAt
  calc
    liuMainPanAggregateInverseLogPsiAverage N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      liuMainPanAggregateInverseLogPrincipalPNTAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B +
        liuMainPanAggregateInverseLogNoncoprimeCorrectionAverage N B +
        liuMainPanAggregateInverseLogNonprincipalPsiAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B :=
      liuMainPanAggregateInverseLogPsiAverage_le_decomposition N B
    _ ≤ Cpnt * N / Real.log N ^ A +
          Cnoncoprime * N / Real.log N ^ A +
          Cnonprincipal * N / Real.log N ^ A :=
      add_le_add (add_le_add hpnt hnc) hnonprincipal
    _ = (Cpnt + Cnoncoprime + Cnonprincipal) * N /
        Real.log N ^ A := by ring

/-- The exact three-regime analytic predicate implies the original aggregate
source-family psi contract; the noncoprime correction is supplied
unconditionally. -/
theorem LiuMainPanAggregateInverseLogPsiConductorSplitSourceFamilyBound.to_psi
    (h : LiuMainPanAggregateInverseLogPsiConductorSplitSourceFamilyBound) :
    LiuMainPanAggregateInverseLogPsiSourceFamilyBound :=
  h.to_remaining.to_psi

/-- Low-conductor Siegel--Walfisz plus the medium/high primitive bilinear
estimate now suffice for the full aggregate psi source-family contract.
Principal PNT and noncoprime terms are supplied unconditionally. -/
theorem
    LiuMainPanAggregateInverseLogPsiNonprincipalConductorSourceFamilyBound.to_psi
    (h :
      LiuMainPanAggregateInverseLogPsiNonprincipalConductorSourceFamilyBound) :
    LiuMainPanAggregateInverseLogPsiSourceFamilyBound :=
  h.to_remaining.to_psi

/-!
## Remaining analytic split

The ordinary principal/PNT family is closed unconditionally by
`liuMainPanAggregateInverseLogPrincipalPNTSourceFamilyBound`, and the
noncoprime family is also closed unconditionally.  Exactly two analytic regimes
remain, neither asserted here:

* low primitive conductors, to be treated by Siegel--Walfisz;
* medium and high conductors, requiring a weighted primitive bilinear
  hyperbola maximal estimate.
-/

end MathlibNt.SieveTheory.LiuWeight
