import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVSquareMeanToL1Dyadic

/-!
# Standard Bombieri--Vinogradov: finite character orthogonality

This file contains only the finite algebra between Chebyshev `Λ` sums in a
reduced residue class and Dirichlet-character prefix sums.  In particular, the
principal character is split literally before any estimate is made.  No
Bombieri--Vinogradov conclusion is assumed or stated.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The Chebyshev `Λ` coefficient, regarded as a complex coefficient. -/
def lambdaNatCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The Chebyshev prefix in one residue class, through the integer endpoint
`y`. -/
def lambdaAPPrefix (y q a : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (y + 1)).filter
      (fun n : ℕ => (n : ZMod q) = (a : ZMod q)),
    lambdaNatCoeff n

/-- The full Chebyshev prefix restricted to integers coprime to `q`. -/
def coprimeLambdaPrefix (y q : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (y + 1)).filter (fun n => n.Coprime q), lambdaNatCoeff n

/-- The level-`q` character transform of the Chebyshev prefix. -/
def lambdaCharacterPrefix (y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), lambdaNatCoeff n * χ (n : ZMod q)

/-- Character orthogonality expands a reduced-residue Chebyshev prefix exactly.
The normalization `1/φ(q)` is retained literally. -/
theorem lambdaAPPrefix_eq_character_average
    {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) (y : ℕ) :
    lambdaAPPrefix y q a =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hq))
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  unfold lambdaAPPrefix lambdaCharacterPrefix
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hfactor :
      (∑ χ : DirichletCharacter ℂ q,
        (q.totient : ℂ)⁻¹ *
          (star (χ (a : ZMod q)) * (lambdaNatCoeff n * χ (n : ZMod q)))) =
        (q.totient : ℂ)⁻¹ * lambdaNatCoeff n *
          ∑ χ : DirichletCharacter ℂ q,
            χ (n : ZMod q) * star (χ (a : ZMod q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  rw [hfactor, charOrthSum hq]
  by_cases heq : (n : ZMod q) = (a : ZMod q)
  · have hnu : IsUnit (n : ZMod q) := heq ▸ hau
    simp [heq, hau]
    field_simp
  · simp [heq]

/-- The principal character transform is exactly the coprime `Λ` total. -/
theorem lambdaCharacterPrefix_one (y q : ℕ) :
    lambdaCharacterPrefix y q (1 : DirichletCharacter ℂ q) =
      coprimeLambdaPrefix y q := by
  rw [lambdaCharacterPrefix, coprimeLambdaPrefix, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  change lambdaNatCoeff n * (if IsUnit (n : ZMod q) then 1 else 0) =
    if n.Coprime q then lambdaNatCoeff n else 0
  simp only [ZMod.isUnit_iff_coprime, mul_ite, mul_one, mul_zero]

/-- The principal contribution to the character average. -/
def principalLambdaContribution (y q : ℕ) : ℂ :=
  (q.totient : ℂ)⁻¹ * coprimeLambdaPrefix y q

/-- Its error relative to the global Chebyshev main term `y`. -/
def principalLambdaMainError (y q : ℕ) : ℂ :=
  coprimeLambdaPrefix y q - (y : ℂ)

/-- The reduced-residue Chebyshev error centered at the global main term. -/
def lambdaAPMainError (y q a : ℕ) : ℂ :=
  lambdaAPPrefix y q a - (q.totient : ℂ)⁻¹ * (y : ℂ)

/-- Literal principal/nonprincipal decomposition of the Chebyshev AP error.
The first summand is precisely the principal PNT-type error divided by `φ(q)`;
all character estimates apply only to the second summand. -/
theorem lambdaAPMainError_eq_principal_add_nonprincipal
    {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) (y : ℕ) :
    lambdaAPMainError y q a =
      (q.totient : ℂ)⁻¹ * principalLambdaMainError y q +
      (q.totient : ℂ)⁻¹ *
        ∑ χ ∈ nonprincipalCharacters q,
          star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ := by
  rw [lambdaAPMainError, lambdaAPPrefix_eq_character_average hq ha,
    sum_allCharacters_eq_principal_add_nonprincipal,
    lambdaCharacterPrefix_one]
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hone : (1 : DirichletCharacter ℂ q) (a : ZMod q) = 1 := by
    change (if IsUnit (a : ZMod q) then 1 else 0) = 1
    simp [hau]
  rw [hone, star_one, one_mul]
  unfold principalLambdaMainError
  ring

/-- A pointwise reduced-residue error is bounded by the literal principal error
plus the nonprincipal character transforms. -/
theorem norm_lambdaAPMainError_le_principal_add_nonprincipal
    {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) (y : ℕ) :
    ‖lambdaAPMainError y q a‖ ≤
      (q.totient : ℝ)⁻¹ *
        (‖principalLambdaMainError y q‖ +
          ∑ χ ∈ nonprincipalCharacters q, ‖lambdaCharacterPrefix y q χ‖) := by
  rw [lambdaAPMainError_eq_principal_add_nonprincipal hq ha]
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  calc
    _ ≤ ‖(q.totient : ℂ)⁻¹ * principalLambdaMainError y q‖ +
        ‖(q.totient : ℂ)⁻¹ *
          ∑ χ ∈ nonprincipalCharacters q,
            star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ‖ :=
      norm_add_le _ _
    _ = (q.totient : ℝ)⁻¹ * ‖principalLambdaMainError y q‖ +
        (q.totient : ℝ)⁻¹ *
          ‖∑ χ ∈ nonprincipalCharacters q,
            star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ‖ := by
      simp
    _ ≤ (q.totient : ℝ)⁻¹ * ‖principalLambdaMainError y q‖ +
        (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ nonprincipalCharacters q,
            ‖star (χ (a : ZMod q)) * lambdaCharacterPrefix y q χ‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (q.totient : ℝ)⁻¹ * ‖principalLambdaMainError y q‖ +
        (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ nonprincipalCharacters q, ‖lambdaCharacterPrefix y q χ‖ := by
      gcongr with χ hχ
      rw [norm_mul, norm_star]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (χ.norm_le_one (a : ZMod q))
    _ = _ := by ring

/-- Maximum principal PNT-type error through endpoint `N`. -/
def principalLambdaPrefixMaxError (N q : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image
    (fun y => ‖principalLambdaMainError y q‖)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Maximum transform amplitude for one character through endpoint `N`. -/
def lambdaCharacterPrefixMaxAmplitude
    (N q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ((Finset.range (N + 1)).image
    (fun y => ‖lambdaCharacterPrefix y q χ‖)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The Chebyshev AP error, maximized over canonical reduced residues and all
prefixes through `N`.  Adjoining zero gives the empty-modulus convention and a
canonical witness for `max'`. -/
def lambdaAPPrefixMaxError (N q : ℕ) : ℝ :=
  (insert 0 (((Finset.range (N + 1)).product
    (AnalyticNumberTheory.Sieve.unitResidues q)).image
      (fun p => ‖lambdaAPMainError p.1 q p.2‖))).max' (by simp)

/-- Exact finite prefix-max consequence of character orthogonality. -/
theorem lambdaAPPrefixMaxError_le_character_majorant
    {q N : ℕ} (hq : 0 < q) :
    lambdaAPPrefixMaxError N q ≤
      (q.totient : ℝ)⁻¹ *
        (principalLambdaPrefixMaxError N q +
          ∑ χ ∈ nonprincipalCharacters q,
            lambdaCharacterPrefixMaxAmplitude N q χ) := by
  have hprincipal (y : ℕ) (hy : y ∈ Finset.range (N + 1)) :
      ‖principalLambdaMainError y q‖ ≤ principalLambdaPrefixMaxError N q := by
    unfold principalLambdaPrefixMaxError
    exact Finset.le_max'
      ((Finset.range (N + 1)).image (fun y => ‖principalLambdaMainError y q‖)) _
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have hcharacter (y : ℕ) (hy : y ∈ Finset.range (N + 1))
      (χ : DirichletCharacter ℂ q) :
      ‖lambdaCharacterPrefix y q χ‖ ≤ lambdaCharacterPrefixMaxAmplitude N q χ := by
    unfold lambdaCharacterPrefixMaxAmplitude
    exact Finset.le_max'
      ((Finset.range (N + 1)).image (fun y => ‖lambdaCharacterPrefix y q χ‖)) _
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  unfold lambdaAPPrefixMaxError
  apply Finset.max'_le
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_image] at hz
  rcases hz with rfl | ⟨p, hp, rfl⟩
  · have hzero : 0 ∈ Finset.range (N + 1) := by simp
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (add_nonneg ((norm_nonneg _).trans (hprincipal 0 hzero))
        (Finset.sum_nonneg fun χ _ =>
          (norm_nonneg _).trans (hcharacter 0 hzero χ)))
  · rcases Finset.mem_product.mp hp with ⟨hyN, haq⟩
    have haCoprime : p.2.Coprime q := by
      have h := haq
      simp [AnalyticNumberTheory.Sieve.unitResidues] at h
      exact h.2
    refine (norm_lambdaAPMainError_le_principal_add_nonprincipal
      hq haCoprime p.1).trans ?_
    apply mul_le_mul_of_nonneg_left
    · exact add_le_add (hprincipal p.1 hyN)
        (Finset.sum_le_sum fun χ _ => hcharacter p.1 hyN χ)
    · exact inv_nonneg.mpr (by positivity)

end

end AnalyticNumberTheory.LargeSieve
