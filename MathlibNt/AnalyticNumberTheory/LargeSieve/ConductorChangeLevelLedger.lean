

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanSmallRangeAndCharacters

/-!
 # Conductor grouping and change-level correction ledger

A finite, quantitative reduction from all nonprincipal Dirichlet characters to
primitive characters grouped by conductor.  The principal summand is retained
literally.  No prime-number theorem or Bombieri--Vinogradov assertion occurs.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section


/-- Pointwise `4‖b(n)‖²` bound for the squared change-level correction. -/
theorem conductorChangeLevelError_norm_sq_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (n : ℤ) :
    ‖conductorChangeLevelError χ b n‖ ^ 2 ≤ 4 * ‖b n‖ ^ 2 := by
  have hq := χ.norm_le_one (n : ZMod q)
  have hc := χ.primitiveCharacter.norm_le_one (n : ZMod χ.conductor)
  have h₁ : ‖b n * χ (n : ZMod q)‖ ≤ ‖b n‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (b n)]
  have h₂ : ‖b n * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ ‖b n‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (b n)]
  have he : ‖conductorChangeLevelError χ b n‖ ≤ 2 * ‖b n‖ := by
    unfold conductorChangeLevelError
    exact (norm_sub_le _ _).trans (by linarith)
  nlinarith [norm_nonneg (conductorChangeLevelError χ b n), norm_nonneg (b n)]


/-- Squared prefix correction. -/
def conductorErrorPrefixSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (y : ℕ) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M + 1) (M + y), conductorChangeLevelError χ b n‖ ^ 2

/-- Maximum squared prefix correction over `0 ≤ y ≤ N`. -/
def conductorErrorPrefixMaxSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image (fun y => conductorErrorPrefixSquare χ b M y)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)


/-- Squared prefix for an arbitrary (possibly imprimitive) character. -/
def characterPrefixSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (y : ℕ) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M + 1) (M + y), b n * χ (n : ZMod q)‖ ^ 2

/-- Maximum squared prefix for an arbitrary character. -/
def characterPrefixMaxSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image (fun y => characterPrefixSquare χ b M y)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

private theorem norm_add_sq_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_add_le x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x + y),
    norm_nonneg x, norm_nonneg y]

/-- Per-character maximal reduction to its conductor primitive character plus
its literal correction maximum. -/
theorem characterPrefixMaxSquare_le_conductor_add_error
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    characterPrefixMaxSquare χ b M N ≤
      2 * (primitiveCharacterPrefixMaxSquare b M N χ.conductor
          (conductorPrimitiveCharacter χ) +
        conductorErrorPrefixMaxSquare χ b M N) := by
  unfold characterPrefixMaxSquare
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  rw [characterPrefixSquare, characterInterval_eq_conductorPrimitive_add_error]
  refine (norm_add_sq_le_two _ _).trans ?_
  gcongr
  · exact primitiveCharacterPrefixSquare_le_max b M hyN
      (conductorPrimitiveCharacter χ)
  · unfold conductorErrorPrefixMaxSquare
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

/-- Positive divisors at least two: precisely the possible nonprincipal
conductors at a positive level. -/
def nonprincipalConductors (q : ℕ) : Finset ℕ :=
  q.divisors.filter (fun d => 2 ≤ d)


/-- At one positive level, characters of nontrivial conductor are in bijection
with primitive characters over the divisors `d ≥ 2` of that level. -/
theorem sum_nonprincipal_by_conductor
    {q : ℕ} (hq : 0 < q)
    (F : (d : ℕ) → PrimitiveCharacter d → ℝ) :
    (∑ χ ∈ nonprincipalCharacters q,
        F χ.conductor (conductorPrimitiveCharacter χ)) =
      ∑ d ∈ nonprincipalConductors q, ∑ ψ : PrimitiveCharacter d, F d ψ := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [Finset.sum_sigma' (s := nonprincipalConductors q)
    (t := fun d => Finset.univ) (f := F)]
  let T := (nonprincipalConductors q).sigma
    (fun d => (Finset.univ : Finset (PrimitiveCharacter d)))
  let lift : (p : Σ d, PrimitiveCharacter d) → p ∈ T →
      DirichletCharacter ℂ q := fun p hp =>
    DirichletCharacter.changeLevel
      ((Finset.mem_filter.mp (Finset.mem_sigma.mp hp).1).1 |>
        Nat.mem_divisors.mp |>.1) p.2.1
  have lift_injective : ∀ (p p' : Σ d, PrimitiveCharacter d)
      (hp : p ∈ T) (hp' : p' ∈ T), lift p hp = lift p' hp' → p = p' := by
    intro p p' hp hp' h
    rcases p with ⟨d, ψ⟩
    rcases p' with ⟨d', ψ'⟩
    have hdq : d ∣ q :=
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).1).1 |>
        Nat.mem_divisors.mp |>.1
    have hdq' : d' ∣ q :=
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hp').1).1 |>
        Nat.mem_divisors.mp |>.1
    have hd : d = d' := by
      calc
        d = (lift ⟨d, ψ⟩ hp).conductor := by
          simp only [lift, DirichletCharacter.conductor_changeLevel,
            primitive_conductor]
        _ = (lift ⟨d', ψ'⟩ hp').conductor := congrArg (·.conductor) h
        _ = d' := by
          simp only [lift, DirichletCharacter.conductor_changeLevel,
            primitive_conductor]
    subst d'
    have hψ : ψ = ψ' := by
      apply Subtype.ext
      apply DirichletCharacter.changeLevel_injective hdq
      exact h
    exact congrArg (Sigma.mk d) hψ
  have encode_mem : ∀ χ ∈ nonprincipalCharacters q,
      (⟨χ.conductor, conductorPrimitiveCharacter χ⟩ : Σ d, PrimitiveCharacter d) ∈ T := by
    intro χ hχ
    rw [Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ _⟩
    change χ.conductor ∈ nonprincipalConductors q
    rw [nonprincipalConductors, Finset.mem_filter]
    refine ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq.ne'⟩, ?_⟩
    have hc1 : χ.conductor ≠ 1 :=
      mem_nonprincipalCharacters_iff_conductor_ne_one.mp hχ
    have hcpos : 0 < χ.conductor := Nat.pos_of_dvd_of_pos χ.conductor_dvd_level hq
    omega
  have lift_mem : ∀ p (hp : p ∈ T), lift p hp ∈ nonprincipalCharacters q := by
    intro p hp
    rw [mem_nonprincipalCharacters_iff_conductor_ne_one]
    have hdmem : p.1 ∈ nonprincipalConductors q := (Finset.mem_sigma.mp hp).1
    have hd2 : 2 ≤ p.1 := (Finset.mem_filter.mp hdmem).2
    simp only [lift, DirichletCharacter.conductor_changeLevel, primitive_conductor]
    omega
  refine Finset.sum_bij'
    (fun χ hχ => ⟨χ.conductor, conductorPrimitiveCharacter χ⟩)
    lift encode_mem lift_mem ?_ ?_ ?_
  · intro χ hχ
    exact changeLevel_conductorPrimitiveCharacter χ
  · intro p hp
    apply lift_injective _ _ (encode_mem _ (lift_mem p hp)) hp
    exact changeLevel_conductorPrimitiveCharacter (lift p hp)
  · intro χ hχ
    rfl


end

end AnalyticNumberTheory.LargeSieve
