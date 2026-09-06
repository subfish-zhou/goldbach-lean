

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

/-- Integers in the interval on which changing from level `q` to the conductor
can produce an error. -/
def conductorBadSupport (q : ℕ) (M : ℤ) (N : ℕ) : Finset ℤ :=
  (Finset.Icc (M + 1) (M + N)).filter (fun n => ¬ IsCoprime n q)

@[simp] theorem mem_conductorBadSupport {q : ℕ} {M n : ℤ} {N : ℕ} :
    n ∈ conductorBadSupport q M N ↔
      M + 1 ≤ n ∧ n ≤ M + N ∧ ¬ IsCoprime n q := by
  simp [conductorBadSupport, and_assoc]

/-- The change-level error has exactly zero contribution away from the explicit
bad support. -/
theorem conductorChangeLevelError_eq_zero_of_not_mem
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ)
    {n : ℤ} (hn : n ∈ Finset.Icc (M + 1) (M + N))
    (hbad : n ∉ conductorBadSupport q M N) :
    conductorChangeLevelError χ b n = 0 := by
  apply conductorChangeLevelError_eq_zero_of_isCoprime
  by_contra h
  exact hbad (by simp [conductorBadSupport, hn, h])

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

/-- Exact support restriction for the finite correction energy. -/
theorem conductorChangeLevelError_energy_eq_badSupport
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖conductorChangeLevelError χ b n‖ ^ 2) =
      ∑ n ∈ conductorBadSupport q M N,
        ‖conductorChangeLevelError χ b n‖ ^ 2 := by
  rw [conductorBadSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hbad : ¬ IsCoprime n q
  · simp [hbad]
  · simp only [if_neg hbad]
    rw [conductorChangeLevelError_eq_zero_of_isCoprime χ b (not_not.mp hbad)]
    simp

/-- Explicit finite energy bound: only bad-prime-supported coefficients occur,
with pointwise constant four. -/
theorem conductorChangeLevelError_energy_le_badSupport
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖conductorChangeLevelError χ b n‖ ^ 2) ≤
      4 * ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2 := by
  rw [conductorChangeLevelError_energy_eq_badSupport, Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ => conductorChangeLevelError_norm_sq_le χ b n

/-- Squared prefix correction. -/
def conductorErrorPrefixSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (y : ℕ) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M + 1) (M + y), conductorChangeLevelError χ b n‖ ^ 2

/-- Maximum squared prefix correction over `0 ≤ y ≤ N`. -/
def conductorErrorPrefixMaxSquare {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image (fun y => conductorErrorPrefixSquare χ b M y)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Every correction prefix is controlled by `N` times its full interval
energy. -/
theorem conductorErrorPrefixSquare_le_energy
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ)
    {N y : ℕ} (hy : y ≤ N) :
    conductorErrorPrefixSquare χ b M y ≤
      (N : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖conductorChangeLevelError χ b n‖ ^ 2 := by
  unfold conductorErrorPrefixSquare
  refine (norm_finset_sum_sq_le_card_mul_sum_norm_sq
    (Finset.Icc (M + 1) (M + y)) (fun n => conductorChangeLevelError χ b n)).trans ?_
  have hcard : ((Finset.Icc (M + 1) (M + y)).card : ℝ) ≤ N := by
    rw [Int.card_Icc]
    have heq : (M + (y : ℤ) + 1 - (M + 1)).toNat = y := by
      congr 1
      omega
    rw [heq]
    exact_mod_cast hy
  have hsub : Finset.Icc (M + 1) (M + y) ⊆ Finset.Icc (M + 1) (M + N) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    refine ⟨hn.1, hn.2.trans ?_⟩
    have hyz : (y : ℤ) ≤ (N : ℤ) := by exact_mod_cast hy
    simpa [add_comm] using add_le_add_left hyz M
  calc
    ((Finset.Icc (M + 1) (M + y)).card : ℝ) *
        ∑ n ∈ Finset.Icc (M + 1) (M + y),
          ‖conductorChangeLevelError χ b n‖ ^ 2
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + y),
          ‖conductorChangeLevelError χ b n‖ ^ 2 := by
        gcongr
    _ ≤ (N : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N),
          ‖conductorChangeLevelError χ b n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => sq_nonneg _)
        · positivity

/-- Explicit support bound for the maximal correction. -/
theorem conductorErrorPrefixMaxSquare_le_badSupport
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    conductorErrorPrefixMaxSquare χ b M N ≤
      4 * (N : ℝ) * ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2 := by
  unfold conductorErrorPrefixMaxSquare
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  calc
    conductorErrorPrefixSquare χ b M y ≤
        (N : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N),
          ‖conductorChangeLevelError χ b n‖ ^ 2 :=
      conductorErrorPrefixSquare_le_energy χ b M hyN
    _ ≤ (N : ℝ) * (4 * ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2) := by
      gcongr
      exact conductorChangeLevelError_energy_le_badSupport χ b M N
    _ = _ := by ring

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

/-- Total `q/φ(q)` weight with which one primitive character of conductor `d`
appears among levels `1 ≤ q ≤ Q`.  This is the exact imprimitive multiplicity
with the analytic weight retained, rather than replaced by a crude count. -/
def imprimitiveConductorWeight (Q d : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q with d ∣ q, (q : ℝ) / (q.totient : ℝ)

/-- At one positive level, characters of nontrivial conductor are in bijection
with primitive characters over the divisors `d ≥ 2` of that level. -/
theorem sum_nonprincipal_by_conductor
    {q : ℕ} (hq : 0 < q)
    (F : (d : ℕ) → PrimitiveCharacter d → ℝ) :
    (∑ χ ∈ nonprincipalCharacters q,
        F χ.conductor (conductorPrimitiveCharacter χ)) =
      ∑ d ∈ nonprincipalConductors q, ∑ ψ : PrimitiveCharacter d, F d ψ := by
  letI : NeZero q := ⟨hq.ne'⟩
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

/-- Exact global conductor regrouping.  Every primitive character of conductor
`d` receives exactly `imprimitiveConductorWeight Q d`; hence both ordinary
imprimitive multiplicity and the `q/φ(q)` weight are visible. -/
theorem weighted_sum_nonprincipal_by_conductor
    (Q : ℕ) (F : (d : ℕ) → PrimitiveCharacter d → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ nonprincipalCharacters q,
            F χ.conductor (conductorPrimitiveCharacter χ)) =
      ∑ d ∈ Finset.Icc 2 Q,
        imprimitiveConductorWeight Q d * ∑ ψ : PrimitiveCharacter d, F d ψ := by
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ d ∈ nonprincipalConductors q,
            ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_nonprincipal_by_conductor (Finset.mem_Icc.mp hq).1 F]
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 2 Q,
        if d ∣ q then ((q : ℝ) / (q.totient : ℝ)) *
          ∑ ψ : PrimitiveCharacter d, F d ψ else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      rw [← Finset.sum_filter]
      apply Finset.sum_subset
      · intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hddiv : d ∣ q := (Nat.mem_divisors.mp hd'.1).1
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hd'.2, (Nat.le_of_dvd (Finset.mem_Icc.mp hq).1 hddiv).trans
          (Finset.mem_Icc.mp hq).2⟩, hddiv⟩
      · intro d hdQ hdnot
        simp only [Finset.mem_filter] at hdQ
        exfalso
        apply hdnot
        rw [nonprincipalConductors, Finset.mem_filter]
        exact ⟨Nat.mem_divisors.mpr ⟨hdQ.2,
            Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩,
          (Finset.mem_Icc.mp hdQ.1).1⟩
    _ = ∑ d ∈ Finset.Icc 2 Q, ∑ q ∈ Finset.Icc 1 Q,
        if d ∣ q then ((q : ℝ) / (q.totient : ℝ)) *
          ∑ ψ : PrimitiveCharacter d, F d ψ else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [imprimitiveConductorWeight, Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hdq : d ∣ q <;> simp [hdq]

/-- The requested all-character nonprincipal maximal ledger.  Its first term is
then exactly regrouped by the preceding theorem, while the second is the honest
bad-prime correction; no principal estimate is inserted. -/
theorem weighted_allCharacter_nonprincipal_prefix_ledger
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ nonprincipalCharacters q, characterPrefixMaxSquare χ b M N) ≤
      2 * (∑ d ∈ Finset.Icc 2 Q,
        imprimitiveConductorWeight Q d *
          ∑ ψ : PrimitiveCharacter d,
            primitiveCharacterPrefixMaxSquare b M N d ψ) +
      8 * (N : ℝ) *
        ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ nonprincipalCharacters q,
              ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2 := by
  have hgroup := weighted_sum_nonprincipal_by_conductor Q
    (fun d ψ => primitiveCharacterPrefixMaxSquare b M N d ψ)
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ nonprincipalCharacters q,
          2 * (primitiveCharacterPrefixMaxSquare b M N χ.conductor
              (conductorPrimitiveCharacter χ) +
            conductorErrorPrefixMaxSquare χ b M N) := by
      gcongr with q hq χ hχ
      exact characterPrefixMaxSquare_le_conductor_add_error χ b M N
    _ = 2 * (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ nonprincipalCharacters q,
            primitiveCharacterPrefixMaxSquare b M N χ.conductor
              (conductorPrimitiveCharacter χ)) +
        2 * (∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ nonprincipalCharacters q,
              conductorErrorPrefixMaxSquare χ b M N) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    _ ≤ 2 * (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ nonprincipalCharacters q,
            primitiveCharacterPrefixMaxSquare b M N χ.conductor
              (conductorPrimitiveCharacter χ)) +
        8 * (N : ℝ) *
          ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ nonprincipalCharacters q,
                ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2 := by
      have herr :
          (∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ nonprincipalCharacters q,
                conductorErrorPrefixMaxSquare χ b M N) ≤
            4 * (N : ℝ) *
              ∑ q ∈ Finset.Icc 1 Q,
                ((q : ℝ) / (q.totient : ℝ)) *
                  ∑ χ ∈ nonprincipalCharacters q,
                    ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2 := by
        calc
          _ ≤ ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (q.totient : ℝ)) *
                ∑ χ ∈ nonprincipalCharacters q,
                  (4 * (N : ℝ) *
                    ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2) := by
              apply Finset.sum_le_sum
              intro q hq
              apply mul_le_mul_of_nonneg_left
              · exact Finset.sum_le_sum fun χ _ =>
                  conductorErrorPrefixMaxSquare_le_badSupport χ b M N
              · positivity
          _ = _ := by
              simp only [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro χ hχ
              apply Finset.sum_congr rfl
              intro n hn
              ring
      calc
        _ ≤ 2 * (∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ nonprincipalCharacters q,
                primitiveCharacterPrefixMaxSquare b M N χ.conductor
                  (conductorPrimitiveCharacter χ)) +
            2 * (4 * (N : ℝ) *
              ∑ q ∈ Finset.Icc 1 Q,
                ((q : ℝ) / (q.totient : ℝ)) *
                  ∑ χ ∈ nonprincipalCharacters q,
                    ∑ n ∈ conductorBadSupport q M N, ‖b n‖ ^ 2) := by
              gcongr
        _ = _ := by ring
    _ = _ := by rw [hgroup]

/-- Principal/nonprincipal split with the principal maximal term kept literally.
This theorem is bookkeeping only, not a PNT assertion. -/
theorem weighted_allCharacter_prefix_eq_principal_add_nonprincipal
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : DirichletCharacter ℂ q, characterPrefixMaxSquare χ b M N) =
      (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          characterPrefixMaxSquare (1 : DirichletCharacter ℂ q) b M N) +
      ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ nonprincipalCharacters q, characterPrefixMaxSquare χ b M N := by
  simp_rw [sum_allCharacters_eq_principal_add_nonprincipal, mul_add]
  exact Finset.sum_add_distrib

end

end AnalyticNumberTheory.LargeSieve
