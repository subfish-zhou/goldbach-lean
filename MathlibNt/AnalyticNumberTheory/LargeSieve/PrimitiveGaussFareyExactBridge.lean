

import MathlibNt.AnalyticNumberTheory.LargeSieve.ReducedFareyGauss
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
 # Exact primitive Gauss-to-Farey square-ledger bridge

This module deliberately stops before enlarging primitive characters to all
characters.  It records the exact Gauss expansion of each primitive character
interval sum, keeps both the Gauss factor and the reciprocal-totient weight,
and isolates the one finite numerical estimate needed before the additive
Farey large sieve can be applied.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- The interval sum in the primitive-character square ledger. -/
def primitiveIntervalAmplitude {q : ℕ} (b : ℤ → ℂ) (M : ℤ) (N : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q)

/-- The additive amplitude at the canonical reduced frequency `a/q`. -/
def reducedAdditiveAmplitude (q : ℕ) (b : ℤ → ℂ) (M : ℤ) (N a : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N),
    (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n

/-- The coherent reduced-frequency Gauss expansion belonging to one primitive
character.  The character coefficient remains inside the norm. -/
def primitiveReducedGaussAmplitude {q : ℕ} (b : ℤ → ℂ) (M : ℤ) (N : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ a ∈ reducedResidues q,
    χ.1⁻¹ (a : ZMod q) * reducedAdditiveAmplitude q b M N a

/-- Exact primitive Gauss inversion, with no sum over all characters. -/
theorem primitiveIntervalAmplitude_gauss_exact {q : ℕ} [NeZero q]
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) (χ : PrimitiveCharacter q) :
    gaussSum χ.1⁻¹ (primitiveGaussAddChar q) *
        primitiveIntervalAmplitude b M N χ =
      primitiveReducedGaussAmplitude b M N χ := by
  let χi : PrimitiveCharacter q :=
    ⟨χ.1⁻¹, by
      change χ.1⁻¹.conductor = q
      rw [DirichletCharacter.conductor_inv]
      exact χ.2⟩
  calc
    gaussSum χ.1⁻¹ (primitiveGaussAddChar q) *
        primitiveIntervalAmplitude b M N χ =
      ∑ n ∈ Finset.Icc (M + 1) (M + N),
        b n * (χi.1⁻¹ (n : ZMod q) *
          gaussSum χi.1 (primitiveGaussAddChar q)) := by
            rw [primitiveIntervalAmplitude, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            simp [χi]
            ring
    _ = ∑ n ∈ Finset.Icc (M + 1) (M + N), b n *
          (∑ a ∈ reducedResidues q,
            χi.1 (a : ZMod q) *
              charReal ((n : ℝ) * (a : ℝ) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [sum_reducedResidues_eq_invChar_mul_gaussSum χi n]
    _ = ∑ n ∈ Finset.Icc (M + 1) (M + N),
          ∑ a ∈ reducedResidues q,
            b n * (χi.1 (a : ZMod q) *
              charReal ((n : ℝ) * (a : ℝ) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
    _ = primitiveReducedGaussAmplitude b M N χ := by
            rw [primitiveReducedGaussAmplitude, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a ha
            rw [reducedAdditiveAmplitude, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            simp [χi]
            ring

/-- Exact square-ledger identity retaining the Gauss factors and the
`1 / φ(q)` weight.  This is the strongest unconditional bridge supplied by the
current primitive Gauss/Farey API without introducing all characters. -/
theorem primitiveGaussSquareLedger_exact {q : ℕ} [NeZero q]
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖gaussSum χ.1⁻¹ (primitiveGaussAddChar q) *
            primitiveIntervalAmplitude b M N χ‖ ^ 2 =
      (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveReducedGaussAmplitude b M N χ‖ ^ 2 := by
  congr 1
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [primitiveIntervalAmplitude_gauss_exact]

/-- Equivalent AP-normalized form of the exact ledger.  The equality uses only
`|τ(χ⁻¹)|² = q`; no character-family enlargement occurs. -/
theorem weightedPrimitiveSquareLedger_eq_reducedGauss {q : ℕ} [NeZero q]
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveIntervalAmplitude b M N χ‖ ^ 2 =
      (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveReducedGaussAmplitude b M N χ‖ ^ 2 := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  calc
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveIntervalAmplitude b M N χ‖ ^ 2 =
      (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖gaussSum χ.1⁻¹ (primitiveGaussAddChar q) *
            primitiveIntervalAmplitude b M N χ‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro χ hχ
          have hn := primitive_gaussSum_norm_sq
            (⟨χ.1⁻¹, by
              change χ.1⁻¹.conductor = q
              rw [DirichletCharacter.conductor_inv]
              exact χ.2⟩ : PrimitiveCharacter q)
          rw [norm_mul, mul_pow]
          rw [hn]
          field_simp
    _ = _ := primitiveGaussSquareLedger_exact b M N

/-- The direct primitive Bessel statement.  Its coefficient cancels the retained
`1 / φ(q)` weight and exposes the unweighted reduced additive energy. -/
def PrimitiveReducedBesselDirect (q : ℕ) [NeZero q] : Prop :=
  ∀ c : ℕ → ℂ,
    (∑ χ : PrimitiveCharacter q,
        ‖∑ a ∈ reducedResidues q, c a * χ.1⁻¹ (a : ZMod q)‖ ^ 2) ≤
      (q.totient : ℝ) * ∑ a ∈ reducedResidues q, ‖c a‖ ^ 2

/-- A primitive character, normalized in the finite `L²(ZMod q)` space. -/
private def normalizedPrimitiveCharacterVector {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) : EuclideanSpace ℂ (ZMod q) :=
  WithLp.toLp 2 (fun a => ((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) * χ.1 a)

private lemma primitiveCharacter_raw_inner {q : ℕ} [NeZero q]
    (χ ψ : PrimitiveCharacter q) :
    (∑ a : ZMod q, inner ℂ (χ.1 a) (ψ.1 a)) =
      if χ = ψ then (q.totient : ℂ) else 0 := by
  rw [show (∑ a : ZMod q, inner ℂ (χ.1 a) (ψ.1 a)) =
      ∑ a : ZMod q, (ψ.1 * χ.1⁻¹) a by
    apply Finset.sum_congr rfl
    intro a ha
    rw [RCLike.inner_apply]
    change ψ.1 a * star (χ.1 a) = _
    rw [MulChar.star_apply', MulChar.mul_apply]]
  split_ifs with h
  · subst ψ
    simp [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · have hne : ψ.1 * χ.1⁻¹ ≠ 1 := by
      intro hp
      apply h
      exact Subtype.ext (mul_inv_eq_one.mp hp).symm
    exact MulChar.sum_eq_zero_of_ne_one hne

/-- Primitive characters are an orthonormal subfamily after the standard
`φ(q)⁻¹/²` normalization.  This is proved directly on the finite unit support;
no character ledger is enlarged. -/
private lemma normalizedPrimitiveCharacterVector_orthonormal
    {q : ℕ} [NeZero q] :
    Orthonormal ℂ (normalizedPrimitiveCharacterVector (q := q)) := by
  rw [orthonormal_iff_ite]
  intro χ ψ
  calc
    inner ℂ (normalizedPrimitiveCharacterVector χ)
        (normalizedPrimitiveCharacterVector ψ) =
        ((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) ^ 2 *
          ∑ a : ZMod q, inner ℂ (χ.1 a) (ψ.1 a) := by
      rw [PiLp.inner_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [normalizedPrimitiveCharacterVector, WithLp.ofLp_toLp,
        RCLike.inner_apply]
      rw [map_mul (starRingEnd ℂ)]
      rw [show (starRingEnd ℂ) ((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) =
          ((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) by simp]
      ring
    _ = if χ = ψ then 1 else 0 := by
      rw [primitiveCharacter_raw_inner χ ψ]
      split_ifs with h
      · have hφ : (0 : ℝ) < (q.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
        rw [inv_pow]
        have hs : ((Real.sqrt (q.totient : ℝ) : ℂ) ^ 2) =
            (q.totient : ℂ) := by
          norm_cast
          exact Real.sq_sqrt (le_of_lt hφ)
        rw [hs]
        field_simp [show (q.totient : ℂ) ≠ 0 by exact_mod_cast
          (Nat.totient_pos.mpr (NeZero.pos q)).ne']
      · simp

/-- Coefficients on canonical reduced residues, extended by zero off the unit
support of `ZMod q`. -/
private def reducedCoefficientVector {q : ℕ} (c : ℕ → ℂ) :
    EuclideanSpace ℂ (ZMod q) :=
  WithLp.toLp 2 (fun a => if IsUnit a then c a.val else 0)

private lemma inner_normalizedPrimitiveCharacter_reducedCoefficient
    {q : ℕ} [NeZero q] (c : ℕ → ℂ) (χ : PrimitiveCharacter q) :
    inner ℂ (normalizedPrimitiveCharacterVector χ) (reducedCoefficientVector c) =
      ((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) *
        ∑ a ∈ reducedResidues q, c a * χ.1⁻¹ (a : ZMod q) := by
  rw [PiLp.inner_apply]
  rw [show (∑ a : ZMod q,
      inner ℂ (normalizedPrimitiveCharacterVector χ a) (reducedCoefficientVector c a)) =
      ((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) *
        ∑ a : ZMod q, (if IsUnit a then c a.val else 0) * χ.1⁻¹ a by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [normalizedPrimitiveCharacterVector, reducedCoefficientVector,
      WithLp.ofLp_toLp, RCLike.inner_apply]
    rw [map_mul (starRingEnd ℂ),
      show (starRingEnd ℂ) ((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) =
        ((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) by simp,
      show (starRingEnd ℂ) (χ.1 a) = χ.1⁻¹ a by
        change star (χ.1 a) = χ.1⁻¹ a
        exact MulChar.star_apply' χ.1 a]
    ring]
  rw [sum_zmod_eq_sum_range]
  rw [reducedResidues, Finset.sum_filter]
  apply congrArg
  apply Finset.sum_congr rfl
  intro a ha
  have haval : (a : ZMod q).val = a := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
  simp only [haval, ZMod.isUnit_iff_coprime, ite_mul, zero_mul]

private lemma reducedCoefficientVector_norm_sq {q : ℕ} [NeZero q]
    (c : ℕ → ℂ) :
    ‖reducedCoefficientVector (q := q) c‖ ^ 2 =
      ∑ a ∈ reducedResidues q, ‖c a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, sum_zmod_eq_sum_range]
  rw [reducedResidues, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have haval : (a : ZMod q).val = a := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
  simp only [reducedCoefficientVector, WithLp.ofLp_toLp, haval,
    ZMod.isUnit_iff_coprime]
  split_ifs <;> simp

/-- Direct finite-dimensional Bessel inequality for the primitive-character
orthonormal subfamily.  The proof never compares the primitive ledger with an
all-character energy. -/
theorem primitiveReducedBesselDirect (q : ℕ) [NeZero q] :
    PrimitiveReducedBesselDirect q := by
  intro c
  have hB :=
    (normalizedPrimitiveCharacterVector_orthonormal (q := q)).sum_inner_products_le
      (reducedCoefficientVector (q := q) c) (s := Finset.univ)
  rw [reducedCoefficientVector_norm_sq] at hB
  simp_rw [inner_normalizedPrimitiveCharacter_reducedCoefficient] at hB
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hsqrt : (0 : ℝ) < Real.sqrt (q.totient : ℝ) := Real.sqrt_pos.2 hφ
  have hscale : ∀ z : ℂ,
      ‖((Real.sqrt (q.totient : ℝ) : ℂ)⁻¹) * z‖ ^ 2 =
        (1 / (q.totient : ℝ)) * ‖z‖ ^ 2 := by
    intro z
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt,
      mul_pow, inv_pow, Real.sq_sqrt (le_of_lt hφ)]
    field_simp
  simp_rw [hscale, ← Finset.mul_sum] at hB
  have hmul := mul_le_mul_of_nonneg_left hB (le_of_lt hφ)
  calc
    _ = (q.totient : ℝ) *
        ((1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖∑ a ∈ reducedResidues q, c a * χ.1⁻¹ (a : ZMod q)‖ ^ 2) := by
      field_simp
    _ ≤ _ := hmul

/-- Once the direct primitive Bessel estimate is supplied, the exact ledger
reduces to the unweighted reduced additive energy.  This consumer itself never
introduces all characters. -/
theorem weightedPrimitiveSquareLedger_le_reducedAdditive_of_directBessel
    {q : ℕ} [NeZero q] (hB : PrimitiveReducedBesselDirect q)
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveIntervalAmplitude b M N χ‖ ^ 2 ≤
      ∑ a ∈ reducedResidues q, ‖reducedAdditiveAmplitude q b M N a‖ ^ 2 := by
  rw [weightedPrimitiveSquareLedger_eq_reducedGauss]
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  -- Bessel writes the coefficient first; the Gauss amplitude writes it second.
  have hgauss :
      (∑ χ : PrimitiveCharacter q, ‖primitiveReducedGaussAmplitude b M N χ‖ ^ 2) ≤
        (q.totient : ℝ) *
          ∑ a ∈ reducedResidues q, ‖reducedAdditiveAmplitude q b M N a‖ ^ 2 := by
    simpa only [primitiveReducedGaussAmplitude, mul_comm] using
      hB (reducedAdditiveAmplitude q b M N)
  calc
    _ ≤ (1 / (q.totient : ℝ)) *
        ((q.totient : ℝ) *
          ∑ a ∈ reducedResidues q, ‖reducedAdditiveAmplitude q b M N a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hgauss (by positivity)
    _ = _ := by field_simp

/-- Reindex the complete reduced additive energy by the multiplicity-free Farey
index.  This is an equality, not a relaxation to unreduced representatives. -/
theorem reducedAdditiveEnergy_reindex_exact (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ reducedResidues q,
        ‖reducedAdditiveAmplitude q b M N a‖ ^ 2) =
      ∑ qa ∈ reducedFareyIndices Q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) * b n‖ ^ 2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => (x.1, x.2)) ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with ⟨q, a⟩
    simp only [Finset.mem_sigma] at hx
    rw [mem_reducedFareyIndices]
    rcases Finset.mem_Icc.mp hx.1 with ⟨hq1, hqQ⟩
    rcases mem_reducedResidues.mp hx.2 with ⟨haq, hcop⟩
    exact ⟨hq1, hqQ, haq, hcop⟩
  · intro x hx y hy hxy
    rcases x with ⟨q, a⟩
    rcases y with ⟨r, c⟩
    cases hxy
    rfl
  · intro qa hqa
    rcases qa with ⟨q, a⟩
    rw [mem_reducedFareyIndices] at hqa
    refine ⟨⟨q, a⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr ⟨hqa.1, hqa.2.1⟩,
      mem_reducedResidues.mpr ⟨hqa.2.2.1, hqa.2.2.2⟩⟩
  · intro x hx
    rcases x with ⟨q, a⟩
    congr 2
    apply Finset.sum_congr rfl
    intro n hn
    congr 2
    dsimp [reducedFareyPoint]
    ring

/-- End-to-end additive large-sieve consumer parameterized by a direct primitive
Bessel estimate, retained as a reusable compatibility theorem. -/
theorem weightedPrimitiveSquareLedger_largeSieve_of_directBessel
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) (hQ : 0 < Q)
    (hB : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q),
      @PrimitiveReducedBesselDirect q
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveIntervalAmplitude b M N χ‖ ^ 2) ≤
      largeSieveBound N (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ reducedResidues q,
        ‖reducedAdditiveAmplitude q b M N a‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      let : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      exact weightedPrimitiveSquareLedger_le_reducedAdditive_of_directBessel
        (hB q hq) b M N
    _ = ∑ qa ∈ reducedFareyIndices Q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) * b n‖ ^ 2 :=
      reducedAdditiveEnergy_reindex_exact b M N Q
    _ ≤ _ := largeSieveReducedFareyIndices M N Q hQ b

/-- Unconditional primitive square-ledger large sieve.  Primitive characters
are handled as an orthonormal subfamily on the finite unit support, without
enlarging the original ledger to all-character energy. -/
theorem weightedPrimitiveSquareLedger_largeSieve
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveIntervalAmplitude b M N χ‖ ^ 2) ≤
      largeSieveBound N (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  apply weightedPrimitiveSquareLedger_largeSieve_of_directBessel b M N Q hQ
  intro q hq
  let _ : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
  exact primitiveReducedBesselDirect q

/-- The exact factor delivered by the current production reduced-Farey theorem
on a conductor cell `(R,2R]` and an interval of length `L`.

This name is intentionally transparent.  With the present well-spaced additive
large-sieve API it unfolds to
`L + (2 * ⌈log (4R²) / log 2⌉₊ + 12) * 4R²`; in particular no downstream
consumer may silently replace it by the sharper classical factor `L + 4R²`. -/
def primitiveGaussFareyCellFactor (R L : ℕ) : ℝ :=
  largeSieveBound L (1 / ((2 * R : ℕ) : ℝ) ^ 2)

/-- Cell-local primitive Gauss--Farey large sieve.  Restricting from all
`q ≤ 2R` to the literal cell `(R,2R]` costs nothing because every summand is
nonnegative. -/
theorem weightedPrimitiveSquareLedger_cell_largeSieve
    (b : ℤ → ℂ) (M : ℤ) (L R : ℕ) (hR : 0 < R) :
    (∑ q ∈ Finset.Ioc R (2 * R),
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveIntervalAmplitude b M L χ‖ ^ 2) ≤
      primitiveGaussFareyCellFactor R L *
        ∑ n ∈ Finset.Icc (M + 1) (M + L), ‖b n‖ ^ 2 := by
  have hsub : Finset.Ioc R (2 * R) ⊆ Finset.Icc 1 (2 * R) := by
    intro q hq
    have hq' := Finset.mem_Ioc.mp hq
    exact Finset.mem_Icc.mpr ⟨by omega, hq'.2⟩
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 (2 * R),
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖primitiveIntervalAmplitude b M L χ‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q hq hnot
      positivity
    _ ≤ primitiveGaussFareyCellFactor R L *
        ∑ n ∈ Finset.Icc (M + 1) (M + L), ‖b n‖ ^ 2 := by
      exact weightedPrimitiveSquareLedger_largeSieve b M L (2 * R) (by omega)

/-- One dyadic layer of a primitive prefix decomposition on `(R,2R]`.  The
coefficient function may depend on the aligned interval `j`; this lets lane
consumers insert their *actual grouped coefficient* rather than an atomwise
triangle majorant. -/
def primitiveGaussFareyDyadicLayerLedger
    (b : ℕ → ℤ → ℂ) (N R k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    ∑ q ∈ Finset.Ioc R (2 * R),
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖primitiveIntervalAmplitude (b j) ((j * 2 ^ k : ℕ) : ℤ)
            (2 ^ k) χ‖ ^ 2

/-- The real coefficient energy of the aligned intervals at level `k`.  There
is no factor `N+1`: a lane with one global coefficient sequence proves its
intervals disjoint and bounds this exact sum by the global grouped energy. -/
def primitiveGaussFareyDyadicLayerCoefficientEnergy
    (b : ℕ → ℤ → ℂ) (N k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    ∑ n ∈ Finset.Icc (((j * 2 ^ k : ℕ) : ℤ) + 1)
        (((j * 2 ^ k : ℕ) : ℤ) + (2 ^ k : ℕ)), ‖b j n‖ ^ 2

/-- Unconditional cell payment for one dyadic layer.  This is the exact
Gauss--Farey factor times the true coefficient energy, summed over `j` before
any estimate is made. -/
theorem primitiveGaussFareyDyadicLayerLedger_le
    (b : ℕ → ℤ → ℂ) (N R k : ℕ) (hR : 0 < R) :
    primitiveGaussFareyDyadicLayerLedger b N R k ≤
      primitiveGaussFareyCellFactor R (2 ^ k) *
        primitiveGaussFareyDyadicLayerCoefficientEnergy b N k := by
  unfold primitiveGaussFareyDyadicLayerLedger
    primitiveGaussFareyDyadicLayerCoefficientEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact weightedPrimitiveSquareLedger_cell_largeSieve
    (b j) ((j * 2 ^ k : ℕ) : ℤ) (2 ^ k) R hR

/-- Medium-long dyadic layers are exactly `R < 2^k ≤ R²`. -/
def primitiveGaussFareyMediumLongLayers (N R : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log2 N + 1)).filter fun k => R < 2 ^ k ∧ 2 ^ k ≤ R ^ 2

/-- Medium-long payment with the single external Rademacher--Menshov factor
visible.  The right side retains the exact layer length and the true `j`-summed
coefficient energy; hence it is the faithful scale to use when deciding whether
a half-budget closes. -/
theorem primitiveGaussFareyMediumLongLedger_le
    (b : ℕ → ℕ → ℤ → ℂ) (N R : ℕ) (hR : 0 < R) :
    ((Nat.log2 N + 1 : ℕ) : ℝ) *
        ∑ k ∈ primitiveGaussFareyMediumLongLayers N R,
          primitiveGaussFareyDyadicLayerLedger (b k) N R k ≤
      ((Nat.log2 N + 1 : ℕ) : ℝ) *
        ∑ k ∈ primitiveGaussFareyMediumLongLayers N R,
          primitiveGaussFareyCellFactor R (2 ^ k) *
            primitiveGaussFareyDyadicLayerCoefficientEnergy (b k) N k := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun k hk =>
    primitiveGaussFareyDyadicLayerLedger_le (b k) N R k hR

/-- The layers still requiring a primitive analytic source after the
medium-long Gauss--Farey payment: precisely `R² < 2^k`. -/
def primitiveGaussFareyUltraLongLayers (N R : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log2 N + 1)).filter fun k => R ^ 2 < 2 ^ k

end

end AnalyticNumberTheory.LargeSieve
