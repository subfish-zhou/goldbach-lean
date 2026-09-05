import MathlibNt.SieveTheory.Liu.LogarithmicIntegral.LiuTrueLiPan
import MathlibNt.SieveTheory.Arithmetic.LiuLogarithmicIntegral

/-!
! # MathlibNt.SieveTheory.BombieriVinogradov

The Bombieri--Vinogradov theorem is an analytic literature input in this
development.  This file deliberately states only its standard uniform
average form: it does not manufacture parameter-dependent constants, and its
main term is a genuine logarithmic integral rather than the proxy `x / log x`.

For references see Bombieri, *On the large sieve* (1965), Vinogradov (1965),
or Halberstam--Richert, *Sieve Methods*, Chapter 9.
-/

namespace MathlibNt.SieveTheory.BombieriVinogradov

open Real Finset Filter
open scoped Classical BigOperators

/-- A normalized genuine logarithmic integral:
`2 / log 2 + ∫ t in 2..x, 1 / log t`.  Thus it differs from the literal
integral from `2` to `x` by the fixed additive constant `2 / log 2`; the two
normalizations are asymptotically interchangeable.  This normalization is
chosen so that it dominates `x / log x` for `x ≥ 2`. -/
noncomputable def trueLogarithmicIntegral (x : ℝ) : ℝ :=
  LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) x

/-- The usual prime count through the integer endpoint `x` in the residue
class `l` modulo `q`. -/
def primesInAP (x q l : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card

/-- The ordinary prime-AP error centered at the genuine logarithmic integral. -/
noncomputable def standardPrimeAPError (x q l : ℕ) : ℝ :=
  (primesInAP x q l : ℝ) - trueLogarithmicIntegral x / Nat.totient q

/-- The maximum standard AP error over canonical reduced residues.  It is
defined as `0` for the empty modulus-zero residue set; modulo `1` its unique
canonical reduced residue is `0`. -/
noncomputable def standardPrimeAPMaxError (x q : ℕ) : ℝ :=
  let S := AnalyticNumberTheory.Sieve.unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |standardPrimeAPError x q l|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

theorem standardPrimeAPMaxError_zero (x : ℕ) :
    standardPrimeAPMaxError x 0 = 0 := by
  simp [standardPrimeAPMaxError, AnalyticNumberTheory.Sieve.unitResidues]

theorem standardPrimeAPMaxError_one (x : ℕ) :
    standardPrimeAPMaxError x 1 = |standardPrimeAPError x 1 0| := by
  simp [standardPrimeAPMaxError, AnalyticNumberTheory.Sieve.unitResidues]

/-- A reduced residue is bounded by the corresponding canonical maximum. -/
theorem abs_standardPrimeAPError_le_max {x q l : ℕ}
    (hl : l ∈ AnalyticNumberTheory.Sieve.unitResidues q) :
    |standardPrimeAPError x q l| ≤ standardPrimeAPMaxError x q := by
  unfold standardPrimeAPMaxError
  dsimp only
  have hS : (AnalyticNumberTheory.Sieve.unitResidues q).Nonempty := ⟨l, hl⟩
  rw [dif_pos hS]
  exact Finset.le_max' ((AnalyticNumberTheory.Sieve.unitResidues q).image
    (fun l => |standardPrimeAPError x q l|)) _
    (Finset.mem_image.mpr ⟨l, hl, rfl⟩)

/-- The prefix maximum occurring in the standard Bombieri--Vinogradov theorem:
first maximize over reduced residues, then over every integer endpoint `y ≤ x`.
The finite set is always nonempty because it contains `y = 0`. -/
noncomputable def standardPrimeAPPrefixMaxError (x q : ℕ) : ℝ :=
  ((range (x + 1)).image (fun y => standardPrimeAPMaxError y q)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The endpoint error is one of the terms in the standard prefix maximum. -/
theorem standardPrimeAPMaxError_le_prefixMaxError (x q : ℕ) :
    standardPrimeAPMaxError x q ≤ standardPrimeAPPrefixMaxError x q := by
  unfold standardPrimeAPPrefixMaxError
  exact Finset.le_max'
    ((range (x + 1)).image (fun y => standardPrimeAPMaxError y q)) _
    (Finset.mem_image.mpr ⟨x, by simp, rfl⟩)

/-- The canonical maximal AP error is nonnegative at every modulus, including
the explicitly defined zero endpoint. -/
theorem standardPrimeAPMaxError_nonneg (x q : ℕ) :
    0 ≤ standardPrimeAPMaxError x q := by
  unfold standardPrimeAPMaxError
  dsimp only
  by_cases hS : (AnalyticNumberTheory.Sieve.unitResidues q).Nonempty
  · rw [dif_pos hS]
    let M := (AnalyticNumberTheory.Sieve.unitResidues q).image
      (fun l => |standardPrimeAPError x q l|)
    have hmem : M.max' (Finset.image_nonempty.mpr hS) ∈ M :=
      Finset.max'_mem M _
    rcases Finset.mem_image.mp hmem with ⟨l, _, hl⟩
    rw [← hl]
    exact abs_nonneg _
  · rw [dif_neg hS]

/-- The prefix maximum is nonnegative, since every endpoint maximum is. -/
theorem standardPrimeAPPrefixMaxError_nonneg (x q : ℕ) :
    0 ≤ standardPrimeAPPrefixMaxError x q :=
  (standardPrimeAPMaxError_nonneg x q).trans
    (standardPrimeAPMaxError_le_prefixMaxError x q)

/-- Summing the endpoint errors over any finite modulus set is bounded by the
sum of the standard prefix-maximal errors over the same set. -/
theorem sum_standardPrimeAPMaxError_le_prefixMaxError
    (x : ℕ) (S : Finset ℕ) :
    (∑ q ∈ S, standardPrimeAPMaxError x q) ≤
      ∑ q ∈ S, standardPrimeAPPrefixMaxError x q := by
  exact Finset.sum_le_sum fun q _ => standardPrimeAPMaxError_le_prefixMaxError x q

/-- Replacing a residue by its canonical representative does not change the
standard prime-AP count. -/
theorem primesInAP_modEq_N_eq (N d : ℕ) :
    primesInAP N d (N % d) =
      ((Finset.range (N + 1)).filter
        (fun p => p.Prime ∧ p ≡ N [MOD d])).card := by
  unfold primesInAP
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hRange, hp, hmod⟩
    refine ⟨hRange, hp, ?_⟩
    rw [Nat.ModEq] at hmod ⊢
    simpa [Nat.mod_mod] using hmod
  · rintro ⟨hRange, hp, hmod⟩
    refine ⟨hRange, hp, ?_⟩
    rw [Nat.ModEq] at hmod ⊢
    simpa [Nat.mod_mod] using hmod

/-- The genuine logarithmic integral dominates the historical elementary
proxy. -/
theorem div_log_le_trueLogarithmicIntegral {x : ℝ} (hx : 2 ≤ x) :
    x / Real.log x ≤ trueLogarithmicIntegral x :=
  LiuWeight.div_log_le_liuLogarithmicIntegral hx

/-- **Standard Bombieri--Vinogradov literature interface.**

For every `A > 0`, a nonnegative logarithmic loss exponent `B` and a positive
constant `C` work uniformly for all sufficiently large endpoints.  For every
modulus this uses the standard nested maxima `max_{y ≤ N} max_{(l,q)=1}`; in
particular it is not the weaker fixed-endpoint assertion.  The sum is over the
genuine moduli `1 ≤ q ≤ floor(N^(1/2) / log(N)^B)` with no reduction of the
classical modulus range.  The finite conventions at `q = 0` and `q = 1` are
explicit above, but `q = 0` is not included in this theorem. -/
def StandardBombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, 2 ≤ N →
        ∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N B),
          standardPrimeAPPrefixMaxError N q ≤
            C * (N : ℝ) / Real.log N ^ A

/-- The fixed-endpoint estimate used by the lower-sieve consumer is a direct
finite consequence of the standard prefix-maximal theorem.  This theorem keeps
the producer interface standard while allowing endpoint-only consumers to use
exactly the bound they need. -/
theorem endpoint_bound (hBV : StandardBombieriVinogradov) :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
        ∀ᶠ N : ℕ in atTop, 2 ≤ N →
          ∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N B),
            standardPrimeAPMaxError N q ≤
              C * (N : ℝ) / Real.log N ^ A := by
  intro A hA
  rcases hBV A hA with ⟨B, hB, C, hC, hprefix⟩
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [hprefix] with N hN
  intro hN₂
  exact (sum_standardPrimeAPMaxError_le_prefixMaxError N _).trans (hN hN₂)

end MathlibNt.SieveTheory.BombieriVinogradov
