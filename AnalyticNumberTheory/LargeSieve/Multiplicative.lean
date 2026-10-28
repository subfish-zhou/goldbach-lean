import AnalyticNumberTheory.LargeSieve.WellSpaced
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # AnalyticNumberTheory.LargeSieve.Multiplicative

## Multiplicative large sieve

The multiplicative step in the Pan mean-value argument
starts from the additive large sieve (`LargeSieve/WellSpaced.lean`)
and uses Dirichlet-character orthogonality and finite Fourier Parseval
to obtain:

  * The additive large sieve on the rational point set
    `X_Q = {r/q : 1 ≤ q ≤ Q, 0 ≤ r < q}` (the Farey fractions after
    removing duplicates):
    `Σ_{x∈X_Q} |Σ_n a_n·e(nx)|² ≤ C(N, 1/Q²)·Σ_n |a_n|²`
    (`largeSieveRationalPoints`).
  * The character large-sieve inequality for each modulus `q`:
    `(q/φ(q))·Σ_{χ mod q} |Σ_n a_n·χ(n)|² ≤ Σ_{r<q} |Σ_n a_n·e(nr/q)|²`
    (`characterSieveModulus_le`).

Proof structure (Montgomery's classical route):

1. **Character orthogonality**: summing over all characters modulo `q`,
   `Σ_χ |S(χ)|² = φ(q)·Σ_{(a,q)=1} |Σ_{n≡a (q)} a_n|²`.
   Use mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`;
   `χ(n) = 0` for `(n,q) > 1` handles the coprimality restriction.
2. **Finite Fourier Parseval**:
   `Σ_{a mod q} |Σ_{n≡a (q)} a_n|² = (1/q)·Σ_{r mod q} |S(r/q)|²`
   (`zmodParseval_inv`/`zmodParseval_character`), using the
   geometric-series kernel `Σ_a e(a(r−s)/q) = q·1_{r=s}`.
3. **Spacing of rational points**: `X_Q` is `1/Q²`-well-spaced, since
   the numerator-denominator difference gives a lower bound
   `≥ 1/(q₁q₂)` (`rationalPoints_wellSpaced`).
4. **Additive large sieve**: apply `largeSievePrimal_wellSpaced` to
   `X_Q` to obtain `largeSieveRationalPoints`, with the weaker additive
   large-sieve constant `C(N, 1/Q²)` (`largeSieveBound`).

**Scope and limitations.** The classical Bombieri--Davenport bound
`Σ_{q≤Q} (q/φ(q))·Σ*_{χ mod q} |S(χ)|² ≤ (Q²+N−1)·Σ_n |a_n|²`
restricts `Σ*` to **primitive characters**. Its derivation needs
(i) primitive-character theory and Gauss sums (`|τ(χ)|² = q`) to write
`(q/φ(q))·|S(χ)|²` as
`(1/φ(q))·|Σ_{(a,q)=1} conj(χ(a))·S(a/q)|²`, and
(ii) an explicit sum over reduced fraction pairs, with a bijection to
the deduplicated `rationalPoints` set. These additional steps belong to
`BombieriDavenport.lean`, not to the per-modulus argument here.

One cannot simply sum the Parseval bounds over **all** characters or over
the point multiset `Σ_{q≤Q} Σ_{r<q} |S(r/q)|²`.
For example, with `a_n ≡ 1`, `Q = 2`, and sufficiently large `N`,
`Σ_q (q/φ(q))Σ_χ |S(χ)|² ≈ 3N²/2`, whereas
`C(N,1/4)·N = (N+64)·N`. The primitive-character restriction is therefore
essential. The constant `C(N,δ)` comes from the additive estimate; the sharp
`N + δ⁻¹` bound is not supplied by this argument.

References: Montgomery, "Topics in Multiplicative Number Theory" (1971), Ch. 1;
Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7;
Kedlaya, "Notes on Analytic Number Theory", Ch. 16 (Bombieri--Davenport).
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-! ## 1. Complex roots of unity and conjugation of character values -/

/-- `ℂ` has enough `n`th roots of unity for `n ≠ 0`: `exp(2πi/n)` is
primitive and the group of roots of unity is cyclic. This supplies the
complex instance needed by the `DirichletCharacter` orthogonality theorem,
in addition to mathlib's instances for `Circle` and algebraic closures. -/
theorem complexHasEnoughRootsOfUnity (n : ℕ) (hn : n ≠ 0) :
    HasEnoughRootsOfUnity ℂ n := by
  classical
  have : NeZero n := ⟨hn⟩
  refine { prim := ?_, cyc := ?_ }
  · exact ⟨Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)), Complex.isPrimitiveRoot_exp n hn⟩
  · infer_instance

/-- The conjugate of a complex number of norm 1 equals its inverse. -/
theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : star z = z⁻¹ := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hmul : z * star z = 1 := by
    have h := Complex.mul_conj z
    rw [hsq] at h
    simpa using h
  have hne : z ≠ 0 := by
    intro hz0
    have : ‖z‖ = 0 := by simp [hz0]
    linarith
  calc
    star z = 1 * star z := by rw [one_mul]
    _ = (z⁻¹ * z) * star z := by rw [inv_mul_cancel₀ hne]
    _ = z⁻¹ * (z * star z) := by ring
    _ = z⁻¹ := by rw [hmul, mul_one]

/-- Conjugation equals evaluation of the inverse character:
`conj(χ(a)) = χ⁻¹(a)` for a unit `a`. The nonunit case is handled
separately in the orthogonality lemma, where both sides are zero. -/
theorem char_conj_inv {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    star (χ a) = χ⁻¹ a := by
  have hnorm : ‖χ a‖ = 1 := DirichletCharacter.unit_norm_eq_one χ ha.unit
  have hconj : star (χ a) = (χ a)⁻¹ := conj_eq_inv_of_norm_eq_one hnorm
  have hspec : (↑ha.unit : ZMod q) = a := ha.unit_spec
  have hinv : χ⁻¹ a = (χ a)⁻¹ := by
    rw [MulChar.inv_apply]
    have hrinv : Ring.inverse a = (↑ha.unit⁻¹ : ZMod q) := by
      calc
        Ring.inverse a = Ring.inverse (↑ha.unit : ZMod q) := by rw [hspec]
        _ = (↑ha.unit⁻¹ : ZMod q) := Ring.inverse_unit ha.unit
    rw [hrinv]
    -- χ(↑u⁻¹) = (χ ↑u)⁻¹ = (χ a)⁻¹
    have hmul : χ (↑ha.unit : ZMod q) * χ (↑ha.unit⁻¹ : ZMod q) = 1 := by
      rw [← map_mul χ]
      have hunit : (↑ha.unit : ZMod q) * (↑ha.unit⁻¹ : ZMod q) = 1 := by
        exact Units.val_inv ha.unit
      rw [hunit, χ.map_one]
    have hmu : χ (↑ha.unit⁻¹ : ZMod q) = (χ (↑ha.unit : ZMod q))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hmul)
    rwa [hspec] at hmu
  rw [hconj]
  exact hinv.symm

/-! ## 2. Geometric-series kernel and Parseval modulo q -/

/-- `e(x)` is 1 at integers: `e(k) = 1` (`k : ℤ`). -/
theorem charReal_int_eq_one (k : ℤ) : charReal (k : ℝ) = 1 := by
  have hf : Int.fract (k : ℝ) = 0 := by
    rw [Int.fract_eq_iff]
    refine ⟨by norm_num, by norm_num, ⟨k, ?_⟩⟩
    simp
  calc
    charReal (k : ℝ) = charReal (Int.fract (k : ℝ)) := charReal_eq_charReal_fract (k : ℝ)
    _ = charReal 0 := by rw [hf]
    _ = 1 := charReal_zero

/-- Every integer is a period of `e`: `e(x + k) = e(x)` (`k : ℤ`). -/
theorem charReal_periodic_int (x : ℝ) (k : ℤ) : charReal (x + (k : ℝ)) = charReal x := by
  calc
    charReal (x + (k : ℝ)) = charReal (Int.fract (x + (k : ℝ))) := charReal_eq_charReal_fract (x + (k : ℝ))
    _ = charReal (Int.fract x) := by congr 1; rw [Int.fract_add_intCast]
    _ = charReal x := (charReal_eq_charReal_fract x).symm

/-- **Geometric-series kernel modulo q**:
`Σ_{r<q} e(r·k/q) = q·1_{q|k}` for integer `k`. If `q | k`,
each term is 1; otherwise use the geometric-series formula with `e(k) = 1`. -/
theorem geomSum_zmod_charReal {q : ℕ} (hq : 0 < q) (k : ℤ) :
    (∑ r ∈ Finset.range q, charReal ((k : ℝ) * (r : ℝ) / (q : ℝ))) =
      if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  by_cases hk : (q : ℤ) ∣ k
  · -- q | k: write k = q·m, so each term e(r·m) is 1.
    rcases hk with ⟨m, hm⟩
    have hk' : (q : ℤ) ∣ k := ⟨m, hm⟩
    have hsum : (∑ r ∈ Finset.range q, charReal ((k : ℝ) * (r : ℝ) / (q : ℝ))) =
        ∑ r ∈ Finset.range q, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro r hr
      have harg : (k : ℝ) * (r : ℝ) / (q : ℝ) = ((m * r : ℤ) : ℝ) := by
        calc
          (k : ℝ) * (r : ℝ) / (q : ℝ)
              = ((k * (r : ℤ) : ℤ) : ℝ) / (q : ℝ) := by
                norm_num
          _ = (((m * (r : ℤ) : ℤ) * (q : ℤ) : ℤ) : ℝ) / (q : ℝ) := by
                have hint : k * (r : ℤ) = (m * (r : ℤ)) * (q : ℤ) := by
                  rw [hm]
                  ring
                rw [hint]
          _ = ((m * (r : ℤ) : ℤ) : ℝ) := by
                field_simp [hq.ne']
                norm_cast
                ring
          _ = ((m * r : ℤ) : ℝ) := by
                norm_num
      rw [harg, charReal_int_eq_one]
    rw [if_pos hk', hsum]
    simp
  · -- If q does not divide k, the geometric-series numerator is e(k·q/q) - 1 = 0 and the denominator is nonzero.
    have hθ : ¬ ∃ t : ℤ, (t : ℝ) = (k : ℝ) / (q : ℝ) := by
      intro ht
      rcases ht with ⟨t, ht⟩
      apply hk
      refine ⟨t, ?_⟩
      -- (k:ℝ)/(q:ℝ) = t implies k = t·q as integers.
      have hkmul : (k : ℝ) = (t : ℝ) * (q : ℝ) := by
        calc
          (k : ℝ) = (k : ℝ) / (q : ℝ) * (q : ℝ) := by field_simp [hq.ne']
          _ = (t : ℝ) * (q : ℝ) := by rw [ht]
      have hint : k = t * (q : ℤ) := by
        exact_mod_cast hkmul
      simpa [mul_comm] using hint
    have hz : charReal ((k : ℝ) / (q : ℝ)) ≠ 1 := by
      exact charReal_ne_one_of_not_int hθ
    have hg := geomSum_exp_eq_geomSeries q hz
    -- Σ_{r<q} e(r·(k/q)) = (e(q·(k/q)) − 1)/(e(k/q) − 1)
    -- Since e(q·(k/q)) = e(k) = 1, the numerator is zero.
    have hnum : charReal (q * ((k : ℝ) / (q : ℝ))) = 1 := by
      have : q * ((k : ℝ) / (q : ℝ)) = (k : ℝ) := by
        field_simp [hq.ne']
      rw [this, charReal_int_eq_one]
    have hg' : (∑ r ∈ Finset.range q, charReal ((r : ℝ) * ((k : ℝ) / (q : ℝ)))) =
        (charReal (q * ((k : ℝ) / (q : ℝ))) - 1) / (charReal ((k : ℝ) / (q : ℝ)) - 1) :=
      hg
    have hzero : (charReal (q * ((k : ℝ) / (q : ℝ))) - 1) / (charReal ((k : ℝ) / (q : ℝ)) - 1) = 0 := by
      rw [hnum]
      simp
    rw [if_neg hk]
    calc
      (∑ r ∈ Finset.range q, charReal ((k : ℝ) * (r : ℝ) / (q : ℝ)))
          = ∑ r ∈ Finset.range q, charReal ((r : ℝ) * ((k : ℝ) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro r hr
            congr 1
            field_simp [hq.ne']
      _ = 0 := by rw [hg', hzero]

/-- **Finite Fourier Parseval modulo q**: for any `z : ℕ → ℂ`,
  `Σ_{a<q} |Σ_{r<q} e(ar/q)·z_r|² = q·Σ_{r<q} |z_r|²`. -/
theorem zmodParseval {q : ℕ} (hq : 0 < q) (z : ℕ → ℂ) :
    (∑ a ∈ Finset.range q, (‖∑ r ∈ Finset.range q,
        charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r‖ ^ 2 : ℂ)) =
      (q : ℂ) * ∑ r ∈ Finset.range q, (‖z r‖ ^ 2 : ℂ) := by
  calc
    (∑ a ∈ Finset.range q, (‖∑ r ∈ Finset.range q,
        charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r‖ ^ 2 : ℂ))
        = ∑ a ∈ Finset.range q,
            ∑ r ∈ Finset.range q,
              ∑ s ∈ Finset.range q,
                (charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r) *
                  star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ)) * z s) := by
          apply Finset.sum_congr rfl
          intro a ha
          have hcast : (‖∑ r ∈ Finset.range q,
              charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r‖ ^ 2 : ℂ) =
              (‖∑ r ∈ Finset.range q,
                charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r‖ : ℂ) ^ 2 := by
            norm_num
          rw [hcast]
          exact normSq_sum_eq_sum_mul_star (Finset.range q)
            (fun r => charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r)
    _ = ∑ r ∈ Finset.range q,
          ∑ s ∈ Finset.range q,
            z r * star (z s) * (∑ a ∈ Finset.range q,
              charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ))) := by
          -- Exchange sums and combine e(ar/q)·star(e(as/q)) into e(a(r−s)/q).
          have hcross : ∀ a r s : ℕ,
              charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ))) =
                charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) := by
            intro a r s
            have h1 : charReal ((a : ℝ) * (s : ℝ) / (q : ℝ)) =
                charReal (((a : ℝ) * (r : ℝ) / (q : ℝ)) - ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ))) := by
              congr 1
              field_simp [hq.ne']
              ring
            -- Use star(e(x)) = e(−x), followed by e(x−y) = e(x)·e(−y).
            have hs : star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ))) =
                charReal (-((a : ℝ) * (s : ℝ) / (q : ℝ))) := (charReal_neg _).symm
            have hsum' : charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) *
                charReal (-((a : ℝ) * (s : ℝ) / (q : ℝ))) =
                charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) := by
              have harg : (a : ℝ) * (r : ℝ) / (q : ℝ) + -((a : ℝ) * (s : ℝ) / (q : ℝ)) =
                  (a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ) := by
                field_simp [hq.ne']
                ring
              rw [← charReal_add, harg]
            rw [hs]
            exact hsum'
          -- Use sum_comm to replace Σ_a Σ_r Σ_s by Σ_r Σ_s Σ_a.
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s hs
          -- First distribute the factor z r·star(z s) on the right into the sum.
          rw [Finset.mul_sum]
          -- Simplify term by term.
          apply Finset.sum_congr rfl
          intro a ha
          have hterm : (charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r) *
              star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ)) * z s) =
              z r * star (z s) * charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) := by
            calc
              (charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r) *
                  star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ)) * z s)
                  = charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) *
                      star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ))) * (z r * star (z s)) := by
                    rw [star_mul]
                    ring
              _ = charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) * (z r * star (z s)) := by
                    rw [hcross a r s]
              _ = z r * star (z s) * charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) := by ring
          rw [hterm]
    _ = (q : ℂ) * ∑ r ∈ Finset.range q, (‖z r‖ ^ 2 : ℂ) := by
          -- Inner kernel: Σ_a e(a(r−s)/q) = q·1_{r=s} for r,s < q.
          have hkern : ∀ r s : ℕ, r ∈ Finset.range q → s ∈ Finset.range q →
              (∑ a ∈ Finset.range q,
                charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ))) =
                if r = s then (q : ℂ) else 0 := by
            intro r s hr hs
            by_cases hrs : r = s
            · subst hrs
              rw [if_pos rfl]
              calc
                (∑ a ∈ Finset.range q, charReal ((a : ℝ) * ((r : ℝ) - (r : ℝ)) / (q : ℝ)))
                    = ∑ a ∈ Finset.range q, (1 : ℂ) := by
                      apply Finset.sum_congr rfl
                      intro a ha
                      have h0 : (a : ℝ) * ((r : ℝ) - (r : ℝ)) / (q : ℝ) = 0 := by ring
                      rw [h0, charReal_zero]
                _ = (q : ℂ) := by simp
            · rw [if_neg hrs]
              have hdiv : ¬ (q : ℤ) ∣ ((r : ℤ) - (s : ℤ)) := by
                intro hd
                rcases hd with ⟨m, hm⟩
                have hne : (r : ℤ) ≠ (s : ℤ) := by exact_mod_cast hrs
                have hz : (r : ℤ) - (s : ℤ) ≠ 0 := sub_ne_zero.mpr hne
                have hm0 : m ≠ 0 := by
                  intro hm0
                  rw [hm0, mul_zero] at hm
                  exact hz hm
                have hqle : (q : ℤ) ≤ ((r : ℤ) - (s : ℤ)).natAbs := by
                  have hqm : (r : ℤ) - (s : ℤ) = (q : ℤ) * m := hm
                  have habs : ((r : ℤ) - (s : ℤ)).natAbs = (q : ℤ) * |m| := by
                    rw [hqm, Int.natAbs_mul, Int.natAbs_natCast, Int.abs_eq_natAbs]
                    norm_num
                  have hm1 : 1 ≤ |m| := Int.one_le_abs hm0
                  have hq0 : 0 ≤ (q : ℤ) := by exact_mod_cast (Nat.zero_le q)
                  rw [habs]
                  nlinarith
                have hlt : ((r : ℤ) - (s : ℤ)).natAbs < (q : ℤ) := by
                  have h1 : (r : ℤ) - (s : ℤ) < (q : ℤ) := by
                    have hrq : (r : ℤ) < (q : ℤ) := by exact_mod_cast (Finset.mem_range.mp hr)
                    have hs0 : 0 ≤ (s : ℤ) := by exact_mod_cast (Nat.zero_le s)
                    linarith
                  have h2 : -(q : ℤ) < (r : ℤ) - (s : ℤ) := by
                    have hsq : (s : ℤ) < (q : ℤ) := by exact_mod_cast (Finset.mem_range.mp hs)
                    have hr0 : 0 ≤ (r : ℤ) := by exact_mod_cast (Nat.zero_le r)
                    linarith
                  have hlt' : |(r : ℤ) - (s : ℤ)| < (q : ℤ) := (abs_lt).2 ⟨h2, h1⟩
                  rwa [Int.abs_eq_natAbs] at hlt'
                linarith
              have hgeo' : (∑ a ∈ Finset.range q,
                  charReal ((↑((r : ℤ) - (s : ℤ)) : ℝ) * (a : ℝ) / (q : ℝ))) = 0 := by
                have hgeo := geomSum_zmod_charReal hq ((r : ℤ) - (s : ℤ))
                rw [hgeo, if_neg hdiv]
              calc
                (∑ a ∈ Finset.range q, charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)))
                    = ∑ a ∈ Finset.range q,
                        charReal ((↑((r : ℤ) - (s : ℤ)) : ℝ) * (a : ℝ) / (q : ℝ)) := by
                      apply Finset.sum_congr rfl
                      intro a ha
                      congr 1
                      have hc : (↑((r : ℤ) - (s : ℤ)) : ℝ) = (r : ℝ) - (s : ℝ) := by
                        norm_num
                      rw [hc]
                      ring
                _ = 0 := hgeo'
          calc
            (∑ r ∈ Finset.range q, ∑ s ∈ Finset.range q,
                z r * star (z s) * (∑ a ∈ Finset.range q,
                  charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ))))
                = ∑ r ∈ Finset.range q, ∑ s ∈ Finset.range q,
                    z r * star (z s) * (if r = s then (q : ℂ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  apply Finset.sum_congr rfl
                  intro s hs
                  rw [hkern r s hr hs]
            _ = ∑ r ∈ Finset.range q, z r * star (z r) * (q : ℂ) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  calc
                    (∑ s ∈ Finset.range q, z r * star (z s) * if r = s then (q : ℂ) else 0)
                        = z r * star (z r) * if r = r then (q : ℂ) else 0 := by
                          refine Finset.sum_eq_single r ?_ ?_
                          · intro b hb hbr
                            simp [hbr.symm]
                          · intro hnr
                            exact False.elim (hnr hr)
                    _ = z r * star (z r) * (q : ℂ) := by simp
            _ = (q : ℂ) * ∑ r ∈ Finset.range q, (‖z r‖ ^ 2 : ℂ) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro r hr
                  have hmul : z r * star (z r) = (‖z r‖ ^ 2 : ℂ) := by
                    have h := Complex.mul_conj (z r)
                    rw [Complex.normSq_eq_norm_sq] at h
                    simpa using h
                  rw [hmul, mul_comm]

/-! ## 3. Character orthogonality -/

/-- Pointwise character orthogonality: for `m, n : ZMod q`,
  `Σ_χ χ(m)·conj(χ(n)) = φ(q)·1_{IsUnit m ∧ IsUnit n ∧ m = n}`. -/
theorem charOrthSum {q : ℕ} (hq : 0 < q) (m n : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, χ m * star (χ n)) =
      if IsUnit m ∧ IsUnit n ∧ m = n then (q.totient : ℂ) else 0 := by
  classical
  have : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    complexHasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ) (by
      -- The finite unit group (ZMod q)ˣ has nonzero exponent, by finiteness.
      have hfin : Finite (ZMod q)ˣ := inferInstance
      exact Monoid.exponent_ne_zero.mpr (Monoid.ExponentExists.of_finite (G := (ZMod q)ˣ)))
  by_cases hm : IsUnit m
  · by_cases hn : IsUnit n
    · -- Both are units: rewrite χ(m)·conj(χ(n)) as χ(n⁻¹)·χ(m) and use sum_char_inv_mul_char_eq.
      have hsum := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (a := n) hn m
      -- hsum : ∑ χ, χ n⁻¹ * χ m = if n = m then q.totient else 0
      have hrewrite : ∀ χ : DirichletCharacter ℂ q, χ m * star (χ n) = χ n⁻¹ * χ m := by
        intro χ
        have hconj := char_conj_inv χ hn
        -- star(χ n) = χ⁻¹ n = χ(n⁻¹)
        have hinv : χ⁻¹ n = χ (n⁻¹) := by
          rw [MulChar.inv_apply]
          have hspec : (↑hn.unit : ZMod q) = n := hn.unit_spec
          have hrinv : Ring.inverse n = (↑hn.unit⁻¹ : ZMod q) := by
            calc
              Ring.inverse n = Ring.inverse (↑hn.unit : ZMod q) := by rw [hspec]
              _ = (↑hn.unit⁻¹ : ZMod q) := Ring.inverse_unit hn.unit
          rw [hrinv]
          -- The unit inverses agree: ↑hn.unit⁻¹ = n⁻¹, by uniqueness from n·n⁻¹ = 1 and n·↑u⁻¹ = 1.
          have hnval : n.val.Coprime q := by
            have hunit : IsUnit (↑n.val : ZMod q) := by
              simpa [ZMod.natCast_zmod_val] using hn
            exact (ZMod.isUnit_iff_coprime n.val q).mp hunit
          have hmul : n * n⁻¹ = 1 := by
            have h := ZMod.coe_mul_inv_eq_one n.val hnval
            simpa [ZMod.natCast_zmod_val] using h
          have hmul' : n * (↑hn.unit⁻¹ : ZMod q) = 1 := by
            simp
          have hninv : (↑hn.unit⁻¹ : ZMod q) = n⁻¹ := (inv_unique hmul hmul').symm
          rw [hninv]
        rw [hconj, hinv]
        -- Commute χ m·χ(n⁻¹) to χ(n⁻¹)·χ m.
        rw [mul_comm]
      -- Substitute term by term.
      have hsum' : (∑ χ : DirichletCharacter ℂ q, χ m * star (χ n)) =
          ∑ χ : DirichletCharacter ℂ q, χ n⁻¹ * χ m := by
        apply Finset.sum_congr rfl
        intro χ hχ
        exact hrewrite χ
      rw [hsum']
      -- The sum now equals if n = m then q.totient else 0, by hsum.
      by_cases hmn : m = n
      · have hcond : IsUnit m ∧ IsUnit n ∧ m = n := ⟨hm, hn, hmn⟩
        rw [if_pos hcond]
        rw [hsum, if_pos hmn.symm]
      · have hnot : ¬ (IsUnit m ∧ IsUnit n ∧ m = n) := by
          intro h
          exact hmn h.2.2
        rw [if_neg hnot]
        rw [hsum, if_neg (fun hnm => hmn hnm.symm)]
    · -- n is not a unit: star(χ n) = star 0 = 0.
      have hχn : ∀ χ : DirichletCharacter ℂ q, star (χ n) = 0 := by
        intro χ
        have hz : χ n = 0 := χ.map_nonunit hn
        simp [hz]
      have hnot : ¬ (IsUnit m ∧ IsUnit n ∧ m = n) := by
        intro h
        exact hn h.2.1
      rw [if_neg hnot]
      -- The sum is zero.
      apply Finset.sum_eq_zero
      intro χ hχ
      rw [hχn χ, mul_zero]
  · -- m is not a unit: χ(m) = 0.
    have hχm : ∀ χ : DirichletCharacter ℂ q, χ m = 0 := by
      intro χ
      exact χ.map_nonunit hm
    have hnot : ¬ (IsUnit m ∧ IsUnit n ∧ m = n) := by
      intro h
      exact hm h.1
    rw [if_neg hnot]
    apply Finset.sum_eq_zero
    intro χ hχ
    rw [hχm χ, zero_mul]


/-! ## 4. Well-spaced rational points and the multiplicative large sieve -/

/-- The rational point set `X_Q = {r/q : 1 ≤ q ≤ Q, 0 ≤ r < q} ⊆ [0,1)`. -/
noncomputable def rationalPoints (Q : ℕ) : Finset ℝ :=
  (Finset.Icc 1 Q).biUnion (fun q => (Finset.range q).image (fun r : ℕ => (r : ℝ) / (q : ℝ)))

/-- Two distinct rational points modulo 1 have distance at least `1/(q₁q₂)`. -/
theorem rationals_distToInt_ge {q₁ r₁ q₂ r₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : r₁ < q₁) (hr₂ : r₂ < q₂)
    (hne : (r₁ : ℝ) / (q₁ : ℝ) ≠ (r₂ : ℝ) / (q₂ : ℝ)) :
    1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      distToInt ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) := by
  -- Both distinct points lie in [0,1), so their difference is not an integer.
  have hx0 : 0 ≤ (r₁ : ℝ) / (q₁ : ℝ) := by positivity
  have hx1 : (r₁ : ℝ) / (q₁ : ℝ) < 1 := by
    exact (div_lt_one (by exact_mod_cast hq₁)).mpr (by exact_mod_cast hr₁)
  have hy0 : 0 ≤ (r₂ : ℝ) / (q₂ : ℝ) := by positivity
  have hy1 : (r₂ : ℝ) / (q₂ : ℝ) < 1 := by
    exact (div_lt_one (by exact_mod_cast hq₂)).mpr (by exact_mod_cast hr₂)
  have hnotint : ¬ ∃ k : ℤ, (k : ℝ) = (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) := by
    intro hk
    rcases hk with ⟨k, hk⟩
    -- |x − y| < 1 and x ≠ y force k = 0, hence x = y, a contradiction.
    have hlt : |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)| < 1 := by
      -- 0 ≤ x,y < 1 ⟹ |x−y| < 1
      have hxy : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) < 1 := by linarith
      have hxy' : -1 < (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) := by linarith
      rw [abs_lt]
      exact ⟨hxy', hxy⟩
    have hkabs : |(k : ℝ)| < 1 := by
      calc
        |(k : ℝ)| = |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)| := by
          exact congrArg abs hk
        _ < 1 := hlt
    have hk0 : k = 0 := by
      -- An integer k with |k| < 1 is zero.
      have hkz : (k.natAbs : ℝ) < 1 := by
        -- |k| = ↑k.natAbs
        have hcast : |(k : ℝ)| = ((k.natAbs : ℕ) : ℝ) := by
          rw [← Int.cast_abs]
          congr 1
          exact Int.abs_eq_natAbs k
        calc
          (k.natAbs : ℝ) = |(k : ℝ)| := hcast.symm
          _ < 1 := hkabs
      have hk0' : k.natAbs = 0 := by
        -- 0 ≤ k.natAbs < 1 ⟹ = 0
        have hlt' : k.natAbs < 1 := by exact_mod_cast hkz
        omega
      exact Int.natAbs_eq_zero.mp hk0'
    -- x = y is a contradiction.
    apply hne
    have hxy : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) = 0 := by
      rw [← hk, hk0]
      norm_num
    linarith
  -- For every integer k, |x − y − k| ≥ 1/(q₁q₂).
  have hk : ∀ k : ℤ, 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) - (k : ℝ)| := by
    intro k
    -- x − y − k = (r₁q₂ − r₂q₁ − k q₁q₂)/(q₁q₂), with a nonzero integer numerator.
    have hnum : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) ≠ 0 := by
      intro hz
      -- A zero numerator would imply x − y = k by cross multiplication, contradicting hnotint.
      apply hnotint
      refine ⟨k, ?_⟩
      -- (r₁:ℝ)/(q₁:ℝ) − (r₂:ℝ)/(q₂:ℝ) = (r₁q₂ − r₂q₁)/(q₁q₂) = k
      have hcross : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) : ℤ) = k * ((q₁ : ℤ) * (q₂ : ℤ)) := by
        linarith
      -- Cast to ℝ.
      have hcrossR : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) : ℝ) =
          (k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℝ) := by exact_mod_cast hcross
      -- Goal: (r₁:ℝ)/(q₁:ℝ) − (r₂:ℝ)/(q₂:ℝ) = k.
      have htarget : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) = (k : ℝ) := by
        have hmain : ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) * ((q₁ : ℝ) * (q₂ : ℝ)) =
            (k : ℝ) * ((q₁ : ℝ) * (q₂ : ℝ)) := by
          calc
            ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) * ((q₁ : ℝ) * (q₂ : ℝ))
                = (r₁ : ℝ) * (q₂ : ℝ) - (r₂ : ℝ) * (q₁ : ℝ) := by
                  field_simp [hq₁.ne', hq₂.ne']
            _ = (k : ℝ) * ((q₁ : ℝ) * (q₂ : ℝ)) := hcrossR
        have hden : (q₁ : ℝ) * (q₂ : ℝ) ≠ 0 := by positivity
        have hmain' : (q₁ : ℝ) * (q₂ : ℝ) * ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) =
            (q₁ : ℝ) * (q₂ : ℝ) * (k : ℝ) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
        exact mul_left_cancel₀ hden hmain'
      exact htarget.symm
    -- |x − y − k| = |numerator|/(q₁q₂) ≥ 1/(q₁q₂).
    have habs : |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) - (k : ℝ)| =
        |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| /
          ((q₁ : ℝ) * (q₂ : ℝ)) := by
      have hnumR : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) - (k : ℝ) =
          (((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ) /
            ((q₁ : ℝ) * (q₂ : ℝ)) := by
        field_simp [hq₁.ne', hq₂.ne']
        norm_num [Int.cast_mul, Int.cast_sub]
        ring
      have hden : 0 < (q₁ : ℝ) * (q₂ : ℝ) := mul_pos (by exact_mod_cast hq₁) (by exact_mod_cast hq₂)
      rw [hnumR, abs_div, abs_of_nonneg (le_of_lt hden)]
    have hnumR : |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| ≠ 0 := by
      have hn : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) ≠ 0 := hnum
      have hz : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℝ) ≠ 0 := by
        exact_mod_cast hn
      intro habs
      have h0 : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℝ) = 0 := by
        simpa using (abs_eq_zero.mp habs)
      exact hz h0
    have hge1 : 1 ≤ |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| := by
      -- A nonzero integer has absolute value at least 1.
      have hz : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) ≠ 0 := hnum
      have hz' : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ).natAbs ≠ 0 :=
        Int.natAbs_ne_zero.mpr hz
      have hz1 : 1 ≤ ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ).natAbs := by
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz')
      -- |↑n| = ↑n.natAbs ≥ 1
      have hcast : |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| =
          (((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ).natAbs : ℝ) := by
        rw [← Int.cast_abs]
        congr 1
        exact Int.abs_eq_natAbs (r₁ * q₂ - r₂ * q₁ - k * (q₁ * q₂) : ℤ)
      rw [hcast]
      exact_mod_cast hz1
    rw [habs]
    -- |numerator|/(q₁q₂) ≥ 1/(q₁q₂) is equivalent to |numerator| ≥ 1.
    have hden : 0 < (q₁ : ℝ) * (q₂ : ℝ) := mul_pos (by exact_mod_cast hq₁) (by exact_mod_cast hq₂)
    have hpos : 0 ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := one_div_nonneg.mpr (le_of_lt hden)
    calc
      1 / ((q₁ : ℝ) * (q₂ : ℝ))
          ≤ |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| *
              (1 / ((q₁ : ℝ) * (q₂ : ℝ))) := by
            simpa using (mul_le_mul_of_nonneg_right hge1 hpos)
      _ = |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| /
            ((q₁ : ℝ) * (q₂ : ℝ)) := by ring
  -- distToInt z = min(fract z, 1−fract z), and both |z−⌊z⌋| and |z−(⌊z⌋+1)| are at least 1/(q₁q₂).
  let z : ℝ := (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)
  have hz1 : 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |z - (⌊z⌋ : ℝ)| := by
    change 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) -
        (⌊(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)⌋ : ℝ)|
    exact hk (⌊(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)⌋)
  have hz2 : 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |z - ((⌊z⌋ + 1 : ℤ) : ℝ)| := by
    change 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) -
        ((⌊(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)⌋ + 1 : ℤ) : ℝ)|
    exact hk (⌊(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)⌋ + 1)
  -- |z − ⌊z⌋| = fract z, |z − (⌊z⌋+1)| = 1 − fract z
  have hf1 : |z - (⌊z⌋ : ℝ)| = Int.fract z := by
    -- fract z = z − ⌊z⌋ ≥ 0
    have hzge : 0 ≤ z - (⌊z⌋ : ℝ) := by
      rw [Int.self_sub_floor]
      exact Int.fract_nonneg z
    calc
      |z - (⌊z⌋ : ℝ)| = z - (⌊z⌋ : ℝ) := abs_of_nonneg hzge
      _ = Int.fract z := Int.self_sub_floor z
  have hf2 : |z - ((⌊z⌋ + 1 : ℤ) : ℝ)| = 1 - Int.fract z := by
    -- ⌊z⌋+1 − z = 1 − fract z ≥ 0
    have hzle : 0 ≤ ((⌊z⌋ + 1 : ℤ) : ℝ) - z := by
      -- z < ⌊z⌋ + 1
      have hlt : z < (⌊z⌋ : ℝ) + 1 := by
        -- Int.lt_floor_add_one
        have := Int.lt_floor_add_one z
        -- z < ↑⌊z⌋ + 1
        exact this
      have hle : (⌊z⌋ : ℝ) + 1 ≤ ((⌊z⌋ + 1 : ℤ) : ℝ) := by norm_num
      linarith
    have habs : |z - ((⌊z⌋ + 1 : ℤ) : ℝ)| = ((⌊z⌋ + 1 : ℤ) : ℝ) - z := by
      rw [abs_sub_comm]
      exact abs_of_nonneg hzle
    rw [habs]
    -- (⌊z⌋+1) − z = 1 − fract z
    have hfz : z = Int.fract z + (⌊z⌋ : ℝ) := (Int.fract_add_floor z).symm
    calc
      ((⌊z⌋ + 1 : ℤ) : ℝ) - z = ((⌊z⌋ : ℝ) + 1) - z := by norm_num
      _ = ((⌊z⌋ : ℝ) + 1) - (Int.fract z + (⌊z⌋ : ℝ)) := by
            conv_lhs =>
              arg 2
              rw [hfz]
      _ = 1 - Int.fract z := by ring
  -- distToInt z = min(fract z, 1 − fract z) ≥ 1/(q₁q₂)
  dsimp [distToInt]
  rw [le_min_iff]
  constructor
  · -- fract z ≥ 1/(q₁q₂)
    rw [← hf1]
    exact hz1
  · -- 1 − fract z ≥ 1/(q₁q₂)
    rw [← hf2]
    exact hz2

/-- The rational point set `X_Q = {r/q : 1 ≤ q ≤ Q, 0 ≤ r < q}`
is `1/Q²`-well-spaced. -/
theorem rationalPoints_wellSpaced (Q : ℕ) (hQ : 0 < Q) :
    wellSpacedReal (rationalPoints Q) (1 / (Q : ℝ) ^ 2) := by
  intro x hx y hy hxy
  rcases (Finset.mem_biUnion.mp hx) with ⟨q₁, hq₁, hx'⟩
  rcases (Finset.mem_image.mp hx') with ⟨r₁, hr₁, rfl⟩
  rcases (Finset.mem_biUnion.mp hy) with ⟨q₂, hq₂, hy'⟩
  rcases (Finset.mem_image.mp hy') with ⟨r₂, hr₂, rfl⟩
  have hq₁pos : 0 < q₁ := (Finset.mem_Icc.mp hq₁).1
  have hq₂pos : 0 < q₂ := (Finset.mem_Icc.mp hq₂).1
  have hq₁Q : q₁ ≤ Q := (Finset.mem_Icc.mp hq₁).2
  have hq₂Q : q₂ ≤ Q := (Finset.mem_Icc.mp hq₂).2
  have hr₁' : r₁ < q₁ := Finset.mem_range.mp hr₁
  have hr₂' : r₂ < q₂ := Finset.mem_range.mp hr₂
  have hd : 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      distToInt ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) :=
    rationals_distToInt_ge hq₁pos hq₂pos hr₁' hr₂' hxy
  have hq₁q₂ : (q₁ : ℝ) * (q₂ : ℝ) ≤ (Q : ℝ) * (Q : ℝ) := by
    have h₁ : (q₁ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₁Q
    have h₂ : (q₂ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₂Q
    exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have hden₁ : 0 < (q₁ : ℝ) * (q₂ : ℝ) := mul_pos (by exact_mod_cast hq₁pos) (by exact_mod_cast hq₂pos)
  have hQinv : 1 / ((Q : ℝ) * (Q : ℝ)) ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) :=
    one_div_le_one_div_of_le hden₁ hq₁q₂
  have hQ2 : (Q : ℝ) ^ 2 = (Q : ℝ) * (Q : ℝ) := by ring
  calc
    1 / (Q : ℝ) ^ 2 = 1 / ((Q : ℝ) * (Q : ℝ)) := by rw [hQ2]
    _ ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := hQinv
    _ ≤ distToInt ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) := hd

/-! ## 5. Multiplicative large-sieve assembly: inverse Parseval, characters, and Farey points -/

/-- Summation along the bijection between residue classes modulo `q`
and `0..q−1`: `Σ_{x : ZMod q} f x = Σ_{a < q} f ↑a`. -/
theorem zmod_sum_range {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M] (f : ZMod q → M) :
    (∑ x : ZMod q, f x) = ∑ a ∈ Finset.range q, f (a : ZMod q) := by
  symm
  refine Finset.sum_bij (s := Finset.range q) (t := (Finset.univ : Finset (ZMod q)))
    (fun a _ => (a : ZMod q)) ?_ ?_ ?_ ?_
  · intro a ha
    simp
  · intro a ha b hb hab
    have hltb : b < q := Finset.mem_range.mp hb
    have hmod : a ≡ b [MOD q] := (ZMod.natCast_eq_natCast_iff a b q).mp hab
    exact Nat.ModEq.eq_of_lt_of_lt hmod (Finset.mem_range.mp ha) hltb
  · intro x hx
    refine ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩
    exact (ZMod.natCast_zmod_val x)
  · intro a ha
    rfl


/-- Congruence periodicity modulo `q`: for an integer `m` and natural `n`,
`(m : ZMod q) = (n : ZMod q)` implies `e(mr/q) = e(nr/q)`. -/
theorem charReal_zmod_eq {q : ℕ} (hq : 0 < q) {m : ℤ} {n : ℕ}
    (hmn : (m : ZMod q) = (n : ZMod q)) (r : ℕ) :
    charReal ((m : ℝ) * (r : ℝ) / (q : ℝ)) = charReal ((n : ℝ) * (r : ℝ) / (q : ℝ)) := by
  have hmod : m ≡ (n : ℤ) [ZMOD (q : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff m (n : ℤ) (q)]
    simpa using hmn
  rcases (Int.modEq_iff_add_fac.mp hmod) with ⟨t, ht⟩
  have hRt : (n : ℝ) = (m : ℝ) + (q : ℝ) * (t : ℝ) := by exact_mod_cast ht
  calc
    charReal ((m : ℝ) * (r : ℝ) / (q : ℝ))
        = charReal (((n : ℝ) * (r : ℝ) / (q : ℝ)) + (-(t : ℝ) * (r : ℝ))) := by
          congr 1
          field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne']
          nlinarith
    _ = charReal ((n : ℝ) * (r : ℝ) / (q : ℝ)) := by
          have hk : (-(t : ℝ) * (r : ℝ)) = ((-(t * (r : ℤ) : ℤ) : ℤ) : ℝ) := by
            norm_num
          rw [hk]
          exact charReal_periodic_int ((n : ℝ) * (r : ℝ) / (q : ℝ)) (-(t * (r : ℤ) : ℤ))
