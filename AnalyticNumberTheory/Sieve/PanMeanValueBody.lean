import AnalyticNumberTheory.Sieve.WeightedPan
import AnalyticNumberTheory.Sieve.VaughanIdentity
import Mathlib.Data.ZMod.Basic
import AnalyticNumberTheory.LargeSieve.CharacterIndicators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.GroupTheory.Exponent
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

/-! # AnalyticNumberTheory.Sieve.PanMeanValueBody

## Finite reductions for weighted Pan mean values

This module supplies reductions toward `PanMeanValueUniform`
(`WeightedPan.lean`), following Liu 2022 §II--§III:

- Sections 1--2 absorb a coprime scaling factor `a` into the residue
  class: `π(y;a,q,l) = π(y/a;q,l·a⁻¹)`. The Pan expression becomes
  a weighted sum of ordinary arithmetic-progression prime counts.
- Section 3 proves nonnegativity and maximum-to-sum bounds for
  `panMaxL` and `panMaxY`.
- Sections 4--5 record Type I, Type II, and main-term input propositions
  and prove the finite character-expansion/Cauchy--Schwarz reductions.

Section 1 defines `natInvMod q a` and proves
`a·p ≡ l [MOD q] ⟺ p ≡ natInvMod q a · l [MOD q]` for `(a,q)=1`.
Section 2 uses this and `a·p ≤ y ⟺ p ≤ y/a` for positive `a` to prove
`primesInAPBelow y a q l
 = primesInAP (y/a) q (natInvMod q a · l % q)`.
The counting bijection is the identity on `p`.
Consequently the distribution error is
`π(y/a;q,l·a⁻¹) − li(y/a)/φ(q)`, with natural division in the
prime-count cutoff and real division in the main-term argument.
Here `li` denotes the project's `x/log x` proxy.

The weighted sum becomes
`Σ_{1≤a≤X} [a.Coprime q]·f(a)·(π(y/a;q,l·a⁻¹) − li(y/a)/φ(q))`
plus the explicitly separated `a = 0` term. This is an exact identity,
not an asymptotic error term.

Related inputs include the Farey-point large sieve
`LargeSieve.Multiplicative.largeSieveRationalPoints`, the per-modulus
character bound `characterSieveModulus_le`, Vaughan's identity
(`Sieve.VaughanIdentity`), and the squarefree weight identity
`3^{ω(q)} = Σ_{d|q} 2^{ω(d)}` in `WeightedPan`.

The Type I and Type II reductions are conditional:
`PanTypeIWeightedBound.of_characterMeanValue` and
`PanTypeIIWeightedBound.of_characterMeanValue` require their
respective character-mean inputs. The later square-mean reductions
do not prove those analytic inputs or an unrestricted uniform
all-character bound. Further assembly is in `PanAssembly.lean`;
the main-term distinction is described in `PanMainTerm.lean`.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

/-! ## 1. Inverse residues and congruence cancellation modulo q -/

/-- Inverse residue modulo `q`: when `(a,q)=1`, take the natural
representative of the inverse of `a` in `ZMod q`. `ZMod.val` is the
least nonnegative representative, or the absolute value at modulus 0.
It satisfies `a·b ≡ 1 [MOD q]`. Otherwise use 0; the inverse
properties are only used under the coprimality hypothesis. -/
noncomputable def natInvMod (q a : ℕ) : ℕ :=
  if _h : a.Coprime q then (a⁻¹ : ZMod q).val else 0

/-- Defining property of `natInvMod`: if `(a,q)=1`, then
`a · natInvMod q a % q = 1 % q`, equivalently
`a · natInvMod q a ≡ 1 [MOD q]`.
This holds for every `q`, including the trivial cases `q = 0,1`. -/
theorem natInvMod_spec {q a : ℕ} (hcop : a.Coprime q) :
    a * natInvMod q a % q = 1 % q := by
  unfold natInvMod
  rw [dif_pos hcop]
  have hz : ((a * (a⁻¹ : ZMod q).val : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    rw [Nat.cast_mul]
    simpa using (ZMod.mul_val_inv hcop)
  exact (ZMod.natCast_eq_natCast_iff (a := a * (a⁻¹ : ZMod q).val) (b := 1) (c := q)).mp hz

/-- Congruence form of `natInvMod`:
`a · natInvMod q a ≡ 1 [MOD q]` under coprimality, for every `q`,
including `q = 0,1`. -/
theorem natInvMod_congr {q a : ℕ} (hcop : a.Coprime q) :
    a * natInvMod q a ≡ 1 [MOD q] := by
  rw [Nat.ModEq]
  exact natInvMod_spec hcop

/-- **Cancellation by an invertible factor**: if `a·b ≡ 1 [MOD q]`,
then `a·p ≡ l [MOD q] ⟺ p ≡ b·l [MOD q]`.
This is the congruence step in Liu §II's absorption of `a`:
replace the congruence on the coprime multiple `a·p` by a residue
condition on `p`. -/
theorem modEq_mul_left_inv_iff {q a p l b : ℕ} (hb : a * b ≡ 1 [MOD q]) :
    (a * p ≡ l [MOD q]) ↔ (p ≡ b * l [MOD q]) := by
  constructor
  · intro hcong
    have h1 : b * (a * p) ≡ b * l [MOD q] := hcong.mul_left b
    have hba : b * a ≡ 1 [MOD q] := by simpa [Nat.mul_comm] using hb
    have hp : (b * a) * p ≡ 1 * p [MOD q] := hba.mul_right p
    have h2 : b * (a * p) ≡ p [MOD q] := by
      simpa [Nat.mul_assoc, one_mul] using hp
    exact h2.symm.trans h1
  · intro hcong
    have h1 : a * p ≡ a * (b * l) [MOD q] := hcong.mul_left a
    have h2 : a * (b * l) ≡ l [MOD q] := by
      simpa [Nat.mul_assoc, one_mul] using hb.mul_right l
    exact h1.trans h2

/-! ## 2. Absorbing a as in Liu §II: scaled counts and weighted errors -/

/-- **Scaled count as an ordinary AP count** (Liu §II):
for `(a,q)=1` and `a ≥ 1`,
`π(y;a,q,l) = π(y/a;q,l·a⁻¹)`.
Among primes,
`#{p : a·p ≤ y, a·p ≡ l [MOD q]}
 = #{p : p ≤ y/a, p ≡ l·a⁻¹ [MOD q]}`.
Division is in `ℕ`, since the integer solutions of `a·p ≤ y`
satisfy `p ≤ ⌊y/a⌋`. -/
theorem primesInAPBelow_eq_primesInAP_inv (y a q l : ℕ) (ha : 0 < a)
    (hcop : a.Coprime q) :
    primesInAPBelow y a q l = primesInAP (y / a) q (natInvMod q a * l % q) := by
  unfold primesInAPBelow primesInAP
  have hcongr := natInvMod_congr (q := q) (a := a) hcop
  have hiff : (fun p : ℕ => a * p ≡ l [MOD q]) =
      (fun p : ℕ => p ≡ natInvMod q a * l % q [MOD q]) := by
    funext p
    have h1 : (a * p ≡ l [MOD q]) ↔ (p ≡ natInvMod q a * l [MOD q]) :=
      modEq_mul_left_inv_iff hcongr
    have hmod : (p ≡ natInvMod q a * l % q [MOD q]) ↔
        (p ≡ natInvMod q a * l [MOD q]) := by
      have hmm : natInvMod q a * l % q ≡ natInvMod q a * l [MOD q] :=
        (Nat.mod_modEq (a := natInvMod q a * l) (n := q))
      constructor
      · intro hp
        exact hp.trans hmm
      · intro hp
        exact hp.trans hmm.symm
    exact propext (h1.trans hmod.symm)
  have hfilt : (Finset.range (y + 1)).filter
        (fun p => p.Prime ∧ a * p ≤ y ∧ a * p ≡ l [MOD q]) =
      (Finset.range (y / a + 1)).filter
        (fun p => p.Prime ∧ p ≡ natInvMod q a * l % q [MOD q]) := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpR, hpp, hle, hcong⟩
      constructor
      · rw [Finset.mem_range]
        have hle' : p ≤ y / a :=
          (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using hle)
        exact Nat.lt_succ_of_le hle'
      · exact ⟨hpp, (congrFun hiff p).mp hcong⟩
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpR, hpp, hcong⟩
      have hp_le : p ≤ y / a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpR)
      have hle : a * p ≤ y := by
        have hle' : p * a ≤ y := (Nat.le_div_iff_mul_le ha).1 hp_le
        simpa [Nat.mul_comm] using hle'
      constructor
      · rw [Finset.mem_range]
        have hp_le_y : p ≤ y := le_trans (Nat.le_mul_of_pos_left p ha) hle
        exact Nat.lt_succ_of_le hp_le_y
      · exact ⟨hpp, ⟨hle, (congrFun hiff p).mpr hcong⟩⟩
  exact congrArg Finset.card hfilt

/-- **Distribution-error form of a-absorption** (Liu §II):
for `(a,q)=1` and `a ≥ 1`,
`Δ(y;a,q,l) = π(y/a;q,l·a⁻¹) − li(y/a)/φ(q)`.
The `li` proxy uses the real argument `(y : ℝ)/a`, whereas
the prime count uses natural division `y/a`. This distinction must
be retained when comparing the main term with the sieve main term. -/
theorem panDistributionError_scaled_inv (y a q l : ℕ) (ha : 0 < a)
    (hcop : a.Coprime q) :
    panDistributionError y a q l =
      ((primesInAP (y / a) q (natInvMod q a * l % q) : ℝ) -
        logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) := by
  unfold panDistributionError
  rw [primesInAPBelow_eq_primesInAP_inv y a q l ha hcop]

/-- **Weighted distribution sum in Liu §II form**: for any `f`,
`Σ_{(a,q)=1, a≤X} f(a)·Δ(y;a,q,l)` equals
`Σ_{1≤a≤X} [a.Coprime q]·f(a)·(π(y/a;q,l·a⁻¹) − li(y/a)/φ(q))`
plus the `a = 0` term.
That term can be nonzero only when `q = 1`, since
`0.Coprime q ↔ q = 1`. It is left unreduced and explicit:
the classical sum starts at 1, so separating it preserves exactness. -/
theorem panDistributionSum_eq_weighted (y X q l : ℕ) (f : ℕ → ℝ) :
    panDistributionSum y X q l f =
      (if (0 : ℕ).Coprime q then f 0 * panDistributionError y 0 q l else 0) +
        ∑ a ∈ Finset.Icc 1 X,
          if a.Coprime q then
            f a * ((primesInAP (y / a) q (natInvMod q a * l % q) : ℝ) -
              logarithmicIntegral ((y : ℝ) / a) / Nat.totient q)
          else 0 := by
  unfold panDistributionSum
  have hrange : Finset.range (X + 1) = insert 0 (Finset.Icc 1 X) := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_insert]
      by_cases ha0 : a = 0
      · exact Or.inl ha0
      · have hpos : 0 < a := Nat.pos_of_ne_zero ha0
        have haX : a ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact Or.inr (Finset.mem_Icc.mpr ⟨hpos, haX⟩)
    · intro ha
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | haIcc
      · simp
      · have hmem := Finset.mem_Icc.mp haIcc
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le hmem.2
  rw [hrange, Finset.sum_insert (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · rw [if_pos hcop, if_pos hcop]
    congr 1
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    exact panDistributionError_scaled_inv y a q l (by omega) hcop
  · simp [hcop]

/-! ## 3. Maximum bounds for panMaxL and panMaxY -/

/-- Every `|panDistributionSum|` is nonnegative, so its finite
maximum `panMaxL` is nonnegative, with value 0 for an empty set. -/
theorem panMaxL_nonneg (y X q : ℕ) (f : ℕ → ℝ) : 0 ≤ panMaxL y X q f := by
  unfold panMaxL
  by_cases h : (unitResidues q).Nonempty
  · dsimp only []
    rw [dif_pos h]
    rcases h with ⟨l, hl⟩
    have hl' : |panDistributionSum y X q l f| ∈
        (Finset.image (fun l : ℕ => |panDistributionSum y X q l f|)
          (unitResidues q)) := by
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    exact le_trans (abs_nonneg _) (Finset.le_max' _ _ hl')
  · dsimp only []
    rw [dif_neg h]

/-- The residue maximum is bounded by the sum of absolute values:
`max_l |·| ≤ Σ_l |·|`. -/
theorem panMaxL_le_sum_abs (y X q : ℕ) (f : ℕ → ℝ)
    (hS : (unitResidues q).Nonempty) :
    panMaxL y X q f ≤
      ∑ l ∈ unitResidues q,
        |panDistributionSum y X q l f| := by
  unfold panMaxL
  dsimp only []
  rw [dif_pos hS]
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
  exact Finset.single_le_sum (fun l' hl' => abs_nonneg (panDistributionSum y X q l' f)) hl

/-- The `y`-maximum `panMaxY` is bounded by the sum of
the individual `panMaxL` values. -/
theorem panMaxY_le_sum (X q x : ℕ) (f : ℕ → ℝ) :
    panMaxY X q x f ≤ ∑ y ∈ Finset.range (x + 1), panMaxL y X q f := by
  unfold panMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact Finset.single_le_sum (fun y' hy' => panMaxL_nonneg y' X q f) hy

/-- Combined bound:
`panMaxY ≤ Σ_{y≤x} Σ_{(l,q)=1} |panDistributionSum y X q l f|`.
It replaces both maxima by finite sums for termwise Type I/II estimates. -/
theorem panMaxY_le_sum_abs (X q x : ℕ) (f : ℕ → ℝ)
    (hS : (unitResidues q).Nonempty) :
    panMaxY X q x f ≤
      ∑ y ∈ Finset.range (x + 1),
        ∑ l ∈ unitResidues q,
          |panDistributionSum y X q l f| := by
  exact le_trans (panMaxY_le_sum X q x f)
    (Finset.sum_le_sum (fun y hy => panMaxL_le_sum_abs y X q f hS))


/-! ## 4. Type I, Type II, and main-term input propositions

After a-absorption, the classical argument (Liu 2022 §III;
Halberstam--Richert 1974 Ch. 10) separates Vaughan V1 with `d ≤ u`,
V3 with `d > u, e > v`, and the signed small/middle/main-term
contribution involving `li` and the middle Vaughan term.
The `def ... : Prop` declarations below record bounds as explicit
analytic inputs; defining them does not prove them.

The relevant analytic ingredients are the Farey-point large sieve
`LargeSieve.Multiplicative.largeSieveRationalPoints`, the per-modulus
character bound `characterSieveModulus_le`, Vaughan's identity in
`Sieve.VaughanIdentity`, and prime-distribution main-term estimates.
The pure-`li` bound below is deliberately coarse and does not replace
the signed classical main-term estimate.
-/

/-- AP von Mangoldt count after a-absorption:
`Σ_{n≤y, n≡l [MOD q]} Λ(n)`, the AP version of `ψ`.
Applying `vaughanIdentity` to each `Λ n` supplies the Type I/II
pieces `apV1` and `apV3` together with the small and middle terms. -/
noncomputable def apVonMangoldt (y q l : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then Λ n else 0

/-- **Type I piece** (Vaughan V1):
`Σ_{n≤y, n≡l [MOD q]} Σ_{d|n, d≤u} μ(d)·log(n/d)`. -/
noncomputable def apV1 (y q l u : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanFirst n u else 0

/-- **Type II piece** (Vaughan V3):
`Σ_{n≤y, n≡l [MOD q]} Σ_{d|n, u<d} Σ_{e|n/d, v<e} μ(d)·Λ(e)`. -/
noncomputable def apV3 (y q l u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanThird n u v else 0

/-- Weighted piece before maxima:
`Σ_{1≤a≤X, (a,q)=1} f(a)·g(y/a,q,l·a⁻¹ mod q)`.
This is the a-absorbed expression for any piece `g`.
Only positive `a` occur; the zero term is separated in
`panDistributionSum_eq_weighted`. -/
noncomputable def panPieceSum (y X q l : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * g (y / a) q (natInvMod q a * l % q) else 0

/-- Residue maximum of a weighted piece, mirroring `panMaxL`. -/
noncomputable def panPieceMaxL (y X q : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  let S : Finset ℕ := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |panPieceSum y X q l f g|)).max' (Finset.image_nonempty.mpr h)
  else 0

@[simp] theorem panPieceMaxL_zero (y X : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    panPieceMaxL y X 0 f g = 0 := by
  simp [panPieceMaxL]

@[simp] theorem panPieceMaxL_one (y X : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    panPieceMaxL y X 1 f g = |panPieceSum y X 1 0 f g| := by
  simp [panPieceMaxL]

/-- Truncation maximum of a weighted piece, mirroring `panMaxY`. -/
noncomputable def panPieceMaxY (X q x : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

@[simp] theorem panPieceMaxY_zero (X x : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    panPieceMaxY X 0 x f g = 0 := by
  unfold panPieceMaxY
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    simp
  · simpa using Finset.le_max'
      ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X 0 f g))
      (panPieceMaxL 0 X 0 f g) (Finset.mem_image.mpr ⟨0, by simp, rfl⟩)

theorem panPieceMaxY_one (X x : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    panPieceMaxY X 1 x f g =
      ((Finset.range (x + 1)).image
        (fun y => |panPieceSum y X 1 0 f g|)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  simp only [panPieceMaxY, panPieceMaxL_one]

/-- **Type I weighted-bound proposition**: for each `A > 0`, there
exist `C > 0`, `B`, and `x₀` such that for every `X ≥ x₀`, with
`Q = (xX)^{1/2}/log^B(xX)`,
`Σ_{q≤Q} μ²(q)·3^{ω(q)}·max_{y≤xX} max_{(l,q)=1}
 |Σ_{1≤a≤X, (a,q)=1} f(a)·apV1(y/a;q,l·a⁻¹;u)/log(y/a)|
 ≤ C·xX/log^A(xX)`.
The classical small-factor argument uses character expansion and a
Farey-point large-sieve mean estimate (Liu §III Lemma 1; HR 1974 Ch. 10).
This declaration is for fixed `x,f,u`; it does not establish
uniformity over all `|f| ≤ 1`, which requires additional support
conditions as discussed in `LargeSieve/PanTypeIAssembly.lean`. -/
def PanTypeIWeightedBound (x f : ℕ → ℝ) (u : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apV1 y q l u / Real.log (y : ℝ)) ≤
        C * x X / (log (x X)) ^ A

/-- **Type II weighted-bound proposition** for the bilinear Vaughan V3
piece. The classical argument bounds bilinear expressions with
`|α|, |β| ≤ 1` using a large-sieve mean estimate on Farey points
(`largeSieveRationalPoints`) for
`Σ_{q≤Q} Σ_{(l,q)=1} |Σ α(d)β(e)·e(de·l/q)|²`,
then applies Cauchy--Schwarz (Liu §III; Montgomery's mean-value theorem).
The proposition below is an input, not a proof of that uniform estimate. -/
def PanTypeIIWeightedBound (x f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) ≤
        C * x X / (log (x X)) ^ A

/-- **Pure main-term weighted bound, polylogarithmic form**:
`Σ_{q≤Q} μ²(q)·3^{ω(q)}·max |Σ_{(a,q)=1} f(a)·li(y/a)/φ(q)|
 ≤ C·xX·(log xX)^{A+7}`.
Classically, subtraction of the sieve main term
`x/log x·∏(1-ν(p))` leaves `O(x/log^A x)`
(Liu 2022 §III; HR 1974 Ch. 10).
That requires a sieve-product object and PNT-level main-term input
such as `PrimeDistribution.primeCounting_asymptotic_real`, not just
the elementary absolute-value chain here.

The present coarse bound uses a larger log power to absorb a
fixed degree-7 polylogarithmic factor (`PanMainTerm.lean` §6).
`PanMainTermBound.of_sieveBound` reduces it to `PanMainTermSieveBound`,
which follows from `PanMainSieveAbsorption` under its scale-domination
hypothesis. The classical signed logarithmic-saving main-term input
is a separate requirement. -/
def PanMainTermBound (x f : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) ≤
        C * x X * (log (x X)) ^ (A + 7)


/-! ## 5. Type I reduction to a character mean

The finite chain for the small-factor V1 piece (`d ≤ u`) is:

```text
apV1 -- charSum_ap --> V_χ(y,u) = Σ_{n≤y} vaughanFirst(n,u)·χ(n)
     -- |apV1| ≤ φ(q)⁻¹·Σ_χ ‖V_χ‖, |χ(l)| = 1 --> termwise triangle bound
     -- residue-independent bound --> panPieceMaxL ≤ panTypeIDistributionSum
     -- maximum over y --> panPieceMaxY ≤ panTypeIMeanValueMaxY
     -- nonnegative weights --> PanTypeICharacterMeanValue → PanTypeIWeightedBound.
```

The only analytic input to this implication is
`PanTypeICharacterMeanValue`. The classical approach uses a
multiplicative large-sieve mean for `Σ_χ‖V_χ‖²` and
Cauchy--Schwarz (Liu 2022 §III Lemma 1; HR 1974 Ch. 10).
The implication does not assert that the input holds without
the required analytic and support conditions.
-/
noncomputable section

set_option linter.style.haveILetI false

/-- Complex Type I character sum:
`V_χ(y,u) = Σ_{n≤y} vaughanFirst(n,u)·χ(n)`. -/
noncomputable def panTypeIV1CharSum (q y u : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), (vaughanFirst n u : ℂ) * χ (n : ZMod q)

/-- A Dirichlet character has norm 1 on units: the image of a
finite-order unit is a root of unity. -/
theorem charValue_norm_eq_one {q : ℕ} {χ : DirichletCharacter ℂ q} {l : ℕ}
    (hl : IsUnit (l : ZMod q)) : ‖χ (l : ZMod q)‖ = 1 := by
  haveI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let n : ℕ := Fintype.card (ZMod q)ˣ
  have hn : n ≠ 0 := by
    exact ne_of_gt (Fintype.card_pos (α := (ZMod q)ˣ))
  have hpow_u : hl.unit ^ n = 1 := pow_card_eq_one (G := (ZMod q)ˣ) (x := hl.unit)
  have hpow_l : (l : ZMod q) ^ n = 1 := by
    have hspec : (l : ZMod q) = (hl.unit : ZMod q) := hl.unit_spec.symm
    rw [hspec]
    simpa using congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hpow_u
  have hpow_χ : (χ (l : ZMod q)) ^ n = 1 := by
    rw [← map_pow, hpow_l, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow_χ hn

/-- Complex character expansion:
`(apV1 y q l u : ℂ) = φ(q)⁻¹·Σ_χ star(χ(l))·V_χ(y,u)`
for unit `l`, directly from `charSum_ap`. -/
theorem apV1_charSum {q y u : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) :
    (apV1 y q l u : ℂ) = (Nat.totient q : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ := by
  unfold apV1 panTypeIV1CharSum
  have hcast : ((∑ n ∈ Finset.range (y + 1),
        (if n ≡ l [MOD q] then vaughanFirst n u else 0) : ℝ) : ℂ) =
      ∑ n ∈ Finset.range (y + 1),
        (vaughanFirst n u : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
    calc
      ((∑ n ∈ Finset.range (y + 1),
          (if n ≡ l [MOD q] then vaughanFirst n u else 0) : ℝ) : ℂ)
          = ∑ n ∈ Finset.range (y + 1),
              ((if n ≡ l [MOD q] then vaughanFirst n u else 0 : ℝ) : ℂ) := by
            exact map_sum Complex.ofRealHom
              (fun n => (if n ≡ l [MOD q] then vaughanFirst n u else 0 : ℝ)) (Finset.range (y + 1))
      _ = ∑ n ∈ Finset.range (y + 1),
            (vaughanFirst n u : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hmod : n ≡ l [MOD q] <;> simp [hmod]
  rw [hcast]
  exact AnalyticNumberTheory.LargeSieve.charSum_ap hq hl (fun n : ℕ => (vaughanFirst n u : ℂ)) y

/-- Pointwise bound for unit `l`:
`|apV1 y q l u| ≤ φ(q)⁻¹·Σ_χ ‖V_χ(y,u)‖`. -/
theorem apV1_abs_le {q y u : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) :
    |apV1 y q l u| ≤ (Nat.totient q : ℝ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q y u χ‖ := by
  have hnorm : ‖(apV1 y q l u : ℂ)‖ = |apV1 y q l u| := by
    exact RCLike.norm_ofReal (apV1 y q l u)
  rw [← hnorm]
  rw [apV1_charSum hq hl]
  calc
    ‖(Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖
        ≤ ‖(Nat.totient q : ℂ)⁻¹‖ * ‖∑ χ : DirichletCharacter ℂ q,
            star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖ := by
          exact norm_mul_le _ _
    _ = (Nat.totient q : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q,
            star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖ := by
          congr 1
          rw [norm_inv, Complex.norm_natCast]
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
            (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖panTypeIV1CharSum q y u χ‖ := by
          exact mul_le_mul_of_nonneg_left
            (by
              apply Finset.sum_le_sum
              intro χ hχ
              calc
                ‖star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖
                    ≤ ‖star (χ (l : ZMod q))‖ * ‖panTypeIV1CharSum q y u χ‖ := norm_mul_le _ _
                _ = ‖χ (l : ZMod q)‖ * ‖panTypeIV1CharSum q y u χ‖ := by
                      congr 1
                      simpa using (Complex.norm_conj (χ (l : ZMod q)))
                _ = ‖panTypeIV1CharSum q y u χ‖ := by
                      rw [charValue_norm_eq_one hl]
                      simp)
            (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))

/-- The inverse representative of a unit `a` times a unit `l`
is again a unit modulo `q`, as needed for the pointwise `apV1` bound. -/
lemma isUnit_natInvMod_mul_residue {q a l : ℕ} (hq : 0 < q) (hcop_a : a.Coprime q)
    (hl : l.Coprime q) : IsUnit (((natInvMod q a * l % q) : ℕ) : ZMod q) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hval : (((natInvMod q a * l % q : ℕ) : ZMod q)) =
      (((natInvMod q a * l : ℕ) : ZMod q)) := by
    have hz := ZMod.natCast_zmod_val (((natInvMod q a * l : ℕ) : ZMod q))
    simpa [ZMod.val_natCast] using hz
  rw [hval, Nat.cast_mul]
  have hni : (natInvMod q a : ZMod q) = (a⁻¹ : ZMod q) := by
    unfold natInvMod
    rw [dif_pos hcop_a]
    exact ZMod.natCast_zmod_val (a⁻¹ : ZMod q)
  have hui : IsUnit (a⁻¹ : ZMod q) := by
    refine ⟨⟨(a⁻¹ : ZMod q), (a : ZMod q), ?_, ?_⟩, rfl⟩
    · rw [mul_comm]
      exact ZMod.coe_mul_inv_eq_one a hcop_a
    · exact ZMod.coe_mul_inv_eq_one a hcop_a
  have hni_unit : IsUnit (natInvMod q a : ZMod q) := by
    rw [hni]
    exact hui
  have hl' : IsUnit (l : ZMod q) := (ZMod.isUnit_iff_coprime l q).mpr hl
  refine ⟨hni_unit.unit * hl'.unit, ?_⟩
  simp [Units.val_mul]

/-- **Type I character-mean expression**: for each `y`, the
a-absorbed weighted piece reduces to
`Σ_{1≤a≤X} |f(a)|/|log(y/a)| · Σ_χ ‖V_χ(y/a,u)‖`. -/
noncomputable def panTypeIDistributionSum (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
      ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖

/-- The distribution sum is nonnegative. -/
theorem panTypeIDistributionSum_nonneg (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    0 ≤ panTypeIDistributionSum y X q f u := by
  unfold panTypeIDistributionSum
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _))
    (Finset.sum_nonneg (fun χ hχ => norm_nonneg _))

/-- Termwise Type I triangle bound: for coprime `a` and unit `l`,
`|f(a)·apV1(y/a;q,a⁻¹l)/log(y/a)|
 ≤ |f(a)|/|log(y/a)| · Σ_χ ‖V_χ(y/a,u)‖`,
using the character-expansion bound and `φ(q)⁻¹ ≤ 1`. -/
private lemma panTypeI_summand_abs_le (y _X q : ℕ) (f : ℕ → ℝ) (u a l : ℕ)
    (hq : 0 < q) (hcop : a.Coprime q) (hl : l.Coprime q) :
    |f a * (apV1 (y / a) q (natInvMod q a * l % q) u / Real.log ((y / a : ℕ) : ℝ))|
      ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖ := by
  calc
    |f a * (apV1 (y / a) q (natInvMod q a * l % q) u / Real.log ((y / a : ℕ) : ℝ))|
        = |f a| * |apV1 (y / a) q (natInvMod q a * l % q) u / Real.log ((y / a : ℕ) : ℝ)| := by
          rw [abs_mul]
    _ = |f a| * (|apV1 (y / a) q (natInvMod q a * l % q) u| / |Real.log ((y / a : ℕ) : ℝ)|) := by
          rw [abs_div]
    _ ≤ |f a| * (((Nat.totient q : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) /
            |Real.log ((y / a : ℕ) : ℝ)|) := by
          have h1 : |apV1 (y / a) q (natInvMod q a * l % q) u| ≤
              (Nat.totient q : ℝ)⁻¹ *
                ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖ :=
            apV1_abs_le (q := q) (y := y / a) (u := u) hq (isUnit_natInvMod_mul_residue hq hcop hl)
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (abs_nonneg _)) (abs_nonneg _)
    _ = |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ((Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) := by
          ring
    _ ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) := by
          have hqpos : 0 < (Nat.totient q : ℝ) := by
            exact_mod_cast (Nat.totient_pos.mpr hq)
          have hq1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (Nat.totient_pos.mpr hq))
          have hφ : (Nat.totient q : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hqpos).mpr hq1
          have hS : 0 ≤ (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) := by
            apply Finset.sum_nonneg
            intro χ hχ
            exact norm_nonneg _
          have hPhiS : (Nat.totient q : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) ≤
              (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) := by
            simpa using (mul_le_mul_of_nonneg_right hφ hS)
          exact mul_le_mul_of_nonneg_left hPhiS
            (div_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **Residue-uniform Type I reduction**: for unit `l`,
`|panPieceSum y X q l f g|` is bounded by
`panTypeIDistributionSum`, independently of `l`. -/
theorem panPieceSum_typeI_abs_le (y X q : ℕ) (f : ℕ → ℝ) (u l : ℕ) (hq : 0 < q)
    (hl : l.Coprime q) :
    |panPieceSum y X q l f (fun y' q' l' => apV1 y' q' l' u / Real.log (y' : ℝ))|
      ≤ panTypeIDistributionSum y X q f u := by
  calc
    |panPieceSum y X q l f (fun y' q' l' => apV1 y' q' l' u / Real.log (y' : ℝ))|
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |if a.Coprime q then
              f a * (apV1 (y / a) q (natInvMod q a * l % q) u / Real.log ((y / a : ℕ) : ℝ))
            else 0| := by
          unfold panPieceSum
          exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
            ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖ := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases hcop : a.Coprime q
          · rw [if_pos hcop]
            exact panTypeI_summand_abs_le y X q f u a l hq hcop hl
          · have hnonneg : 0 ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
                ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖ := by
              exact mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _))
                (Finset.sum_nonneg (fun χ hχ => norm_nonneg _))
            simp [hcop]
            exact hnonneg

/-- **Residue-maximum reduction**:
`panPieceMaxL ≤ panTypeIDistributionSum`, since the bound is
independent of the residue. -/
theorem panPieceMaxL_le_typeIDistributionSum (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    panPieceMaxL y X q f (fun y' q' l' => apV1 y' q' l' u / Real.log (y' : ℝ)) ≤
      panTypeIDistributionSum y X q f u := by
  unfold panPieceMaxL
  by_cases hS : (unitResidues q).Nonempty
  · dsimp only []
    rw [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hlS : l ∈ unitResidues q := hl
    have hl' : l.Coprime q := (Finset.mem_filter.mp hlS).2
    have hlrange : l ∈ Finset.range q := (Finset.mem_filter.mp hlS).1
    have hq : 0 < q := by
      have hlq : l < q := Finset.mem_range.mp hlrange
      omega
    exact panPieceSum_typeI_abs_le y X q f u l hq hl'
  · rw [dif_neg hS]
    exact panTypeIDistributionSum_nonneg y X q f u

/-- Maximum over `y` of the character-mean expression,
mirroring `panPieceMaxY`. -/
noncomputable def panTypeIMeanValueMaxY (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panTypeIDistributionSum y X q f u)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **Truncation-maximum reduction**:
`panPieceMaxY ≤ panTypeIMeanValueMaxY`, by maximizing the
pointwise bound `panPieceMaxL ≤ panTypeIDistributionSum`. -/
theorem panPieceMaxY_le_typeIMeanValueMaxY (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    panPieceMaxY X q x f (fun y' q' l' => apV1 y' q' l' u / Real.log (y' : ℝ)) ≤
      panTypeIMeanValueMaxY X q x f u := by
  unfold panPieceMaxY panTypeIMeanValueMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact le_trans (panPieceMaxL_le_typeIDistributionSum y X q f u)
    (Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panTypeIDistributionSum y X q f u))
      (x := panTypeIDistributionSum y X q f u)
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩))

/-- **Type I character-mean input** under `|f| ≤ 1`, with weight
`3^{ω(q)}`. It is the remaining analytic hypothesis in the
reduction to `PanTypeIWeightedBound`. The classical approach uses
a multiplicative large-sieve mean for `Σ_χ‖V_χ‖²` and
Cauchy--Schwarz; this definition does not establish a uniform
estimate for every bounded `f`. -/
def PanTypeICharacterMeanValue (x : ℕ → ℝ) (f : ℕ → ℝ) (u : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panTypeIMeanValueMaxY X q (Nat.floor (x X)) f u ≤
          C * x X / (log (x X)) ^ A

/-- **Type I reduction**:
`PanTypeICharacterMeanValue → PanTypeIWeightedBound`.
Character expansion, pointwise estimates, both maximum reductions,
and weight monotonicity are proved here; the character mean itself
remains the analytic hypothesis. -/
theorem PanTypeIWeightedBound.of_characterMeanValue {x : ℕ → ℝ} {f : ℕ → ℝ} {u : ℕ} :
    PanTypeICharacterMeanValue x f u → PanTypeIWeightedBound x f u := by
  intro hP
  rcases hP with ⟨hfb, hBound⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apV1 y q l u / Real.log (y : ℝ)))
        ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panTypeIMeanValueMaxY X q (Nat.floor (x X)) f u := by
          apply Finset.sum_le_sum
          intro q hq
          have hw : 0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
            exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_left
            (panPieceMaxY_le_typeIMeanValueMaxY X q (Nat.floor (x X)) f u) hw
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX

/-! ## 5.1 Type I square-mean reduction

The proposed analytic chain (Liu 2022 §III Lemma 1; HR 1974 Ch. 10) is

```text
Σ_{q≤Q} μ²(q)·3^{ω(q)}·max_{y≤xX}
  Σ_{1≤a≤X} |f(a)|/|log(y/a)|·Σ_χ ‖V_χ(y/a)‖
≤ Σ_{q≤Q} μ²(q)·3^{ω(q)}·√φ(q)·max_{y≤xX}
  Σ_{1≤a≤X} |f(a)|/|log(y/a)|·√(Σ_χ ‖V_χ(y/a)‖²).
```

The inequality follows from Cauchy--Schwarz and the character count
`φ(q)`. A further logarithmic-saving bound would require a
multiplicative large-sieve mean, a square-sum estimate for
`vaughanFirst`, totient-weight estimates, and the outer `(y,a)` sum.

This section proves the finite components:
`panTypeI_charAbsSum_le_cs`, using
`DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`;
`panTypeIDistributionSum_le_csWeighted`;
`panTypeIMeanValueMaxY_le_charSqrtMeanMaxY`;
`panTypeI_weight_nonneg`;
`panTypeICharSqrtMeanMaxY_le_of_abs_le_one`; and
`PanTypeICharacterMeanValue.of_sieveBound`.
The input is `panTypeICharMeanSieveBound`, with the separate
square-mean proposition `panTypeICharSquareMeanBound`.

Primitive-character decomposition and Gauss sums are essential in
the classical Bombieri--Davenport theorem. Directly summing
all-character Parseval bounds does not work: for `a_n ≡ 1`,
`Q = 2`, and large `N`,
`Σ_q (q/φ(q))Σ_χ |S(χ)|² ≈ 3N²/2`,
whereas `C(N,1/4)·N = (N+64)·N`.
See `Multiplicative.lean`; the all-character input is not a
consequence of the primitive-character theorem alone.
-/

/-- Character-sum L² expression `t_q(m) = Σ_χ ‖V_χ(m)‖²`,
the natural square-mean object for the multiplicative large sieve. -/
noncomputable def panTypeICharSqSum (q m u : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖ ^ 2

/-- **Cauchy--Schwarz**:
`Σ_χ ‖V_χ(m)‖ ≤ √φ(q)·√(Σ_χ ‖V_χ(m)‖²)`,
using the character count `φ(q)` and `(Σa_i)² ≤ n·Σa_i²`. -/
theorem panTypeI_charAbsSum_le_cs (q m u : ℕ) (hq : 0 < q) :
    (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖) ≤
      Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeICharSqSum q m u) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    AnalyticNumberTheory.LargeSieve.complexHasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ)
      (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hcs : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖) ^ 2 ≤
      (Nat.totient q : ℝ) * panTypeICharSqSum q m u := by
    calc
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖) ^ 2
          ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
              (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖ ^ 2) := by
            simpa using (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
              (f := fun χ : DirichletCharacter ℂ q => ‖panTypeIV1CharSum q m u χ‖))
      _ = (Nat.totient q : ℝ) * panTypeICharSqSum q m u := by
            rw [hcard, panTypeICharSqSum]
  have hS : 0 ≤ panTypeICharSqSum q m u := by
    unfold panTypeICharSqSum
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hφ : 0 ≤ (Nat.totient q : ℝ) := by positivity
  have hsq : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖) ^ 2 ≤
      (Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeICharSqSum q m u)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hφ, Real.sq_sqrt hS]
    exact hcs
  exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Termwise weighted Cauchy--Schwarz in the distribution sum:
`panTypeIDistributionSum y X q f u
 ≤ √φ(q)·Σ_{1≤a≤X} |f(a)|/|log(y/a)|·√t_q(y/a)`. -/
theorem panTypeIDistributionSum_le_csWeighted (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) (hq : 0 < q) :
    panTypeIDistributionSum y X q f u ≤
      Real.sqrt (Nat.totient q : ℝ) *
        (∑ a ∈ Finset.Icc 1 X,
          |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u)) := by
  unfold panTypeIDistributionSum
  calc
    (∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖)
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
              (Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeICharSqSum q (y / a) u)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (panTypeI_charAbsSum_le_cs q (y / a) u hq)
            (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = Real.sqrt (Nat.totient q : ℝ) *
          (∑ a ∈ Finset.Icc 1 X,
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring

/-- The fixed-`y` slice of the weighted square-mean expression:
`W(y) = Σ_{1≤a≤X} |f(a)|/|log(y/a)|·√t_q(y/a)`. -/
noncomputable def panTypeICharSqrtMean (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u)

/-- Maximum over `y` of the weighted square-mean expression,
mirroring `panTypeIMeanValueMaxY`. -/
noncomputable def panTypeICharSqrtMeanMaxY (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panTypeICharSqrtMean y X q f u)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **Truncation-maximum reduction**:
`panTypeIMeanValueMaxY ≤ √φ(q)·panTypeICharSqrtMeanMaxY`,
by maximizing the weighted Cauchy--Schwarz bound. -/
theorem panTypeIMeanValueMaxY_le_charSqrtMeanMaxY (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) (hq : 0 < q) :
    panTypeIMeanValueMaxY X q x f u ≤
      Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u := by
  unfold panTypeIMeanValueMaxY panTypeICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panTypeIDistributionSum y X q f u
        ≤ Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMean y X q f u :=
          panTypeIDistributionSum_le_csWeighted y X q f u hq
    _ ≤ Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u := by
          exact mul_le_mul_of_nonneg_left
            (Finset.le_max'
              (s := (Finset.range (x + 1)).image (fun y => panTypeICharSqrtMean y X q f u))
              (x := panTypeICharSqrtMean y X q f u)
              (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
            (Real.sqrt_nonneg _)

/-- Nonnegative weight: `μ²(q)·3^{ω(q)} ≥ 0`. -/
theorem panTypeI_weight_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)

/-- Weighted per-modulus reduction:
`w_q·M_q ≤ w_q·√φ(q)·W_q`; the weight is zero at `q = 0`. -/
private lemma panTypeI_weighted_maxY_le_weighted_sqrtMean (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIMeanValueMaxY X q x f u ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u := by
  by_cases hq0 : q = 0
  · subst q
    have hμ : (μ 0 : ℤ) = 0 := by
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree (not_squarefree_zero)
    simp [hμ, Nat.totient_zero]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    calc
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIMeanValueMaxY X q x f u
          ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              (Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u) := by
            exact mul_le_mul_of_nonneg_left
              (panTypeIMeanValueMaxY_le_charSqrtMeanMaxY X q x f u hq)
              (panTypeI_weight_nonneg q)
      _ = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u := by
            ring

/-- Under `|f(a)| ≤ 1`, the maximum weighted square-mean expression
is bounded by its version with `f ≡ 1`. -/
theorem panTypeICharSqrtMeanMaxY_le_of_abs_le_one (X q x : ℕ) (u : ℕ) {f : ℕ → ℝ}
    (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    panTypeICharSqrtMeanMaxY X q x f u ≤ panTypeICharSqrtMeanMaxY X q x (fun _ : ℕ => 1) u := by
  unfold panTypeICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panTypeICharSqrtMean y X q f u
        ≤ panTypeICharSqrtMean y X q (fun _ : ℕ => 1) u := by
          unfold panTypeICharSqrtMean
          apply Finset.sum_le_sum
          intro a ha
          have hdiv : |f a| / |Real.log ((y / a : ℕ) : ℝ)| ≤
              (1 : ℝ) / |Real.log ((y / a : ℕ) : ℝ)| :=
            div_le_div_of_nonneg_right (hfb a) (abs_nonneg _)
          have hsqrt : 0 ≤ Real.sqrt (panTypeICharSqSum q (y / a) u) := Real.sqrt_nonneg _
          calc
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u)
                ≤ (1 : ℝ) / |Real.log ((y / a : ℕ) : ℝ)| *
                    Real.sqrt (panTypeICharSqSum q (y / a) u) :=
                  mul_le_mul_of_nonneg_right hdiv hsqrt
            _ = |(1 : ℝ)| / |Real.log ((y / a : ℕ) : ℝ)| *
                  Real.sqrt (panTypeICharSqSum q (y / a) u) := by norm_num
    _ ≤ panTypeICharSqrtMeanMaxY X q x (fun _ : ℕ => 1) u := by
          exact Finset.le_max'
            (s := (Finset.range (x + 1)).image (fun y => panTypeICharSqrtMean y X q (fun _ : ℕ => 1) u))
            (x := panTypeICharSqrtMean y X q (fun _ : ℕ => 1) u)
            (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

/-- **Type I square-mean assembly input**: under `|f| ≤ 1`, for
each `A > 0` there are `C > 0`, `B`, and `x₀` such that
for every `X ≥ x₀`, with `Q = (xX)^{1/2}/log^B(xX)`,
`Σ_{q≤Q} μ²(q)·3^{ω(q)}·√φ(q)·max_{y≤xX}
 Σ_{1≤a≤X} |f(a)|/|log(y/a)|·√(Σ_χ ‖V_χ(y/a)‖²)
 ≤ C·xX/log^A(xX)`.

This is the remaining hypothesis in the reduction to
`PanTypeICharacterMeanValue`. The classical route combines the
multiplicative large sieve, Cauchy--Schwarz in `q`, a square-sum
bound for `vaughanFirst`, totient weights, and the outer `(y,a)` sum
(Liu 2022 §III Lemma 1; HR 1974 Ch. 10).
The all-character sum is not obtained by direct Parseval stacking;
primitive-character and Gauss-sum analysis is separate
(`Multiplicative.lean`). Nor does this definition prove uniformity
for all bounded `f`; see the support obstruction in `PanTypeIAssembly.lean`. -/
def panTypeICharMeanSieveBound (x : ℕ → ℝ) (f : ℕ → ℝ) (u : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q (Nat.floor (x X)) f u ≤
          C * x X / (log (x X)) ^ A

/-- **Type I all-character square-mean proposition**:
`Σ_{q≤Q} μ²(q)·3^{ω(q)}·Σ_χ ‖V_χ(m)‖²
 ≤ C·(m+Q²)·Σ_{n≤m} vaughanFirst(n,u)²`.

The classical Bombieri--Davenport theorem (Montgomery 1971 Ch. 1;
Iwaniec--Kowalski 2004 Ch. 7) uses primitive characters and
Gauss sums `|τ(χ)|² = q`; direct all-character Parseval stacking
fails, as explained in `Multiplicative.lean`.
The proposed further assembly also calls for a square-sum estimate
for `vaughanFirst` (classically of `m·log³(m+2)` shape),
`Σ_{q≤Q} μ²(q)3^{ω(q)}φ(q) ≪ Q²·log³(Q+2)`,
and a uniform outer-sum bound of the form
`Σ_{a≤X} |f(a)|/|log(y/a)|·(y/a)^{1/2}·(y/a+Q²)^{1/2}·log³`
for `y ≤ xX`, followed by Cauchy--Schwarz in `q`.
The maximum must remain outside the modulus-dependent estimates.
These requirements describe a proposed route to
`panTypeICharMeanSieveBound`, not a theorem supplied by this definition. -/
def panTypeICharSquareMeanBound (u : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, ∀ m : ℕ,
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeICharSqSum q m u) ≤
      C * ((m : ℝ) + (Q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2)

/-- **Type I square-mean reduction**:
`panTypeICharMeanSieveBound → PanTypeICharacterMeanValue`.
Cauchy--Schwarz, the maximum reduction, nonnegative weights, and
the zero weight at `q = 0` are proved here; the supplied mean
estimate is the sole analytic input. -/
theorem PanTypeICharacterMeanValue.of_sieveBound {x : ℕ → ℝ} {f : ℕ → ℝ} {u : ℕ}
    (hS : panTypeICharMeanSieveBound x f u) : PanTypeICharacterMeanValue x f u := by
  rcases hS with ⟨hfb, hBound⟩
  refine ⟨hfb, ?_⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panTypeIMeanValueMaxY X q (Nat.floor (x X)) f u)
        ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q (Nat.floor (x X)) f u := by
          apply Finset.sum_le_sum
          intro q hq
          exact panTypeI_weighted_maxY_le_weighted_sqrtMean X q (Nat.floor (x X)) f u
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX


/-! ## 5.2 Type II character and square-mean reductions

For V3 with `u < d, v < e`, the finite chain parallels §§5--5.1,
replacing `apV1`, `vaughanFirst`, and `panTypeI*` by
`apV3`, `vaughanThird`, and `panTypeII*`:

```text
apV3 -- charSum_ap --> V_χ(y,u,v) = Σ_{n≤y} vaughanThird(n,u,v)·χ(n)
     -- |apV3| ≤ φ(q)⁻¹·Σ_χ ‖V_χ‖ --> termwise triangle bound
     -- residue-uniform bound --> panPieceMaxL ≤ panTypeIIDistributionSum
     -- maximum over y --> panPieceMaxY ≤ panTypeIIMeanValueMaxY
     -- nonnegative weights --> PanTypeIICharacterMeanValue → PanTypeIIWeightedBound
     -- Cauchy--Schwarz, character count φ(q) --> panTypeIICharSqSum / panTypeIICharSqrtMeanMaxY
     -- panTypeIICharMeanSieveBound --> PanTypeIICharacterMeanValue.of_sieveBound.
```

The remaining analytic input is `panTypeIICharMeanSieveBound`.
The classical bilinear route combines a multiplicative large-sieve
mean for `Σ_χ‖V_χ‖²`, a square-sum bound for `vaughanThird`,
and Cauchy--Schwarz in `q` (Liu 2022 §III; Montgomery 1971 Ch. 1).
All finite implications here are conditional on that input.
-/

/-- Complex Type II character sum:
`V_χ(y,u,v) = Σ_{n≤y} vaughanThird(n,u,v)·χ(n)`. -/
noncomputable def panTypeIIV3CharSum (q y u v : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), (vaughanThird n u v : ℂ) * χ (n : ZMod q)

/-- Complex character expansion:
`(apV3 y q l u v : ℂ) = φ(q)⁻¹·Σ_χ star(χ(l))·V_χ(y,u,v)`
for unit `l`, directly from `charSum_ap`. -/
theorem apV3_charSum {q y u v : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) :
    (apV3 y q l u v : ℂ) = (Nat.totient q : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ := by
  unfold apV3 panTypeIIV3CharSum
  have hcast : ((∑ n ∈ Finset.range (y + 1),
        (if n ≡ l [MOD q] then vaughanThird n u v else 0) : ℝ) : ℂ) =
      ∑ n ∈ Finset.range (y + 1),
        (vaughanThird n u v : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
    calc
      ((∑ n ∈ Finset.range (y + 1),
          (if n ≡ l [MOD q] then vaughanThird n u v else 0) : ℝ) : ℂ)
          = ∑ n ∈ Finset.range (y + 1),
              ((if n ≡ l [MOD q] then vaughanThird n u v else 0 : ℝ) : ℂ) := by
            exact map_sum Complex.ofRealHom
              (fun n => (if n ≡ l [MOD q] then vaughanThird n u v else 0 : ℝ)) (Finset.range (y + 1))
      _ = ∑ n ∈ Finset.range (y + 1),
            (vaughanThird n u v : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hmod : n ≡ l [MOD q] <;> simp [hmod]
  rw [hcast]
  exact AnalyticNumberTheory.LargeSieve.charSum_ap hq hl (fun n : ℕ => (vaughanThird n u v : ℂ)) y

/-- Pointwise bound for unit `l`:
`|apV3 y q l u v| ≤ φ(q)⁻¹·Σ_χ ‖V_χ(y,u,v)‖`. -/
theorem apV3_abs_le {q y u v : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) :
    |apV3 y q l u v| ≤ (Nat.totient q : ℝ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q y u v χ‖ := by
  have hnorm : ‖(apV3 y q l u v : ℂ)‖ = |apV3 y q l u v| := by
    exact RCLike.norm_ofReal (apV3 y q l u v)
  rw [← hnorm]
  rw [apV3_charSum hq hl]
  calc
    ‖(Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖
        ≤ ‖(Nat.totient q : ℂ)⁻¹‖ * ‖∑ χ : DirichletCharacter ℂ q,
            star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖ := by
          exact norm_mul_le _ _
    _ = (Nat.totient q : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q,
            star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖ := by
          congr 1
          rw [norm_inv, Complex.norm_natCast]
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
            (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖panTypeIIV3CharSum q y u v χ‖ := by
          exact mul_le_mul_of_nonneg_left
            (by
              apply Finset.sum_le_sum
              intro χ hχ
              calc
                ‖star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖
                    ≤ ‖star (χ (l : ZMod q))‖ * ‖panTypeIIV3CharSum q y u v χ‖ := norm_mul_le _ _
                _ = ‖χ (l : ZMod q)‖ * ‖panTypeIIV3CharSum q y u v χ‖ := by
                      congr 1
                      simpa using (Complex.norm_conj (χ (l : ZMod q)))
                _ = ‖panTypeIIV3CharSum q y u v χ‖ := by
                      rw [charValue_norm_eq_one hl]
                      simp)
            (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))

/-- **Type II character-mean expression**: for each `y`, the
a-absorbed weighted piece reduces to
`Σ_{1≤a≤X} |f(a)|/|log(y/a)| · Σ_χ ‖V_χ(y/a,u,v)‖`. -/
noncomputable def panTypeIIDistributionSum (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
      ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖

/-- The distribution sum is nonnegative. -/
theorem panTypeIIDistributionSum_nonneg (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ panTypeIIDistributionSum y X q f u v := by
  unfold panTypeIIDistributionSum
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _))
    (Finset.sum_nonneg (fun χ hχ => norm_nonneg _))

/-- Termwise Type II triangle bound: for coprime `a` and unit `l`,
`|f(a)·apV3(y/a;q,a⁻¹l;u,v)/log(y/a)|
 ≤ |f(a)|/|log(y/a)| · Σ_χ ‖V_χ(y/a,u,v)‖`,
using the character-expansion bound and `φ(q)⁻¹ ≤ 1`. -/
private lemma panTypeII_summand_abs_le (y _X q : ℕ) (f : ℕ → ℝ) (u v a l : ℕ)
    (hq : 0 < q) (hcop : a.Coprime q) (hl : l.Coprime q) :
    |f a * (apV3 (y / a) q (natInvMod q a * l % q) u v / Real.log ((y / a : ℕ) : ℝ))|
      ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖ := by
  calc
    |f a * (apV3 (y / a) q (natInvMod q a * l % q) u v / Real.log ((y / a : ℕ) : ℝ))|
        = |f a| * |apV3 (y / a) q (natInvMod q a * l % q) u v / Real.log ((y / a : ℕ) : ℝ)| := by
          rw [abs_mul]
    _ = |f a| * (|apV3 (y / a) q (natInvMod q a * l % q) u v| / |Real.log ((y / a : ℕ) : ℝ)|) := by
          rw [abs_div]
    _ ≤ |f a| * (((Nat.totient q : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) /
            |Real.log ((y / a : ℕ) : ℝ)|) := by
          have h1 : |apV3 (y / a) q (natInvMod q a * l % q) u v| ≤
              (Nat.totient q : ℝ)⁻¹ *
                ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖ :=
            apV3_abs_le (q := q) (y := y / a) (u := u) (v := v) hq
              (isUnit_natInvMod_mul_residue hq hcop hl)
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (abs_nonneg _)) (abs_nonneg _)
    _ = |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ((Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) := by
          ring
    _ ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) := by
          have hqpos : 0 < (Nat.totient q : ℝ) := by
            exact_mod_cast (Nat.totient_pos.mpr hq)
          have hq1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (Nat.totient_pos.mpr hq))
          have hφ : (Nat.totient q : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hqpos).mpr hq1
          have hS : 0 ≤ (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) := by
            apply Finset.sum_nonneg
            intro χ hχ
            exact norm_nonneg _
          have hPhiS : (Nat.totient q : ℝ)⁻¹ *
                (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) ≤
              (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) := by
            simpa using (mul_le_mul_of_nonneg_right hφ hS)
          exact mul_le_mul_of_nonneg_left hPhiS
            (div_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **Residue-uniform Type II reduction**: for unit `l`,
`|panPieceSum y X q l f g|` is bounded by
`panTypeIIDistributionSum`, independently of `l`. -/
theorem panPieceSum_typeII_abs_le (y X q : ℕ) (f : ℕ → ℝ) (u v l : ℕ) (hq : 0 < q)
    (hl : l.Coprime q) :
    |panPieceSum y X q l f (fun y' q' l' => apV3 y' q' l' u v / Real.log (y' : ℝ))|
      ≤ panTypeIIDistributionSum y X q f u v := by
  calc
    |panPieceSum y X q l f (fun y' q' l' => apV3 y' q' l' u v / Real.log (y' : ℝ))|
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |if a.Coprime q then
              f a * (apV3 (y / a) q (natInvMod q a * l % q) u v / Real.log ((y / a : ℕ) : ℝ))
            else 0| := by
          unfold panPieceSum
          exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
            ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖ := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases hcop : a.Coprime q
          · rw [if_pos hcop]
            exact panTypeII_summand_abs_le y X q f u v a l hq hcop hl
          · have hnonneg : 0 ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
                ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖ := by
              exact mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _))
                (Finset.sum_nonneg (fun χ hχ => norm_nonneg _))
            simp [hcop]
            exact hnonneg

/-- **Residue-maximum reduction**:
`panPieceMaxL ≤ panTypeIIDistributionSum`, since the bound
is independent of the residue. -/
theorem panPieceMaxL_le_typeIIDistributionSum (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    panPieceMaxL y X q f (fun y' q' l' => apV3 y' q' l' u v / Real.log (y' : ℝ)) ≤
      panTypeIIDistributionSum y X q f u v := by
  unfold panPieceMaxL
  by_cases hS : (unitResidues q).Nonempty
  · dsimp only []
    rw [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hlS : l ∈ unitResidues q := hl
    have hl' : l.Coprime q := (Finset.mem_filter.mp hlS).2
    have hlrange : l ∈ Finset.range q := (Finset.mem_filter.mp hlS).1
    have hq : 0 < q := by
      have hlq : l < q := Finset.mem_range.mp hlrange
      omega
    exact panPieceSum_typeII_abs_le y X q f u v l hq hl'
  · rw [dif_neg hS]
    exact panTypeIIDistributionSum_nonneg y X q f u v

/-- Maximum over `y` of the Type II character-mean expression,
mirroring `panTypeIMeanValueMaxY`. -/
noncomputable def panTypeIIMeanValueMaxY (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panTypeIIDistributionSum y X q f u v)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **Truncation-maximum reduction**:
`panPieceMaxY ≤ panTypeIIMeanValueMaxY`, by maximizing the
pointwise bound `panPieceMaxL ≤ panTypeIIDistributionSum`. -/
theorem panPieceMaxY_le_typeIIMeanValueMaxY (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    panPieceMaxY X q x f (fun y' q' l' => apV3 y' q' l' u v / Real.log (y' : ℝ)) ≤
      panTypeIIMeanValueMaxY X q x f u v := by
  unfold panPieceMaxY panTypeIIMeanValueMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact le_trans (panPieceMaxL_le_typeIIDistributionSum y X q f u v)
    (Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panTypeIIDistributionSum y X q f u v))
      (x := panTypeIIDistributionSum y X q f u v)
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩))

/-- **Type II character-mean input** under `|f| ≤ 1`, with weight
`3^{ω(q)}`. It is the remaining analytic hypothesis in the
reduction to `PanTypeIIWeightedBound`. The classical approach uses
a multiplicative large-sieve mean for `Σ_χ‖V_χ‖²` and
Cauchy--Schwarz; this definition does not itself prove the estimate. -/
def PanTypeIICharacterMeanValue (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panTypeIIMeanValueMaxY X q (Nat.floor (x X)) f u v ≤
          C * x X / (log (x X)) ^ A

/-- **Type II reduction**:
`PanTypeIICharacterMeanValue → PanTypeIIWeightedBound`.
Character expansion, pointwise estimates, both maximum reductions,
and weight monotonicity are proved here; the character mean itself
remains the analytic hypothesis. -/
theorem PanTypeIIWeightedBound.of_characterMeanValue {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ} :
    PanTypeIICharacterMeanValue x f u v → PanTypeIIWeightedBound x f u v := by
  intro hP
  rcases hP with ⟨hfb, hBound⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apV3 y q l u v / Real.log (y : ℝ)))
        ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panTypeIIMeanValueMaxY X q (Nat.floor (x X)) f u v := by
          apply Finset.sum_le_sum
          intro q hq
          have hw : 0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
            exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_left
            (panPieceMaxY_le_typeIIMeanValueMaxY X q (Nat.floor (x X)) f u v) hw
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX

/-- Character-sum L² expression `t_q(m) = Σ_χ ‖V_χ(m)‖²`,
the natural square-mean object for the multiplicative large sieve. -/
noncomputable def panTypeIICharSqSum (q m u v : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2

/-- **Cauchy--Schwarz**:
`Σ_χ ‖V_χ(m)‖ ≤ √φ(q)·√(Σ_χ ‖V_χ(m)‖²)`,
using the character count `φ(q)` and `(Σa_i)² ≤ n·Σa_i²`. -/
theorem panTypeII_charAbsSum_le_cs (q m u v : ℕ) (hq : 0 < q) :
    (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖) ≤
      Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeIICharSqSum q m u v) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    AnalyticNumberTheory.LargeSieve.complexHasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ)
      (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hcs : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖) ^ 2 ≤
      (Nat.totient q : ℝ) * panTypeIICharSqSum q m u v := by
    calc
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖) ^ 2
          ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
              (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2) := by
            simpa using (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
              (f := fun χ : DirichletCharacter ℂ q => ‖panTypeIIV3CharSum q m u v χ‖))
      _ = (Nat.totient q : ℝ) * panTypeIICharSqSum q m u v := by
            rw [hcard, panTypeIICharSqSum]
  have hS : 0 ≤ panTypeIICharSqSum q m u v := by
    unfold panTypeIICharSqSum
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hφ : 0 ≤ (Nat.totient q : ℝ) := by positivity
  have hsq : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖) ^ 2 ≤
      (Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeIICharSqSum q m u v)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hφ, Real.sq_sqrt hS]
    exact hcs
  exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Termwise weighted Cauchy--Schwarz:
`panTypeIIDistributionSum y X q f u v
 ≤ √φ(q)·Σ_{1≤a≤X} |f(a)|/|log(y/a)|·√t_q(y/a)`. -/
theorem panTypeIIDistributionSum_le_csWeighted (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hq : 0 < q) :
    panTypeIIDistributionSum y X q f u v ≤
      Real.sqrt (Nat.totient q : ℝ) *
        (∑ a ∈ Finset.Icc 1 X,
          |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v)) := by
  unfold panTypeIIDistributionSum
  calc
    (∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖)
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
              (Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeIICharSqSum q (y / a) u v)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (panTypeII_charAbsSum_le_cs q (y / a) u v hq)
            (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = Real.sqrt (Nat.totient q : ℝ) *
          (∑ a ∈ Finset.Icc 1 X,
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring

/-- The fixed-`y` slice of the weighted square-mean expression:
`W(y) = Σ_{1≤a≤X} |f(a)|/|log(y/a)|·√t_q(y/a)`. -/
noncomputable def panTypeIICharSqrtMean (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v)

/-- Maximum over `y` of the weighted square-mean expression,
mirroring `panTypeICharSqrtMeanMaxY`. -/
noncomputable def panTypeIICharSqrtMeanMaxY (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panTypeIICharSqrtMean y X q f u v)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **Truncation-maximum reduction**:
`panTypeIIMeanValueMaxY ≤ √φ(q)·panTypeIICharSqrtMeanMaxY`,
by maximizing the weighted Cauchy--Schwarz bound. -/
theorem panTypeIIMeanValueMaxY_le_charSqrtMeanMaxY (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hq : 0 < q) :
    panTypeIIMeanValueMaxY X q x f u v ≤
      Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v := by
  unfold panTypeIIMeanValueMaxY panTypeIICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panTypeIIDistributionSum y X q f u v
        ≤ Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMean y X q f u v :=
          panTypeIIDistributionSum_le_csWeighted y X q f u v hq
    _ ≤ Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v := by
          exact mul_le_mul_of_nonneg_left
            (Finset.le_max'
              (s := (Finset.range (x + 1)).image (fun y => panTypeIICharSqrtMean y X q f u v))
              (x := panTypeIICharSqrtMean y X q f u v)
              (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
            (Real.sqrt_nonneg _)

/-- Nonnegative weight: `μ²(q)·3^{ω(q)} ≥ 0`. -/
theorem panTypeII_weight_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)

/-- Weighted per-modulus reduction:
`w_q·M_q ≤ w_q·√φ(q)·W_q`; the weight is zero at `q = 0`. -/
private lemma panTypeII_weighted_maxY_le_weighted_sqrtMean (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIIMeanValueMaxY X q x f u v ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v := by
  by_cases hq0 : q = 0
  · subst q
    have hμ : (μ 0 : ℤ) = 0 := by
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree (not_squarefree_zero)
    simp [hμ, Nat.totient_zero]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    calc
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIIMeanValueMaxY X q x f u v
          ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              (Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v) := by
            exact mul_le_mul_of_nonneg_left
              (panTypeIIMeanValueMaxY_le_charSqrtMeanMaxY X q x f u v hq)
              (panTypeII_weight_nonneg q)
      _ = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v := by
            ring

/-- Under `|f(a)| ≤ 1`, the maximum weighted square-mean expression
is bounded by its version with `f ≡ 1`. -/
theorem panTypeIICharSqrtMeanMaxY_le_of_abs_le_one (X q x : ℕ) (u v : ℕ) {f : ℕ → ℝ}
    (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    panTypeIICharSqrtMeanMaxY X q x f u v ≤ panTypeIICharSqrtMeanMaxY X q x (fun _ : ℕ => 1) u v := by
  unfold panTypeIICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panTypeIICharSqrtMean y X q f u v
        ≤ panTypeIICharSqrtMean y X q (fun _ : ℕ => 1) u v := by
          unfold panTypeIICharSqrtMean
          apply Finset.sum_le_sum
          intro a ha
          have hdiv : |f a| / |Real.log ((y / a : ℕ) : ℝ)| ≤
              (1 : ℝ) / |Real.log ((y / a : ℕ) : ℝ)| :=
            div_le_div_of_nonneg_right (hfb a) (abs_nonneg _)
          have hsqrt : 0 ≤ Real.sqrt (panTypeIICharSqSum q (y / a) u v) := Real.sqrt_nonneg _
          calc
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v)
                ≤ (1 : ℝ) / |Real.log ((y / a : ℕ) : ℝ)| *
                    Real.sqrt (panTypeIICharSqSum q (y / a) u v) :=
                  mul_le_mul_of_nonneg_right hdiv hsqrt
            _ = |(1 : ℝ)| / |Real.log ((y / a : ℕ) : ℝ)| *
                  Real.sqrt (panTypeIICharSqSum q (y / a) u v) := by norm_num
    _ ≤ panTypeIICharSqrtMeanMaxY X q x (fun _ : ℕ => 1) u v := by
          exact Finset.le_max'
            (s := (Finset.range (x + 1)).image (fun y => panTypeIICharSqrtMean y X q (fun _ : ℕ => 1) u v))
            (x := panTypeIICharSqrtMean y X q (fun _ : ℕ => 1) u v)
            (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

/-- **Type II square-mean assembly input**: under `|f| ≤ 1`, for
each `A > 0` there are `C > 0`, `B`, and `x₀` such that for
every `X ≥ x₀`, with `Q = (xX)^{1/2}/log^B(xX)`,
`Σ_{q≤Q} μ²(q)·3^{ω(q)}·√φ(q)·max_{y≤xX}
 Σ_{1≤a≤X} |f(a)|/|log(y/a)|·√(Σ_χ ‖V_χ(y/a)‖²)
 ≤ C·xX/log^A(xX)`.
This is the remaining hypothesis in the reduction to
`PanTypeIICharacterMeanValue`. The classical bilinear route combines
the multiplicative large sieve, Cauchy--Schwarz in `q`, a square-sum
bound for `vaughanThird`, totient weights, and the outer `(y,a)` sum
(Liu 2022 §III; Montgomery 1971 Ch. 1; HR 1974 Ch. 10).
The definition is not an unconditional uniform estimate. -/
def panTypeIICharMeanSieveBound (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q (Nat.floor (x X)) f u v ≤
          C * x X / (log (x X)) ^ A

/-- **Type II all-character square-mean proposition**:
`Σ_{q≤Q} μ²(q)·3^{ω(q)}·Σ_χ ‖V_χ(m)‖²
 ≤ C·(m+Q²)·Σ_{n≤m} vaughanThird(n,u,v)²`.
The classical Bombieri--Davenport theorem (Montgomery 1971 Ch. 1;
Iwaniec--Kowalski 2004 Ch. 7) uses primitive-character decomposition
and Gauss sums. The bilinear Type II structure enters after expanding
Vaughan's identity in `d,e` (Liu 2022 §III).
This declaration records an input, not a proved all-character bound. -/
def panTypeIICharSquareMeanBound (u v : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, ∀ m : ℕ,
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIICharSqSum q m u v) ≤
      C * ((m : ℝ) + (Q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2)

/-- **Type II square-mean reduction**:
`panTypeIICharMeanSieveBound → PanTypeIICharacterMeanValue`.
Cauchy--Schwarz, the maximum reduction, nonnegative weights, and
the zero weight at `q = 0` are proved here; the supplied character
mean is the sole analytic input. -/
theorem PanTypeIICharacterMeanValue.of_sieveBound {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hS : panTypeIICharMeanSieveBound x f u v) : PanTypeIICharacterMeanValue x f u v := by
  rcases hS with ⟨hfb, hBound⟩
  refine ⟨hfb, ?_⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panTypeIIMeanValueMaxY X q (Nat.floor (x X)) f u v)
        ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q (Nat.floor (x X)) f u v := by
          apply Finset.sum_le_sum
          intro q hq
          exact panTypeII_weighted_maxY_le_weighted_sqrtMean X q (Nat.floor (x X)) f u v
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX

end

end AnalyticNumberTheory.Sieve
