import AnalyticNumberTheory.Sieve.WeightedPan
import AnalyticNumberTheory.Sieve.VaughanIdentity
import Mathlib.Data.ZMod.Basic
import AnalyticNumberTheory.LargeSieve.CharacterIndicators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.GroupTheory.Exponent
import Mathlib.Data.ZMod.Units

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


/-! ## 3. Maximum bounds for panMaxL and panMaxY -/


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


/-- Complex Type I character sum:
`V_χ(y,u) = Σ_{n≤y} vaughanFirst(n,u)·χ(n)`. -/
noncomputable def panTypeIV1CharSum (q y u : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), (vaughanFirst n u : ℂ) * χ (n : ZMod q)


/-- The inverse representative of a unit `a` times a unit `l`
is again a unit modulo `q`, as needed for the pointwise `apV1` bound. -/
lemma isUnit_natInvMod_mul_residue {q a l : ℕ} (hq : 0 < q) (hcop_a : a.Coprime q)
    (hl : l.Coprime q) : IsUnit (((natInvMod q a * l % q) : ℕ) : ZMod q) := by
  have : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hval : (((natInvMod q a * l % q : ℕ) : ZMod q)) =
      (((natInvMod q a * l : ℕ) : ZMod q)) := by
    have hz := ZMod.natCast_zmod_val (((natInvMod q a * l : ℕ) : ZMod q))
    simp
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


/-- Character-sum L² expression `t_q(m) = Σ_χ ‖V_χ(m)‖²`,
the natural square-mean object for the multiplicative large sieve. -/
noncomputable def panTypeIICharSqSum (q m u v : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2


end

end AnalyticNumberTheory.Sieve
