import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith

/-! # AnalyticNumberTheory.Sieve.BombieriVinogradov

## Bombieri--Vinogradov theorem and pointwise remainder interfaces

The Bombieri--Vinogradov theorem (1965) is a central source of distribution
conditions in Chen's theorem. It controls the average error in the
distribution of primes in arithmetic progressions, replacing the role
of the generalized Riemann hypothesis (GRH) in these mean estimates.

**Classical Bombieri--Vinogradov theorem**: for each fixed `A > 0`,
there exists `B = B(A)` such that

  Σ_{q ≤ x^(1/2) log^(-B) x} max_{y ≤ x} max_{(l,q)=1}
    |π(y; q, l) - li(y)/φ(q)| ≪ x / log^A x.

Here `li` denotes the genuine logarithmic integral. The existing API
name `logarithmicIntegral` below instead denotes the proxy `x / log x`;
it is not the logarithmic integral. The name is retained for compatibility.

Applications in Chen's theorem:
  - The sieve distribution condition
    `|{a ∈ A : d | a}| = ν(d)/d · X + R_d`.
  - Distribution level `D = N^(1/2 - ε)` from Bombieri--Vinogradov.
  - The distribution input required for Jurkat--Richert and Selberg sieves.

This module proves fixed-parameter remainder interfaces, not the classical
uniform averaged theorem.

References:
  - Bombieri, E. (1965), Math. Ann. 157, 220-260
  - Vinogradov, A.I. (1965), Izv. Akad. Nauk SSSR Ser. Mat. 29, 903-934
  - Liu, Z. (2022), arXiv:2203.07871, Theorem 1
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 9
-/

namespace AnalyticNumberTheory.Sieve

open Real Finset

open scoped Classical
open scoped ArithmeticFunction.Moebius

/-! ## 1. Counting primes in arithmetic progressions -/

/-- `π(x; q, l) = |{p ≤ x : p is prime, p ≡ l (mod q)}|`.
For a positive modulus with `(l,q) = 1`, Dirichlet's theorem guarantees
infinitely many such primes. -/
def primesInAP (x q l : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card

/-- Compatibility proxy `x / log x` for the prime-counting main term.

Despite its historical name, this is **not** the paper's logarithmic integral
`li(x) = ∫₂ˣ dt / log t`. The name and definition are retained to preserve the
existing API; source-faithful consumers must keep the main-term model abstract. -/
noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  x / log x

/-- Proxy error `π(x; q, l) - (x / log x) / φ(q)`.

This is not definitionally the classical `π(x; q, l) - li(x) / φ(q)`. -/
noncomputable def distributionError (x q l : ℕ) : ℝ :=
  (primesInAP x q l : ℝ) - logarithmicIntegral x / Nat.totient q

/-! ## 2. Bombieri--Vinogradov-shaped remainder interfaces -/

/-- **Fixed-parameter interface for a Bombieri--Vinogradov-shaped error**.
The classical averaged estimate is

  Σ_{q ≤ x^(1/2) log^(-B) x} max_{y ≤ x} max_{(l,q)=1}
    |π(y; q, l) - li(y)/φ(q)| ≪ x / log^A x.

In Chen's theorem this supplies a distribution level
`D = N^(1/2 - ε)` for arbitrarily small `ε > 0`, with
`Σ |R_d| ≪ N / log^A N`.

The genuine theorem controls an **average over q** with a constant
uniform for all sufficiently large `x`. The interface below has no such
sum and does not assert a uniform per-modulus bound with an extra
`1/φ(q)` factor; that stronger assertion is neither standard BV nor
a consequence of these definitions and the available mathlib results.
It only gives a multiplicative remainder constant after fixing
`x,q,y,l`. The uniform averaged theorem requires the large sieve and
Vaughan's identity. -/
theorem bombieri_vinogradov :
    ∀ A : ℝ, 0 < A → ∀ x : ℕ, 2 ≤ x →
      ∀ q : ℕ, q ≥ 1 →
        ∀ y : ℕ, 2 ≤ y → y ≤ x →
          ∀ l : ℕ, l.Coprime q → l < q →
            ∃ C : ℝ,
              |distributionError y q l| ≤ C * x / ((log x) ^ A * Nat.totient q) := by
  intro A _hA x hx q hq y _hy _hyx l _hl _hlt
  have hlog : 0 < log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hqpos : 0 < q := by omega
  have hphi_nat : 0 < Nat.totient q := Nat.totient_pos.mpr hqpos
  have hphi : 0 < (Nat.totient q : ℝ) := by exact_mod_cast hphi_nat
  have hscale : 0 < (x : ℝ) / ((log x) ^ A * Nat.totient q) := by
    exact div_pos (by exact_mod_cast (by omega : 0 < x))
      (mul_pos (Real.rpow_pos_of_pos hlog A) hphi)
  let E : ℝ := |distributionError y q l|
  refine ⟨E / ((x : ℝ) / ((log x) ^ A * Nat.totient q)), ?_⟩
  change E ≤ E / ((x : ℝ) / ((log x) ^ A * Nat.totient q)) * (x : ℝ) /
    ((log x) ^ A * Nat.totient q)
  rw [mul_div_assoc, div_mul_cancel₀ _ (ne_of_gt hscale)]

/-- A simplified wrapper for the fixed-parameter interface, explicitly
recording the scale `D = x^(1/2) / log^B x`.
The corresponding classical target has the shape
`Σ_{q ≤ D} max_{(l,q)=1} |π(x; q, l) - li(x)/φ(q)| ≪ x / log^A x`;
this wrapper does not assert that uniform average. -/
theorem bombieri_vinogradov_simple :
    ∀ A : ℝ, 0 < A → ∀ x : ℕ, 2 ≤ x →
      ∃ B : ℝ, ∃ D : ℝ,
          D = (x : ℝ) ^ (1/2 : ℝ) / (log x) ^ B ∧
          ∀ q : ℕ, (q : ℝ) ≤ D → q ≥ 1 →
            ∃ y : ℕ, y ≤ x ∧ y ≥ 2 ∧
              ∀ l : ℕ, l.Coprime q → l < q →
                ∃ C : ℝ,
                  |distributionError y q l| ≤
                    C * x / ((log x) ^ A * Nat.totient q) := by
  intro A hA x hx
  refine ⟨0, (x : ℝ) ^ (1/2 : ℝ) / (log x) ^ (0 : ℝ), rfl, ?_⟩
  intro q hq_le hq1
  refine ⟨x, le_rfl, ?_, ?_⟩
  · exact hx
  ·
    intro l hl_coprime hl_lt
    exact bombieri_vinogradov A hA x hx q hq1 x hx le_rfl l hl_coprime hl_lt

/-! ## 3. Distribution expressions for Chen's theorem -/

/-- The prime indices for the Chen sieve set
`A = {N - p : p is prime, N^(1/10) < p < N}`.
The definition stores the primes `p`, rather than their translates `N-p`. -/
noncomputable def chenSieveSet (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p =>
    p.Prime ∧ (N : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) < N)

/-- The prime-counting main-term approximation `X = N / log N`
used in Chen's theorem. -/
noncomputable def chenX (N : ℕ) : ℝ :=
  (N : ℝ) / log N

/-- The Goldbach-type density product `ν(d) = Π_{p|d} (p-1)⁻¹`
used in Chen's theorem. -/
noncomputable def chenNu (d : ℕ) : ℝ :=
  d.primeFactors.prod (fun p => 1 / ((p : ℝ) - 1))

/-- The distribution level `D = N^(1/2 - ε)` used in Chen's theorem. -/
noncomputable def chenDistributionLevel (N : ℕ) (ε : ℝ) : ℝ :=
  (N : ℝ) ^ (1/2 - ε)

/-- **Fixed-N distribution remainder bound**. The classical
Bombieri--Vinogradov application in Chen's theorem has the form
`|{a ∈ A : d | a}| = ν(d)/d · X + R_d` for
`d ≤ D = N^(1/2 - ε)`, with errors controlled on the scale
`N / log^A N` for `A > 0`.

Here `C` is chosen after fixing `N`, so the conclusion is only a bound
uniform over a finite set of moduli at that `N`. A genuine
Bombieri--Vinogradov conclusion requires the same `C` for all
sufficiently large `N`, together with the averaged error estimate. -/
theorem chen_distribution_condition
    (N : ℕ) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1/2) (hN : 2 ≤ N) :
    ∃ A : ℝ, ∃ C : ℝ,
      ∀ d : ℕ, (d : ℝ) ≤ chenDistributionLevel N ε → d ≥ 1 →
        |((chenSieveSet N).filter (fun a => d ∣ a)).sum (fun _ => (1 : ℝ)) -
          (chenNu d / d * chenX N)| ≤ C * (N : ℝ) / (log N) ^ A := by
  let L : ℝ := chenDistributionLevel N ε
  let E : ℕ → ℝ := fun d =>
    ((chenSieveSet N).filter (fun a => d ∣ a)).sum (fun _ => (1 : ℝ)) -
      chenNu d / d * chenX N
  let M : ℝ := (Finset.range (Nat.floor L + 1)).sum (fun d => |E d|)
  have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  refine ⟨1, M * log N / N, ?_⟩
  intro d hd _hd1
  have hd_floor : d ≤ Nat.floor L := by
    apply Nat.le_floor
    simpa [L] using hd
  have hd_mem : d ∈ Finset.range (Nat.floor L + 1) := by
    simp only [Finset.mem_range]
    omega
  have hle : |E d| ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun i _hi => abs_nonneg (E i)) hd_mem
  change |E d| ≤ (M * log (N : ℝ) / (N : ℝ)) * (N : ℝ) /
    (log (N : ℝ)) ^ (1 : ℝ)
  calc
    |E d| ≤ M := hle
    _ = (M * log (N : ℝ) / (N : ℝ)) * (N : ℝ) /
        (log (N : ℝ)) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
          field_simp

/-! ## 4. Pan-shaped remainder interface -/

/-- **Fixed-parameter remainder interface of Pan type**.
The classical weighted target is

  Σ_{q ≤ x^(1/2) log^(-B) x} μ²(q) · 3^ω(q) ·
    max_{y ≤ x} max_{(l,q)=1} |Σ_{(a,q)=1} f(a) · Δ(y; a, q, l)| ≪ x / log^A x,

where `f(a)` is the characteristic function used in Chen's theorem and
`Δ(y; a, q, l) = π(y; a, q, l) - li(y/a)/φ(q)`.
Pan's theorem is a weighted extension of Bombieri--Vinogradov, used
to estimate the remainder `R` in the upper bound for `Ω`.

In the current definition, `distributionError y q l`, summed over
`range x`, does not depend on `a`, so it is not the weighted
distribution error in the literature. The conclusion below only
provides a multiplicative remainder constant for fixed parameters;
it does not place `C` before all `x,q,y,l`. The genuine Pan theorem
requires an error depending on `a` and a single constant uniform for
all sufficiently large `x`. -/
theorem pan_mean_value_theorem :
    ∀ A : ℝ, 0 < A → ∀ x : ℕ, 2 ≤ x →
      ∀ q : ℕ, q ≥ 1 →
        ∀ y : ℕ, 2 ≤ y → y ≤ x →
          ∀ l : ℕ, l.Coprime q → l < q →
            ∃ C : ℝ,
              ((μ q : ℤ) : ℝ) ^ 2 * 3 ^ (q.primeFactors.card) *
                |(Finset.range x).sum (fun a =>
                  if a.Coprime q then
                    distributionError y q l
                  else 0)| ≤
                C * x / (log x) ^ A := by
  intro A _hA x hx q _hq y _hy _hyx l _hl _hlt
  have hlog : 0 < log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hscale : 0 < (x : ℝ) / (log x) ^ A :=
    div_pos (by exact_mod_cast (by omega : 0 < x)) (Real.rpow_pos_of_pos hlog A)
  let E : ℝ := ((μ q : ℤ) : ℝ) ^ 2 * 3 ^ (q.primeFactors.card) *
    |(Finset.range x).sum (fun a =>
      if a.Coprime q then distributionError y q l else 0)|
  refine ⟨E / ((x : ℝ) / (log x) ^ A), ?_⟩
  change E ≤ E / ((x : ℝ) / (log x) ^ A) * (x : ℝ) / (log x) ^ A
  rw [mul_div_assoc]
  rw [div_mul_cancel₀ _ (ne_of_gt hscale)]

/-! ## 5. Parameter choices in Chen's theorem -/

/-
The parameter choices in the classical Chen argument are:

1. **Sifting level**: `z = N^(1/10)`, removing prime factors
   at most `N^(1/10)` from `N-p`.
2. **Distribution level**: `D = N^(1/2 - ε)` from Bombieri--Vinogradov,
   the range in which the errors are controlled.
3. **Sieve ratio**:
   `s = log(D)/log(z) = (1/2 - ε)/(1/10) = 5 - 10ε ≈ 5`.
   Jurkat--Richert gives an effective lower bound at this value.
4. **Switching parameter**: `y = N^(1/3)`, distinguishing the
   three-factor case in `W(N)`.
5. **Selberg sifting level**: `z' = N^(1/4 - ε/2)`,
   used in the upper bound for `Ω`.
-/

/-- The Chen sifting level `z = N^(1/10)`. -/
noncomputable def chenSieveLevel (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1/10 : ℝ)

/-- The Chen switching parameter `y = N^(1/3)`. -/
noncomputable def chenSwitchLevel (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1/3 : ℝ)

/-- The Chen Selberg sifting level `z' = N^(1/4 - ε/2)`. -/
noncomputable def chenSelbergLevel (N : ℕ) (ε : ℝ) : ℝ :=
  (N : ℝ) ^ (1/4 - ε/2)

/-- Sieve ratio `s = log(D)/log(z) = (1/2 - ε)/(1/10) = 5 - 10ε`. -/
noncomputable def chenSieveRatio (_N : ℕ) (ε : ℝ) : ℝ :=
  (1/2 - ε) / (1/10 : ℝ)

/-- For sufficiently small positive `ε`, the sieve ratio is close to 5. -/
theorem chenSieveRatio_approx (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/100) :
    4.9 < chenSieveRatio 0 ε ∧ chenSieveRatio 0 ε < 5 := by
  unfold chenSieveRatio
  constructor
  · field_simp; nlinarith
  · field_simp; nlinarith

/-! ## 6. Mathematical scope -/

/-
**Definitions and interfaces in this module**

1. Definitions:
   - `primesInAP`: the arithmetic-progression prime count `π(x; q, l)`.
   - `logarithmicIntegral`: the proxy `x/log x`, not the true `li(x)`.
   - `distributionError`: the difference between `π(x; q, l)` and
     this proxy divided by `φ(q)`.
   - `chenSieveSet`: prime indices for the translated set `A = {N - p}`.
   - `chenNu`: the Goldbach-type density product `ν(d)`.
   - `chenDistributionLevel`: `D = N^(1/2 - ε)`.

2. Proved interfaces:
   - `bombieri_vinogradov`: a fixed-parameter remainder interface,
     not the classical averaged BV theorem.
   - `bombieri_vinogradov_simple`: the corresponding simplified interface.
   - `pan_mean_value_theorem`: a fixed-parameter Pan-shaped remainder interface.
   - `chen_distribution_condition`: a fixed-N distribution remainder bound.

3. Classical uniform conclusions not asserted or proved here:
   - Bombieri--Vinogradov requires the large sieve and Vaughan's identity.
   - The uniform Pan theorem additionally requires the correct weighted
     error depending on the summation variable.

4. Roles of the classical results in Chen's theorem:
   - The distribution condition enables Jurkat--Richert and a lower bound for `W(N)`.
   - Pan's theorem gives `R ≪ N/log^A N` for the upper bound on `Ω`.
-/

end AnalyticNumberTheory.Sieve
