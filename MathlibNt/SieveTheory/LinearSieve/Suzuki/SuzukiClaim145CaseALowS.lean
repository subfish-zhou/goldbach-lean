import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145ComparisonInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiLowerFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SmallDHighCoordinate

open scoped Classical BigOperators
open Filter Topology Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Suzuki Claim 14.5, Case A: the low-`s` source branch

For `κ = κ̂ = 1` and `β = 2`, Suzuki applies Lemma 14.3 and the factorial
estimate used in (14.7), first obtaining

`L^M / M! * exp L ≤ exp (-s log s + s log log (3K) + O (log K + s))`.

The uniform target below is exactly that first big-O step.  It precedes the
subsequent comparison with

`exp (-s log s - s log log (3s) + sqrt K / 2)`

and therefore must be discharged before the latter comparison can be used.
No Claim-14.5 conclusion is assumed here.
-/

/-- The first missing scalar inequality in Claim 14.5, Case A, low-`s` range.

`A` is the absolute big-O coefficient and `K₀` is the source choice that `K` is
sufficiently large.  The quantifiers are uniform in `K`, `D`, the natural
ceiling cutoff, and `s`; in particular this is not a finite-`D` maximum or an
eventual-`D` statement. -/
def Claim145CaseALowSBigOScalarTarget (C1 ΘK : ℝ) : Prop :=
  ∃ A K₀ : ℝ, 0 ≤ A ∧ 2 ≤ K₀ ∧
    ∀ (D z : ℕ) (K s : ℝ),
      K₀ ≤ K → 2 ≤ D →
      z = ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      2 ≤ s → s ≤ Real.sqrt K / Real.log K →
      Real.log (D : ℝ) ≤ C1 * K ^ ΘK →
      suzukiSourceL (z : ℝ) K ^ (⌊s - 2⌋₊ + 1) /
            ((⌊s - 2⌋₊ + 1).factorial : ℝ) *
          Real.exp (suzukiSourceL (z : ℝ) K) ≤
        Real.exp
          (-s * Real.log s + s * Real.log (Real.log (3 * K)) +
            A * (Real.log K + s))

private theorem pow_div_factorial_exp_le
    {L : ℝ} {m : ℕ} (hL : 0 < L) (hm : 0 < m) :
    L ^ m / (m.factorial : ℝ) * Real.exp L ≤
      Real.exp (L + (m : ℝ) * (1 + Real.log L - Real.log (m : ℝ))) := by
  exact pow_div_factorial_mul_exp_le_logExponent hL hm le_rfl

private theorem lowS_exponent_comparison
    {L m s q r B : ℝ}
    (hL : 1 ≤ L) (hm : 0 < m) (hs : 2 ≤ s)
    (hms : m ≤ s) (hsm : s - 2 < m)
    (hB : 1 ≤ B) (hq : 1 ≤ q) (hr : 0 ≤ r)
    (hLB : L ≤ B * q) (hqr : q ≤ r + 2) :
    L + m * (1 + Real.log L - Real.log m) ≤
      -s * Real.log s + s * Real.log q +
        (B + Real.log B + 10) * (r + s) := by
  have hs0 : 0 < s := by linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hBlogq : 0 < B * q := mul_pos hB0 hq0
  have hlogL : Real.log L ≤ Real.log B + Real.log q := by
    calc
      Real.log L ≤ Real.log (B * q) := Real.log_le_log (by linarith) hLB
      _ = Real.log B + Real.log q := Real.log_mul (ne_of_gt hB0) (ne_of_gt hq0)
  have hcoef : 0 ≤ 1 + Real.log L := by linarith
  have hpositivePart : m * (1 + Real.log L) ≤
      s * (1 + Real.log B + Real.log q) := by
    calc
      m * (1 + Real.log L) ≤ s * (1 + Real.log L) :=
        mul_le_mul_of_nonneg_right hms hcoef
      _ ≤ s * (1 + Real.log B + Real.log q) := by
        apply mul_le_mul_of_nonneg_left _ hs0.le
        linarith [hlogL]
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hgap0 : 0 ≤ s - m := sub_nonneg.mpr hms
  have hgap2 : s - m < 2 := by linarith
  have hlogdiff : Real.log s - Real.log m ≤ s / m - 1 := by
    rw [← Real.log_div (ne_of_gt hs0) (ne_of_gt hm)]
    exact Real.log_le_sub_one_of_pos (div_pos hs0 hm)
  have hloggap : m * (Real.log s - Real.log m) ≤ s - m := by
    have := mul_le_mul_of_nonneg_left hlogdiff hm.le
    calc
      m * (Real.log s - Real.log m) ≤ m * (s / m - 1) := this
      _ = s - m := by
        simp only [mul_sub, div_eq_mul_inv, mul_left_comm m s,
          mul_inv_cancel₀ hm.ne', mul_one]
  have hfirstGap : (s - m) * Real.log s ≤ 2 * s := by
    have hlogs : Real.log s ≤ s :=
      (Real.log_le_sub_one_of_pos hs0).trans (by linarith)
    have hgaple : s - m ≤ 2 := le_of_lt hgap2
    calc
      (s - m) * Real.log s ≤ 2 * Real.log s :=
        mul_le_mul_of_nonneg_right hgaple hlogs0
      _ ≤ 2 * s := by linarith
  have hfactorialGap : s * Real.log s - m * Real.log m ≤ 3 * s := by
    have hdecomp : s * Real.log s - m * Real.log m =
        (s - m) * Real.log s + m * (Real.log s - Real.log m) := by ring
    rw [hdecomp]
    linarith
  have hLcoarse : L ≤ B * (r + s) :=
    hLB.trans (mul_le_mul_of_nonneg_left
      (hqr.trans (add_le_add le_rfl hs)) hB0.le)
  have hA : 0 ≤ B + Real.log B + 10 := by linarith
  have habsorb : L + s * (1 + Real.log B) + 3 * s ≤
      (B + Real.log B + 10) * (r + s) := by
    have hrest : s * (1 + Real.log B) + 3 * s ≤
        (Real.log B + 4) * (r + s) := by
      nlinarith
    have hBpart : B * (r + s) ≤ (B + Real.log B + 10) * (r + s) := by
      gcongr <;> linarith
    nlinarith
  calc
    L + m * (1 + Real.log L - Real.log m) =
        L + m * (1 + Real.log L) - m * Real.log m := by ring
    _ ≤ L + s * (1 + Real.log B + Real.log q) - m * Real.log m := by
      linarith
    _ ≤ -s * Real.log s + s * Real.log q +
        (L + s * (1 + Real.log B) + 3 * s) := by
      linarith
    _ ≤ _ := by linarith

/-- Suzuki (14.7), with the factorial estimated by the elementary Stirling lower
bound, gives the first scalar big-O target in the low-`s` branch. -/
theorem claim145_caseA_lowS_bigOScalarTarget (C1 ΘK : ℝ) :
    Claim145CaseALowSBigOScalarTarget C1 ΘK := by
  let K₀ : ℝ := Real.exp 2
  refine ⟨?_, K₀, ?_, ?_, ?_⟩
  · let C : ℝ := Real.log C1 - Real.log (Real.log 2) +
        Real.log (1 + 1 / Real.log 2)
    let B : ℝ := |ΘK + 1| + |C| + 1
    exact B + Real.log B + 10
  · dsimp only
    have hB : 1 ≤ |ΘK + 1| +
        |Real.log C1 - Real.log (Real.log 2) + Real.log (1 + 1 / Real.log 2)| + 1 := by
      nlinarith [abs_nonneg (ΘK + 1),
        abs_nonneg (Real.log C1 - Real.log (Real.log 2) + Real.log (1 + 1 / Real.log 2))]
    have hlogB := Real.log_nonneg hB
    linarith
  · dsimp [K₀]
    have : (2 : ℝ) ≤ Real.exp 2 := by
      calc
        (2 : ℝ) ≤ 1 + 2 := by norm_num
        _ ≤ Real.exp 2 := by simpa [add_comm] using Real.add_one_le_exp 2
    exact this
  · intro D z K s hK hD hz hs hsLow hsmall
    let C : ℝ := Real.log C1 - Real.log (Real.log 2) +
      Real.log (1 + 1 / Real.log 2)
    let B : ℝ := |ΘK + 1| + |C| + 1
    let L : ℝ := suzukiSourceL (z : ℝ) K
    let m : ℕ := ⌊s - 2⌋₊ + 1
    let q : ℝ := Real.log (3 * K)
    let r : ℝ := Real.log K
    have hKpos : 0 < K := (Real.exp_pos 2).trans_le hK
    have hKone : 1 ≤ K := by
      have : (1 : ℝ) ≤ Real.exp 2 := by
        calc
          (1 : ℝ) ≤ 2 + 1 := by norm_num
          _ ≤ Real.exp 2 := Real.add_one_le_exp 2
      exact this.trans hK
    have hr : 0 ≤ r := by exact Real.log_nonneg hKone
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hlogD : 0 < Real.log (D : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < D by omega))
    have hC1 : 0 < C1 := by
      have hpowpos : 0 < K ^ ΘK := Real.rpow_pos_of_pos hKpos ΘK
      by_contra hn
      have : C1 ≤ 0 := le_of_not_gt hn
      have : C1 * K ^ ΘK ≤ 0 := mul_nonpos_of_nonpos_of_nonneg this hpowpos.le
      linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLleD : L ≤ suzukiSourceL (D : ℝ) K := by
      dsimp only [L]
      subst z
      exact suzukiSourceL_natCeil_rpow_le hD hs
    have hfirst : Real.log (Real.log (D : ℝ) / Real.log 2) ≤
        Real.log C1 + ΘK * Real.log K - Real.log (Real.log 2) := by
      have hquotpos : 0 < Real.log (D : ℝ) / Real.log 2 := div_pos hlogD hlog2
      have hboundpos : 0 < C1 * K ^ ΘK := mul_pos hC1 (Real.rpow_pos_of_pos hKpos ΘK)
      calc
        Real.log (Real.log (D : ℝ) / Real.log 2) =
            Real.log (Real.log (D : ℝ)) - Real.log (Real.log 2) := by
          rw [Real.log_div (ne_of_gt hlogD) (ne_of_gt hlog2)]
        _ ≤ Real.log (C1 * K ^ ΘK) - Real.log (Real.log 2) := by
          gcongr
        _ = Real.log C1 + ΘK * Real.log K - Real.log (Real.log 2) := by
          rw [Real.log_mul (ne_of_gt hC1) (ne_of_gt (Real.rpow_pos_of_pos hKpos ΘK)),
            Real.log_rpow hKpos ΘK]
    have hsecondArg : 1 + K / Real.log 2 ≤ K * (1 + 1 / Real.log 2) := by
      rw [mul_add, mul_one, mul_one_div]
      exact add_le_add hKone le_rfl
    have hconstpos : 0 < 1 + 1 / Real.log 2 := by positivity
    have hsecond : Real.log (1 + K / Real.log 2) ≤
        Real.log K + Real.log (1 + 1 / Real.log 2) := by
      calc
        Real.log (1 + K / Real.log 2) ≤ Real.log (K * (1 + 1 / Real.log 2)) :=
          Real.log_le_log (by positivity) hsecondArg
        _ = _ := Real.log_mul (ne_of_gt hKpos) (ne_of_gt hconstpos)
    have hLD : suzukiSourceL (D : ℝ) K ≤ (ΘK + 1) * r + C := by
      dsimp only [suzukiSourceL, r, C]
      linarith
    have hqform : q = Real.log 3 + r := by
      dsimp only [q, r]
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hKpos)]
    have hqgeR : r ≤ q := by
      rw [hqform]
      exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))
    have hq2 : 2 ≤ q := by
      have h3K : Real.exp 2 ≤ 3 * K := hK.trans (by nlinarith [hKpos])
      have := Real.log_le_log (Real.exp_pos 2) h3K
      simpa using this
    have hB : 1 ≤ B := by
      dsimp [B]
      nlinarith [abs_nonneg (ΘK + 1), abs_nonneg C]
    have hLB : L ≤ B * q := by
      have habsTheta : (ΘK + 1) * r ≤ |ΘK + 1| * q := by
        calc
          (ΘK + 1) * r ≤ |ΘK + 1| * r := by
            gcongr
            exact le_abs_self _
          _ ≤ |ΘK + 1| * q := by gcongr
      have habsC : C ≤ |C| * q := by
        calc
          C ≤ |C| := le_abs_self C
          _ ≤ |C| * q := by nlinarith [abs_nonneg C]
      calc
        L ≤ suzukiSourceL (D : ℝ) K := hLleD
        _ ≤ (ΘK + 1) * r + C := hLD
        _ ≤ (|ΘK + 1| + |C|) * q := by
          rw [add_mul]
          linarith
        _ ≤ B * q := by
          dsimp only [B]
          nlinarith
    have hz2 : 2 ≤ z := by
      subst z
      have hp : (1 : ℝ) < (D : ℝ) ^ (1 / s) :=
        Real.one_lt_rpow (by exact_mod_cast (show 1 < D by omega))
          (one_div_pos.mpr (by linarith))
      have : 1 < ⌈(D : ℝ) ^ (1 / s)⌉₊ := (Nat.lt_ceil).mpr (by simpa using hp)
      omega
    have hLone : 1 ≤ L := by
      have hfirstNonneg : 0 ≤ Real.log (Real.log (z : ℝ) / Real.log 2) := by
        apply Real.log_nonneg
        apply (le_div_iff₀ hlog2).2
        have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
        simpa only [one_mul] using
          (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hz2R)
      have hExpK : Real.exp 1 < K / Real.log 2 := by
        have he12 : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
        have heK : Real.exp 1 < K := he12.trans_le hK
        have hlog2lt1 : Real.log 2 < 1 := by
          have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
          norm_num at this ⊢
          exact this
        exact (lt_div_iff₀ hlog2).2 (by nlinarith [Real.exp_pos 1])
      have hsecondOne : 1 ≤ Real.log (1 + K / Real.log 2) := by
        have harg : Real.exp 1 ≤ 1 + K / Real.log 2 := by linarith
        have := Real.log_le_log (Real.exp_pos 1) harg
        simpa using this
      dsimp only [L, suzukiSourceL]
      linarith
    have hmpos : 0 < m := by dsimp [m]; omega
    have hmle : (m : ℝ) ≤ s := by
      dsimp only [m]
      have hf := Nat.floor_le (show 0 ≤ s - 2 by linarith)
      push_cast
      linarith
    have hsmlt : s - 2 < (m : ℝ) := by
      dsimp only [m]
      have hf := Nat.lt_floor_add_one (s - 2)
      exact_mod_cast hf
    have hqUpper : q ≤ r + 2 := by
      rw [hqform]
      have hlog3 : Real.log 3 ≤ 2 :=
        (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans (by norm_num)
      linarith
    have henv := pow_div_factorial_exp_le (L := L) (m := m) (by linarith) hmpos
    have hexponent := lowS_exponent_comparison hLone
      (by exact_mod_cast hmpos) hs hmle hsmlt hB (by linarith [hq2]) hr hLB hqUpper
    have hexp := Real.exp_le_exp.mpr hexponent
    exact henv.trans (by simpa [L, m, q, r, B, C] using hexp)

/-- Lemma 14.3 reaches the left side of the frozen low-`s` scalar target with
no dependence on the depth `N`. -/
theorem claim145_caseA_lowS_lemma14_3_upper
    (S : BoundingSieve) {N D z : ℕ} {K s : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) (hs : 2 ≤ s) :
    suzukiActualT S N D z ≤
      suzukiSourceL (z : ℝ) K ^ (⌊s - 2⌋₊ + 1) /
            ((⌊s - 2⌋₊ + 1).factorial : ℝ) *
          Real.exp (suzukiSourceL (z : ℝ) K) := by
  exact suzukiLemma14_3_natCeil_uniform_explicit
    S hlocal (by omega) hs hz

/-- Proposition 13.1(ii) supplies the lower side of (14.6), uniformly in the
parity/depth.  This is the target-scale edge used after the two scalar
exponential comparisons in Suzuki's low-`s` branch. -/
theorem claim145_caseA_lowS_equation14_6_lower
    (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) :
    ∃ C M : ℝ, 0 ≤ C ∧ 3 ≤ M ∧
      ∀ (N D : ℕ) (d Δ K s : ℝ),
        2 ≤ D → M ≤ s →
        claim14_5VProduct S (D : ℝ) *
              (Real.exp (Real.sqrt K) /
                (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) *
              ((1 + s ^ d / Real.log (D : ℝ)) ^ s * s *
                proposition131iiLowerProfile C s) *
              (Real.log (D : ℝ)) ^ (-Δ) ≤
          claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K s := by
  rcases proposition131iiUniformQuantitativeLower_of_source hH with
    ⟨C, M, hC, hM, hprop⟩
  refine ⟨C, M, hC, hM, ?_⟩
  intro N D d Δ K s hD hs
  exact claim14_5Scale_lower_of_proposition131ii
    S H (N := N) (D := (D : ℝ)) (d := d) (Δ := Δ)
      (σ := sourceSigma (D : ℝ) d) (K := K) (C := C) (M := M) (s := s)
      (by exact_mod_cast (show 1 < D by omega))
      (sourceSigma_pos_of_nat_two_le hD) (by linarith) hs hprop

/-- Final pointwise assembly of the high-`s` half of Claim 14.5, Case A.

The two hypotheses `hsourceLarge` and `hexponent` are the explicit large-`K`
threshold hidden in the first `O(log K + s)` on pp. 82--83.  The hypothesis
`habsorb` is the second, final `O(s)` absorption (including all harmless Euler
and logarithmic prefactors).  They are deliberately exposed: the source only
asserts the result after choosing `K` sufficiently large, and replacing them by
a finite-`D` maximum or compactness would not formalize that assertion.

Everything between these threshold inequalities is closed here: Lemma 14.3,
the already proved high-coordinate logarithmic gain, the production lower form
of (14.6), and the literal `Claim14_5Bound`. -/
theorem claim145_caseA_highS_final_of_equation14_6_lower
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {d Δ K s C1 Θ A C145 C : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hs : 2 ≤ s) (hK : 1 < K) (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hhigh : Real.sqrt K / Real.log K ≤ s)
    (hlogrel : Real.log K ≤ 4 * Real.log s)
    (hsmall : Real.log (D : ℝ) ≤ C1 * K ^ Θ)
    (hsourceLarge :
      Real.exp 1 * suzukiSourceL (z : ℝ) K ≤ s - 2)
    (hexponent :
      suzukiSourceL (z : ℝ) K + (s - 2) *
          (1 + Real.log (suzukiSourceL (z : ℝ) K) - Real.log (s - 2)) ≤
        -s * Real.log s + s * Real.log (Real.log (3 * K)) +
          A * (Real.log K + s))
    (hgrowth :
      (C1 * (16 : ℝ) ^ Θ) * (Real.log s) ^ (2 * Θ) *
          (Real.log (3 * K) * (Real.log (3 * s)) ^ 2) ≤
        s ^ (d - 2 * Θ))
    (hC145 : 0 ≤ C145)
    (habsorb :
      Real.exp (A * (Real.log K + s) + C * s -
          s * Real.log (Real.log (3 * s))) ≤
        C145 * (claim14_5VProduct S (D : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (D : ℝ) * sourceSigma (D : ℝ) d))) *
          s * (Real.log (D : ℝ)) ^ (-Δ))
    (hlower :
      claim14_5VProduct S (D : ℝ) *
            (Real.exp (Real.sqrt K) /
              (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) *
            ((1 + s ^ d / Real.log (D : ℝ)) ^ s * s *
              proposition131iiLowerProfile C s) *
            (Real.log (D : ℝ)) ^ (-Δ) ≤
        claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K s) :
    Claim14_5Bound
      (fun m D' z' => suzukiActualT S m ⌈D'⌉₊ ⌈z'⌉₊)
      S H N (D : ℝ) (z : ℝ) d Δ
        (sourceSigma (D : ℝ) d) K s C145 := by
  have hLpos : 0 < suzukiSourceL (z : ℝ) K := by
    have hD1 : (1 : ℝ) < (D : ℝ) := by
      exact_mod_cast (show 1 < D by omega)
    have hs0 : 0 < s := by linarith
    have hzpow : (1 : ℝ) < (D : ℝ) ^ (1 / s) :=
      Real.one_lt_rpow hD1 (one_div_pos.mpr hs0)
    have hz1 : (1 : ℝ) < (z : ℝ) := by
      rw [hz]
      exact_mod_cast ((Nat.lt_ceil).mpr (by simpa using hzpow) :
        1 < ⌈(D : ℝ) ^ (1 / s)⌉₊)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hz2 : 2 ≤ z := by
      have hz1nat : 1 < z := by exact_mod_cast hz1
      omega
    have hfirst : 0 ≤ Real.log (Real.log (z : ℝ) / Real.log 2) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ hlog2).2
      simpa using Real.strictMonoOn_log.monotoneOn
        (by norm_num : (0 : ℝ) < 2)
        (show (0 : ℝ) < (z : ℝ) by positivity)
        (by exact_mod_cast hz2 : (2 : ℝ) ≤ (z : ℝ))
    have hsecond : 0 < Real.log (1 + K / Real.log 2) := by
      apply Real.log_pos
      have : 0 < K / Real.log 2 := div_pos (by linarith) hlog2
      linarith
    unfold suzukiSourceL
    linarith
  have h143 := claim145_caseA_lowS_lemma14_3_upper
    (S := S) (N := N) (D := D) (z := z) (K := K) (s := s)
    hlocal hD hz hs
  have hlogUpper := floorTail_le_claim145_logExponent
    hLpos hsourceLarge h143
  have hgain := claim145_caseA_highS_log_gain_of_growth
    (D := (D : ℝ)) (K := K) (s := s) (d := d) (C1 := C1) (Θ := Θ)
    (by exact_mod_cast (show 1 < D by omega)) hK (by linarith) hC1
    (claim145_caseA_highS_power_chain hK hhigh hlogrel hC1.le hΘ hsmall)
    hgrowth
  let b : ℝ := 1 + s ^ d / Real.log (D : ℝ)
  have hbpos : 0 < b := by
    dsimp [b]
    have hlogD : 0 < Real.log (D : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < D by omega))
    have hpow : 0 ≤ s ^ d := Real.rpow_nonneg (by linarith) _
    positivity
  have hgain' :
      -s * Real.log s + s * Real.log (Real.log (3 * K)) +
          A * (Real.log K + s) ≤
        s * Real.log b - s * Real.log s -
          2 * s * Real.log (Real.log (3 * s)) +
          A * (Real.log K + s) := by
    dsimp [b]
    linarith
  have hcore :
      suzukiActualT S N D z ≤
        Real.exp (s * Real.log b - s * Real.log s -
          2 * s * Real.log (Real.log (3 * s)) +
          A * (Real.log K + s)) :=
    hlogUpper.trans (Real.exp_le_exp.mpr (hexponent.trans hgain'))
  have hprofile :
      b ^ s * proposition131iiLowerProfile C s =
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s) := by
    unfold proposition131iiLowerProfile
    rw [Real.rpow_def_of_pos hbpos, ← Real.exp_add]
    congr 1
    ring
  have hsplit :
      Real.exp (s * Real.log b - s * Real.log s -
          2 * s * Real.log (Real.log (3 * s)) +
          A * (Real.log K + s)) =
        Real.exp (A * (Real.log K + s) + C * s -
          s * Real.log (Real.log (3 * s))) *
          (b ^ s * proposition131iiLowerProfile C s) := by
    rw [hprofile, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit] at hcore
  have hscalar := hcore.trans (mul_le_mul_of_nonneg_right
    habsorb
    (mul_nonneg (Real.rpow_nonneg hbpos.le _) (Real.exp_pos _).le))
  unfold Claim14_5Bound
  simp only [Nat.ceil_natCast]
  calc
    suzukiActualT S N D z ≤
        (C145 * (claim14_5VProduct S (D : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (D : ℝ) * sourceSigma (D : ℝ) d))) *
          s * (Real.log (D : ℝ)) ^ (-Δ)) *
          (b ^ s * proposition131iiLowerProfile C s) := hscalar
    _ = C145 *
        (claim14_5VProduct S (D : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) *
          ((1 + s ^ d / Real.log (D : ℝ)) ^ s * s *
            proposition131iiLowerProfile C s) *
          (Real.log (D : ℝ)) ^ (-Δ)) := by
      dsimp [b]
      ring
    _ ≤ C145 * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K s :=
      mul_le_mul_of_nonneg_left hlower hC145

/-- Source-contract form of the preceding assembly.  It chooses the uniform
Proposition-13.1(ii) constants supplied by (14.6); once the displayed source
large-`K` thresholds hold for those constants, the conclusion is the final
Claim-14.5 bound, not an intermediate scalar comparison. -/
theorem claim145_caseA_highS_final
    (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H)
    {N D z : ℕ} {d Δ K s C1 Θ A C145 : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hs : 2 ≤ s) (hK : 1 < K) (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hhigh : Real.sqrt K / Real.log K ≤ s)
    (hlogrel : Real.log K ≤ 4 * Real.log s)
    (hsmall : Real.log (D : ℝ) ≤ C1 * K ^ Θ)
    (hsourceLarge :
      Real.exp 1 * suzukiSourceL (z : ℝ) K ≤ s - 2)
    (hexponent :
      suzukiSourceL (z : ℝ) K + (s - 2) *
          (1 + Real.log (suzukiSourceL (z : ℝ) K) - Real.log (s - 2)) ≤
        -s * Real.log s + s * Real.log (Real.log (3 * K)) +
          A * (Real.log K + s))
    (hgrowth :
      (C1 * (16 : ℝ) ^ Θ) * (Real.log s) ^ (2 * Θ) *
          (Real.log (3 * K) * (Real.log (3 * s)) ^ 2) ≤
        s ^ (d - 2 * Θ))
    (hC145 : 0 ≤ C145) :
    ∃ C M : ℝ, 0 ≤ C ∧ 3 ≤ M ∧
      (M ≤ s →
        Real.exp (A * (Real.log K + s) + C * s -
            s * Real.log (Real.log (3 * s))) ≤
          C145 * (claim14_5VProduct S (D : ℝ) *
            (Real.exp (Real.sqrt K) /
              (Real.log (D : ℝ) * sourceSigma (D : ℝ) d))) *
            s * (Real.log (D : ℝ)) ^ (-Δ) →
        Claim14_5Bound
          (fun m D' z' => suzukiActualT S m ⌈D'⌉₊ ⌈z'⌉₊)
          S H N (D : ℝ) (z : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K s C145) := by
  obtain ⟨C, M, hC, hM3, hlower⟩ :=
    claim145_caseA_lowS_equation14_6_lower S H hH
  refine ⟨C, M, hC, hM3, ?_⟩
  intro hMs habsorb
  exact claim145_caseA_highS_final_of_equation14_6_lower
    S H hlocal hD hz hs hK hC1 hΘ hhigh hlogrel hsmall
      hsourceLarge hexponent hgrowth hC145 habsorb
      (hlower N D d Δ K s hD hMs)

/-- Suzuki's second displayed comparison in Case A, uniformly throughout
`2 ≤ s ≤ √K / log K`.  Above one source threshold the multiplicative constant
can in fact be chosen to be one. -/
theorem claim145_caseA_lowS_exponent_comparison_eventually
    {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ s : ℝ, 2 ≤ s →
      s ≤ Real.sqrt K / Real.log K →
      Real.exp
          (-s * Real.log s + s * Real.log (Real.log (3 * K)) +
            A * (Real.log K + s)) ≤
        Real.exp
          (-s * Real.log s - s * Real.log (Real.log (3 * s)) +
            Real.sqrt K / 2) := by
  have hll := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 32 by norm_num)
  have hsqrt := (isLittleO_log_rpow_rpow_atTop 1
      (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show (0 : ℝ) < 1 / (16 * (A + 1)) by positivity)
  filter_upwards [eventually_ge_atTop (3 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (16 * A)),
      (Real.tendsto_log_atTop.comp
        (tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num))).eventually hll,
      hsqrt] with K hK hlogKlarge hllK hsqrtK
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hlogK1 : 1 ≤ Real.log K := (le_max_left _ _).trans hlogKlarge
  have hlogK : 0 < Real.log K := lt_of_lt_of_le zero_lt_one hlogK1
  have hsqrt0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hsqrtleK : Real.sqrt K ≤ K := by
    nlinarith [Real.sq_sqrt hK0.le]
  have hlog3K : Real.log (3 * K) ≤ 2 * Real.log K := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hK0)]
    have : Real.log 3 ≤ Real.log K :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hK0 hK
    linarith
  have hlog3Kpos : 0 < Real.log (3 * K) := Real.log_pos (by nlinarith)
  have hloglog3K_nonneg : 0 ≤ Real.log (Real.log (3 * K)) := by
    apply Real.log_nonneg
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hK0)]
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)]
  have hloglog3K : Real.log (Real.log (3 * K)) ≤ Real.log K / 16 := by
    change |Real.log (Real.log (3 * K))| ≤
      (1 / 32 : ℝ) * |Real.log (3 * K)| at hllK
    rw [abs_of_nonneg hloglog3K_nonneg,
      abs_of_nonneg hlog3Kpos.le] at hllK
    nlinarith
  have hAover : A / Real.log K ≤ 1 / 16 := by
    apply (div_le_iff₀ hlogK).2
    have hAlog : 16 * A ≤ Real.log K :=
      (le_max_right 1 (16 * A)).trans hlogKlarge
    nlinarith
  have hAlogSqrt : A * Real.log K ≤ Real.sqrt K / 16 := by
    change |Real.log K ^ (1 : ℝ)| ≤
      1 / (16 * (A + 1)) * |K ^ (1 / 2 : ℝ)| at hsqrtK
    rw [Real.rpow_one, abs_of_nonneg hlogK.le,
      abs_of_nonneg (Real.rpow_nonneg hK0.le _)] at hsqrtK
    have hfrac : A / (A + 1) ≤ 1 := by
      exact (div_le_one (by linarith : 0 < A + 1)).2 (by linarith)
    rw [← Real.sqrt_eq_rpow] at hsqrtK
    have hmul := mul_le_mul_of_nonneg_left hsqrtK hA
    calc
      A * Real.log K ≤ A * (1 / (16 * (A + 1)) * Real.sqrt K) := hmul
      _ = (A / (A + 1)) * (Real.sqrt K / 16) := by field_simp
      _ ≤ 1 * (Real.sqrt K / 16) := by
        exact mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = _ := one_mul _
  refine ⟨by linarith, ?_⟩
  intro s hs hsupper
  have hs0 : 0 < s := by linarith
  have hsleK : s ≤ K := by
    calc
      s ≤ Real.sqrt K / Real.log K := hsupper
      _ ≤ Real.sqrt K := (div_le_self hsqrt0 hlogK1)
      _ ≤ K := hsqrtleK
  have hlog3spos : 0 < Real.log (3 * s) := Real.log_pos (by nlinarith)
  have hlls : Real.log (Real.log (3 * s)) ≤
      Real.log (Real.log (3 * K)) := by
    apply Real.log_le_log hlog3spos
    exact Real.strictMonoOn_log.monotoneOn
      (mul_pos (by norm_num) hs0) (mul_pos (by norm_num) hK0)
      (by nlinarith)
  have hslog :
      s * (Real.log (Real.log (3 * K)) + Real.log (Real.log (3 * s))) ≤
        Real.sqrt K / 8 := by
    have hsum : Real.log (Real.log (3 * K)) + Real.log (Real.log (3 * s)) ≤
        Real.log K / 8 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsum hs0.le
    have hslogK : s * Real.log K ≤ Real.sqrt K :=
      (le_div_iff₀ hlogK).mp hsupper
    nlinarith
  have hAs : A * s ≤ Real.sqrt K / 16 := by
    have hmul := mul_le_mul_of_nonneg_left hsupper hA
    calc
      A * s ≤ A * (Real.sqrt K / Real.log K) := hmul
      _ = (A / Real.log K) * Real.sqrt K := by field_simp
      _ ≤ (1 / 16 : ℝ) * Real.sqrt K := by
        exact mul_le_mul_of_nonneg_right hAover hsqrt0
      _ = Real.sqrt K / 16 := by ring
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Strengthened (14.6) prefactor absorption, including the moving
`sourceSigma D d` denominator factor. -/
theorem claim145_caseA_lowS_146_prefactor_eventually
    {C1 Θ d Δ C : ℝ} (hC1 : 0 ≤ C1) (hΘ : 0 < Θ) (hd : 0 < d)
    (hsource : 2 / d < 1 / Θ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hC : 0 ≤ C) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ D s : ℝ, 2 ≤ D → 2 ≤ s →
      s ≤ Real.sqrt K / Real.log K →
      Real.log D ≤ C1 * K ^ Θ →
      (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          (Real.log D) ^ (1 + Δ) * sourceSigma D d * Real.exp (C * s) ≤
        Real.exp (Real.sqrt K / 2) := by
  have hΘ0 : 0 ≤ Θ := hΘ.le
  have hΘd : Θ / d < 1 / 2 := by
    have hcross : 2 * Θ < d := by
      have := (div_lt_div_iff₀ hd hΘ).mp hsource
      nlinarith
    exact (div_lt_iff₀ hd).2 (by nlinarith)
  let R : ℝ := Real.log 27 / Real.log 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog27 : 0 < Real.log 27 := Real.log_pos (by norm_num)
  have hR0 : 0 < R := by dsimp [R]; positivity
  let B : ℝ := 4 * Θ + 3
  let Q : ℝ := (4 + 1 / d) * |Real.log C1| + |Real.log R| +
    |Real.log (Real.log 2)|
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    have : 0 ≤ 4 + 1 / d := by positivity
    positivity
  have hsqrt := (isLittleO_log_rpow_rpow_atTop 1
      (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show (0 : ℝ) < 1 / (16 * (B + 1)) by positivity)
  filter_upwards [eventually_ge_atTop (max 3 (2 / Real.log 2)),
      Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (16 * C)),
      Real.tendsto_sqrt_atTop.eventually_ge_atTop (16 * Q), hsqrt]
      with K hK hlogKlarge hsqrtQ hsqrtK
  have hK0 : 0 < K := by
    exact lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hK)
  have hK3 : 3 ≤ K := (le_max_left _ _).trans hK
  have hK2 : 2 ≤ K := by linarith
  have hlogK1 : 1 ≤ Real.log K := (le_max_left _ _).trans hlogKlarge
  have hlogK : 0 < Real.log K := zero_lt_one.trans_le hlogK1
  have hsqrt0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hBlog : B * Real.log K ≤ Real.sqrt K / 16 := by
    change |Real.log K ^ (1 : ℝ)| ≤
      1 / (16 * (B + 1)) * |K ^ (1 / 2 : ℝ)| at hsqrtK
    rw [Real.rpow_one, abs_of_nonneg hlogK.le,
      abs_of_nonneg (Real.rpow_nonneg hK0.le _), ← Real.sqrt_eq_rpow] at hsqrtK
    have hfrac : B / (B + 1) ≤ 1 :=
      (div_le_one (by linarith : 0 < B + 1)).2 (by linarith)
    calc
      B * Real.log K ≤ B * (1 / (16 * (B + 1)) * Real.sqrt K) :=
        mul_le_mul_of_nonneg_left hsqrtK hB0
      _ = (B / (B + 1)) * (Real.sqrt K / 16) := by field_simp
      _ ≤ 1 * (Real.sqrt K / 16) :=
        mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = _ := one_mul _
  have hQsqrt : Q ≤ Real.sqrt K / 16 := by nlinarith
  have hbaseK : 1 + K / Real.log 2 ≤ K ^ 2 := by
    have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hpart : K / Real.log 2 ≤ 2 * K := by
      apply (div_le_iff₀ hlog2).2
      nlinarith
    nlinarith [sq_nonneg (K - 3)]
  refine ⟨hK2, ?_⟩
  intro D s hD hs hsupper hsmall
  have hD1 : 1 < D := by linarith
  have hD0 : 0 < D := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hC1pos : 0 < C1 := by
    by_contra hn
    have : C1 = 0 := le_antisymm (le_of_not_gt hn) hC1
    rw [this, zero_mul] at hsmall
    linarith
  have hKpow : 0 < K ^ Θ := Real.rpow_pos_of_pos hK0 _
  have hloglogD : Real.log (Real.log D) ≤ Real.log C1 + Θ * Real.log K := by
    have hh := Real.log_le_log hlogD hsmall
    rw [Real.log_mul (ne_of_gt hC1pos) (ne_of_gt hKpow),
      Real.log_rpow hK0 Θ] at hh
    exact hh
  have hlogD2 : Real.log 2 ≤ Real.log D :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hD0 hD
  have hlog27D_eq : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hD0)]
  have hlog27D_bound : Real.log (27 * D) ≤ R * Real.log D := by
    rw [hlog27D_eq]
    have hc : 0 ≤ Real.log 27 / Real.log 2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hlogD2 hc
    dsimp [R]
    calc
      Real.log 27 + Real.log D =
          (Real.log 27 / Real.log 2) * Real.log 2 + Real.log D := by
            field_simp
      _ ≤ (Real.log 27 / Real.log 2) * Real.log D + Real.log D := by
        simpa [add_comm] using add_le_add_right hh (Real.log D)
      _ = (Real.log 27 / Real.log 2 + 1) * Real.log D := by ring
  have hlog27D_one : 1 < Real.log (27 * D) := by
    rw [Real.lt_log_iff_exp_lt (by positivity : 0 < 27 * D)]
    nlinarith [Real.exp_one_lt_three]
  have hlog27D : 0 < Real.log (27 * D) := zero_lt_one.trans hlog27D_one
  have hloglog27D : Real.log (Real.log (27 * D)) ≤
      Real.log R + Real.log (Real.log D) := by
    have hh := Real.log_le_log hlog27D hlog27D_bound
    rw [Real.log_mul (ne_of_gt hR0) (ne_of_gt hlogD)] at hh
    exact hh
  have hloglog27Dpos : 0 < Real.log (Real.log (27 * D)) :=
    Real.log_pos hlog27D_one
  have htriple : Real.log (Real.log (Real.log (27 * D))) ≤
      Real.log R + Real.log (Real.log D) :=
    (Real.log_le_self hloglog27Dpos.le).trans hloglog27D
  have hlogbase : Real.log (1 + K / Real.log 2) ≤ 2 * Real.log K := by
    have hbpos : 0 < 1 + K / Real.log 2 := by positivity
    have hh := Real.log_le_log hbpos hbaseK
    rw [Real.log_pow] at hh
    simpa using hh
  have hCs : C * s ≤ Real.sqrt K / 16 := by
    have hCover : C / Real.log K ≤ 1 / 16 := by
      apply (div_le_iff₀ hlogK).2
      have : 16 * C ≤ Real.log K := (le_max_right 1 (16 * C)).trans hlogKlarge
      nlinarith
    calc
      C * s ≤ C * (Real.sqrt K / Real.log K) :=
        mul_le_mul_of_nonneg_left hsupper hC
      _ = (C / Real.log K) * Real.sqrt K := by field_simp
      _ ≤ (1 / 16 : ℝ) * Real.sqrt K :=
        mul_le_mul_of_nonneg_right hCover hsqrt0
      _ = Real.sqrt K / 16 := by ring
  have hsigmaPos : 0 < sourceSigma D d := by
    rw [sourceSigma]
    positivity
  have hlogP :
      Real.log ((Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          (Real.log D) ^ (1 + Δ) * sourceSigma D d * Real.exp (C * s)) ≤
        Real.sqrt K / 2 := by
    have hbpos : 0 < 1 + K / Real.log 2 := by positivity
    rw [Real.log_mul (by positivity : (Real.log D / Real.log 2) *
          (1 + K / Real.log 2) * (Real.log D) ^ (1 + Δ) * sourceSigma D d ≠ 0)
        (Real.exp_ne_zero _),
      Real.log_mul (by positivity : (Real.log D / Real.log 2) *
          (1 + K / Real.log 2) * (Real.log D) ^ (1 + Δ) ≠ 0)
        (ne_of_gt hsigmaPos),
      Real.log_mul (by positivity : (Real.log D / Real.log 2) *
          (1 + K / Real.log 2) ≠ 0)
        (by positivity : (Real.log D) ^ (1 + Δ) ≠ 0),
      Real.log_mul (by positivity : Real.log D / Real.log 2 ≠ 0)
        (ne_of_gt hbpos), Real.log_div (ne_of_gt hlogD) (ne_of_gt hlog2),
      Real.log_rpow hlogD (1 + Δ), sourceSigma,
      Real.log_mul (by positivity : (Real.log D) ^ (1 / d) ≠ 0)
        (ne_of_gt hloglog27Dpos), Real.log_rpow hlogD (1 / d), Real.log_exp]
    have hcoef : 0 ≤ 2 + Δ + 1 / d := by positivity
    have hcoefMax : 2 + Δ + 1 / d ≤ 3 + 1 / d := by linarith
    have hmain := mul_le_mul_of_nonneg_left hloglogD hcoef
    have hlogC1 : Real.log C1 ≤ |Real.log C1| := le_abs_self _
    have hlogR : Real.log R ≤ |Real.log R| := le_abs_self _
    have hnegloglog2 : -Real.log (Real.log 2) ≤ |Real.log (Real.log 2)| := neg_le_abs _
    have hC1term : (3 + Δ + 1 / d) * Real.log C1 ≤
        (4 + 1 / d) * |Real.log C1| := by
      have hc0 : 0 ≤ 3 + Δ + 1 / d := by positivity
      have hc4 : 3 + Δ + 1 / d ≤ 4 + 1 / d := by linarith
      calc
        _ ≤ (3 + Δ + 1 / d) * |Real.log C1| :=
          mul_le_mul_of_nonneg_left hlogC1 hc0
        _ ≤ _ := mul_le_mul_of_nonneg_right hc4 (abs_nonneg _)
    have hΘterm : (3 + Δ + 1 / d) * (Θ * Real.log K) ≤
        (4 * Θ + 1 / 2) * Real.log K := by
      have hΔΘ : Δ * Θ ≤ Θ := by
        nlinarith [mul_le_mul_of_nonneg_right hΔ1 hΘ0]
      have hrat := mul_le_mul_of_nonneg_right hΘd.le hlogK.le
      calc
        _ = ((3 + Δ) * Θ + Θ / d) * Real.log K := by ring
        _ ≤ (4 * Θ + 1 / 2) * Real.log K := by nlinarith
    dsimp [B, Q] at hBlog hQsqrt ⊢
    nlinarith
  have hPpos : 0 < (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
      (Real.log D) ^ (1 + Δ) * sourceSigma D d * Real.exp (C * s) := by positivity
  calc
    _ = Real.exp (Real.log ((Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          (Real.log D) ^ (1 + Δ) * sourceSigma D d * Real.exp (C * s))) :=
      (Real.exp_log hPpos).symm
    _ ≤ Real.exp (Real.sqrt K / 2) := Real.exp_le_exp.mpr hlogP


end MathlibNt.SieveTheory
