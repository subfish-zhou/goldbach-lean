/-
Temporary source-faithful closure of the N = 1, κ = 1 part of Suzuki Lemma 14.4.

The production API currently represents V₁(D,z)/V(z), rather than V₁(D,z)
itself: each summand is ν(p) V(p)/V(z).  This is the exact finite object to
which Suzuki Lemma 8.4 applies.  No final Lemma-14.4 error package is assumed.
-/
import MathlibNt.SieveTheory.SwitchingPrinciple
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerProp93

open scoped Classical BigOperators Interval
open Finset

namespace MathlibNt.SieveTheory
namespace SwitchingPrinciple

open SuzukiFiniteContinuousLayers

/-- Suzuki's `y₁ = D^(1/(β+1))`. -/
noncomputable def suzukiYOne (D β : ℝ) : ℝ := D ^ (1 / (β + 1))

/-- The exact finite normalized base object `V₁(D,z)/V(z)` from Lemma 7.1:

`∑_{y₁ ≤ p < z} ν(p) V(p)/V(z)`.

Only supported primes occur, as required by the finite `BoundingSieve` model.
The `D` argument in the production prime-sum is the power-coordinate parameter;
for the constant test function used here it does not affect the value. -/
noncomputable def suzukiVOneNormalized
    (S : BoundingSieve) (D β z : ℝ) : ℝ :=
  suzukiLemmaEightSixPrimeSum S D (suzukiYOne D β) z (fun _ => 1)

/-- The finite Euler product `V(z)` on the production support. -/
noncomputable def suzukiVProduct (S : BoundingSieve) (z : ℝ) : ℝ :=
  ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
    (1 - S.nu p)

/-- The unnormalized finite base object `V₁(D,z)`.  Expanding the normalized
prime sum gives exactly `∑_{y₁≤p<z} ν(p)V(p)`. -/
noncomputable def suzukiVOne
    (S : BoundingSieve) (D β z : ℝ) : ℝ :=
  suzukiVProduct S z * suzukiVOneNormalized S D β z

theorem suzukiVProduct_pos (S : BoundingSieve) (z : ℝ) :
    0 < suzukiVProduct S z := by
  unfold suzukiVProduct
  apply Finset.prod_pos
  intro p hp
  have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
  have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
  exact sub_pos.mpr (S.nu_lt_one_of_prime p hpprime hpdiv)

/-- Suzuki Lemma 8.4 at the exact real base cutoff.  The proof uses the
production real-node Abel identity and prime-atom assembly.  Lemma 8.6 is not
needed in the base case: its integral estimate would be weaker than this exact
telescoping identity. -/
theorem suzukiVOneNormalized_eq_localRatio_sub_one
    (S : BoundingSieve) (D β z : ℝ)
    (hyz : suzukiYOne D β ≤ z) :
    suzukiVOneNormalized S D β z =
      suzukiLocalRatio S (suzukiYOne D β) z - 1 := by
  rw [suzukiVOneNormalized]
  rw [← suzukiFiniteNodeAtomSum_eq_lemmaEightSixPrimeSum
    S D (suzukiYOne D β) z (fun _ => 1) hyz]
  rw [suzukiFiniteNodeAbel_atoms]
  have hvar : ∀ nodes : List ℝ,
      LinearSieve.finiteNodeVariationSum (fun x => suzukiLocalRatio S x z) (fun _ => 1) nodes = 0 := by
    intro nodes
    induction nodes with
    | nil => rfl
    | cons x xs ih =>
        cases xs with
        | nil => rfl
        | cons y ys => simp [LinearSieve.finiteNodeVariationSum, ih]
  rw [hvar]
  simp [suzukiLocalRatio]

/-- At κ = 1 and on the base source interval, Suzuki's continuous layer is
`f₁(s) = ((β+1)-s)/s`. -/
theorem suzukiLayer_one_eq_base_main
    {β s : ℝ} (hs : 0 < s) (hsβ : s ≤ β + 1) :
    suzukiLayer 1 β 1 s = (β + 1 - s) / s := by
  rw [suzukiLayer_one]
  simp only [baseLower, min_eq_left hsβ, dPowDensity]
  norm_num
  field_simp

/-- The one-term source-parity sum is exactly `f₁`. -/
theorem finiteSourceLayer_one_eq_suzukiLayer (β s : ℝ) :
    finiteSourceLayer 1 β 1 s = suzukiLayer 1 β 1 s := by
  simp [finiteSourceLayer]

/-- Replacing a real lower cutoff by `max(w,2)` does not change the finite
Euler ratio: every member of `prodPrimes.primeFactors` is a prime and hence at
least two.  This is the exact endpoint repair used in Suzuki's base case. -/
theorem suzukiLocalRatio_eq_max_two
    (S : BoundingSieve) (w z : ℝ) :
    suzukiLocalRatio S w z = suzukiLocalRatio S (max w 2) z := by
  unfold suzukiLocalRatio
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hwp, hpz⟩
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
    exact ⟨hp, max_le hwp hp2, hpz⟩
  · rintro ⟨hp, hwp, hpz⟩
    exact ⟨hp, (le_max_left w 2).trans hwp, hpz⟩

/-- N=1, κ=1 local-product closure.

This is the finite content of Suzuki (14.8), before the paper-specific
`T̂⁺` absorption: the main term is the genuine continuous `f₁(s)`, and the
remaining loss is the explicit dimension-one local-product error
`K(β+1)²/(s log D)`.

The production local-product contract starts at `2`.  As in Suzuki's proof, we
therefore replace `y₁` by `max(y₁,2)`, use the exact carrier equality above,
and then enlarge the elementary logarithmic bound back to `y₁`. -/
theorem suzukiVOneNormalized_le_fOne_add_localError
    {S : BoundingSieve} {D β z s K : ℝ}
    (hD : 1 < D) (hβ : 1 < β) (hs : 0 < s) (hsβ : s ≤ β + 1)
    (hz : z = D ^ (1 / s))
    (hz2 : 2 ≤ z)
    (hK : 0 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiVOneNormalized S D β z ≤
      finiteSourceLayer 1 β 1 s + K * (β + 1) ^ 2 / (s * Real.log D) := by
  have hβp : 0 < β + 1 := by linarith
  have hD0 : 0 < D := zero_lt_one.trans hD
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hy_formula : Real.log (suzukiYOne D β) = Real.log D / (β + 1) := by
    rw [suzukiYOne, Real.log_rpow hD0]
    ring
  have hz_formula : Real.log z = Real.log D / s := by
    rw [hz, Real.log_rpow hD0]
    ring
  have hExp : 1 / (β + 1) ≤ 1 / s := by
    exact one_div_le_one_div_of_le hs hsβ
  have hyz : suzukiYOne D β ≤ z := by
    rw [suzukiYOne, hz]
    exact Real.rpow_le_rpow_of_exponent_le hD.le hExp
  let w : ℝ := max (suzukiYOne D β) 2
  have hw2 : 2 ≤ w := le_max_right _ _
  have hwz : w ≤ z := max_le hyz hz2
  have hy1 : 1 < suzukiYOne D β := by
    rw [suzukiYOne]
    exact Real.one_lt_rpow hD (by positivity)
  have hw1 : 1 < w := hy1.trans_le (le_max_left _ _)
  have hlogy : 0 < Real.log (suzukiYOne D β) := Real.log_pos hy1
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hlogz : 0 < Real.log z := Real.log_pos (lt_of_lt_of_le (by norm_num) hz2)
  have hyw : suzukiYOne D β ≤ w := le_max_left _ _
  have hlogyw : Real.log (suzukiYOne D β) ≤ Real.log w :=
    Real.strictMonoOn_log.monotoneOn (zero_lt_one.trans hy1) (zero_lt_one.trans hw1) hyw
  have hinv : 1 / Real.log w ≤ 1 / Real.log (suzukiYOne D β) :=
    one_div_le_one_div_of_le hlogy hlogyw
  have hquot : Real.log z / Real.log w ≤
      Real.log z / Real.log (suzukiYOne D β) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hlogz.le
  have hKquot : K / Real.log w ≤ K / Real.log (suzukiYOne D β) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hK
  have hprodmono :
      (Real.log z / Real.log w) * (1 + K / Real.log w) ≤
        (Real.log z / Real.log (suzukiYOne D β)) *
          (1 + K / Real.log (suzukiYOne D β)) := by
    exact mul_le_mul hquot (by linarith [hKquot])
      (by positivity) (by positivity)
  rw [suzukiVOneNormalized_eq_localRatio_sub_one S D β z hyz]
  have hprod := hlocal w z hw2 hwz
  have hratioMax : suzukiLocalRatio S w z - 1 ≤
      (Real.log z / Real.log (suzukiYOne D β)) *
        (1 + K / Real.log (suzukiYOne D β)) - 1 :=
    (sub_le_sub_right hprod 1).trans (sub_le_sub_right hprodmono 1)
  have hratio : suzukiLocalRatio S (suzukiYOne D β) z - 1 ≤
      (Real.log z / Real.log (suzukiYOne D β)) *
        (1 + K / Real.log (suzukiYOne D β)) - 1 :=
    by simpa [w, suzukiLocalRatio_eq_max_two] using hratioMax
  calc
    suzukiLocalRatio S (suzukiYOne D β) z - 1 ≤
        (Real.log z / Real.log (suzukiYOne D β)) *
          (1 + K / Real.log (suzukiYOne D β)) - 1 := hratio
    _ = (β + 1 - s) / s + K * (β + 1) ^ 2 / (s * Real.log D) := by
      rw [hy_formula, hz_formula]
      field_simp
      ring
    _ = finiteSourceLayer 1 β 1 s + K * (β + 1) ^ 2 /
          (s * Real.log D) := by
      rw [finiteSourceLayer_one_eq_suzukiLayer,
        suzukiLayer_one_eq_base_main hs hsβ]

/-- Unnormalized form of the N=1 base estimate, with the exact source `V(z)`
factor displayed. -/
theorem suzukiVOne_le_V_mul_fOne_add_localError
    {S : BoundingSieve} {D β z s K : ℝ}
    (hD : 1 < D) (hβ : 1 < β) (hs : 0 < s) (hsβ : s ≤ β + 1)
    (hz : z = D ^ (1 / s)) (hz2 : 2 ≤ z) (hK : 0 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiVOne S D β z ≤ suzukiVProduct S z *
      (finiteSourceLayer 1 β 1 s + K * (β + 1) ^ 2 / (s * Real.log D)) := by
  unfold suzukiVOne
  exact mul_le_mul_of_nonneg_left
    (suzukiVOneNormalized_le_fOne_add_localError
      hD hβ hs hsβ hz hz2 hK hlocal)
    (suzukiVProduct_pos S z).le

/-- The discrete base object vanishes in the support branch `s ≥ β+1`. -/
theorem suzukiVOneNormalized_eq_zero_of_upper
    (S : BoundingSieve) {D β z s : ℝ}
    (hD : 1 < D) (hβ : 1 < β) (hβs : β + 1 ≤ s)
    (hz : z = D ^ (1 / s)) :
    suzukiVOneNormalized S D β z = 0 := by
  have hβp : 0 < β + 1 := by linarith
  have hExp : 1 / s ≤ 1 / (β + 1) :=
    one_div_le_one_div_of_le hβp hβs
  have hzy : z ≤ suzukiYOne D β := by
    rw [hz, suzukiYOne]
    exact Real.rpow_le_rpow_of_exponent_le hD.le hExp
  unfold suzukiVOneNormalized suzukiLemmaEightSixPrimeSum
  apply Finset.sum_eq_zero
  intro p hp
  have hpdata := Finset.mem_filter.mp hp
  exact False.elim ((not_lt_of_ge hpdata.2.1) (hpdata.2.2.trans_le hzy))

/-- Source support branch: for `s ≥ β+1`, the continuous `f₁` vanishes. -/
theorem finiteSourceLayer_one_eq_zero_of_upper
    (β : ℝ) {s : ℝ} (hs : β + 1 ≤ s) :
    finiteSourceLayer 1 β 1 s = 0 := by
  rw [finiteSourceLayer_one_eq_suzukiLayer]
  apply suzukiLayer_eq_zero_of_le 1 β 1
  norm_num at hs ⊢
  exact hs


end SwitchingPrinciple
end MathlibNt.SieveTheory
