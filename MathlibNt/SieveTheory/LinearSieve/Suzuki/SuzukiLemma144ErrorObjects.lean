import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayersKappaOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Suzuki Lemma 14.4 error objects and algebraic normalization (κ = 1)

Source-faithful transcription of the objects used around (14.13)--(14.15).
The Section 13 majorants `T̂⁺, T̂⁻` are parameters: their genuinely analytic
monotonicity and integral estimates are exposed below as named premises.
-/

open scoped Classical BigOperators
open Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

/-- The two signs occurring in the Section 13 majorants. -/
inductive ErrorSign
  | plus
  | minus
  deriving DecidableEq, Repr

namespace ErrorSign

/-- Reversal of sign, used because the induction step changes parity. -/
def opposite : ErrorSign → ErrorSign
  | .plus => .minus
  | .minus => .plus


@[simp] theorem opposite_plus : opposite .plus = .minus := rfl
@[simp] theorem opposite_minus : opposite .minus = .plus := rfl

/-- Suzuki's convention: odd depth uses `+`, even depth uses `-`. -/
def ofDepth (N : ℕ) : ErrorSign := if Odd N then .plus else .minus

@[simp] theorem ofDepth_of_odd {N : ℕ} (hN : Odd N) : ofDepth N = .plus := by
  simp [ofDepth, hN]

@[simp] theorem ofDepth_of_even {N : ℕ} (hN : Even N) : ofDepth N = .minus := by
  have hnodd : ¬ Odd N := Nat.not_odd_iff_even.mpr hN
  simp [ofDepth, hnodd]

/-- Suzuki's `ε₊=1`, `ε₋=0`. -/
def epsilon : ErrorSign → ℝ
  | .plus => 1
  | .minus => 0

/-- Passing from `N` to `N-1` reverses the sign. -/
theorem ofDepth_pred_eq_opposite {N : ℕ} (hN : 1 ≤ N) :
    ofDepth (N - 1) = (ofDepth N).opposite := by
  rcases Nat.even_or_odd N with hEven | hOdd
  · have hPredOdd : Odd (N - 1) := by
      obtain ⟨k, hk⟩ := hEven
      have hkpos : 0 < k := by omega
      refine ⟨k - 1, ?_⟩
      omega
    simp [ofDepth_of_even hEven, ofDepth_of_odd hPredOdd, opposite]
  · have hPredEven : Even (N - 1) := by
      obtain ⟨k, hk⟩ := hOdd
      refine ⟨k, ?_⟩
      omega
    simp [ofDepth_of_odd hOdd, ofDepth_of_even hPredEven, opposite]

end ErrorSign

/-- The two positive Section 13 majorants `T̂⁺` and `T̂⁻`.
At κ = 1 Suzuki is in the `κ > 1/2` branch of (13.1), hence `κ̂ = κ = 1`:
`δ` does not occur in this branch.  The functions remain analytic input here. -/
structure Section13HatLayers where
  betaHat : ℝ
  Tplus : ℝ → ℝ
  Tminus : ℝ → ℝ

/-- Signed lookup for `T̂⁺` and `T̂⁻`. -/
def Section13HatLayers.T (H : Section13HatLayers) : ErrorSign → ℝ → ℝ
  | .plus => H.Tplus
  | .minus => H.Tminus

/-- At κ=1, equation (13.1) gives `κ̂ = κ = 1`. -/
def Section13HatLayers.kappaHat (_H : Section13HatLayers) : ℝ := 1

/-- Exact κ=1 specialization of Suzuki's
`E_N(D,s) = (1+s^d/log D)^s s^(κ̂-κ+1) T̂^±(s)`.
The sign is `+` for odd `N` and `-` for even `N`. -/
noncomputable def errorEnvelope
    (H : Section13HatLayers) (N : ℕ) (D d s : ℝ) : ℝ :=
  (1 + s ^ d / Real.log D) ^ s *
    s ^ (H.kappaHat - 1 + 1) * H.T (ErrorSign.ofDepth N) s

/-- Exact κ=1 specialization of Suzuki's `q_D^±`. -/
noncomputable def qD
    (H : Section13HatLayers) (sign : ErrorSign) (D d Δ s : ℝ) : ℝ :=
  (1 + s ^ d / Real.log D) ^ (s - 1) *
    (s - 1) ^ (H.kappaHat - 1 + 1) * H.T sign (s - 1) *
      (s / (s - 1)) ^ Δ

/-- Exact κ=1 specialization of Suzuki's auxiliary
`Λ_ε^±(t) = (1+(t+ε)^d/log D)^t t^(κ̂+1) T̂^±(t)`, `ε=0,1`. -/
noncomputable def lambda
    (H : Section13HatLayers) (sign : ErrorSign) (D d ε t : ℝ) : ℝ :=
  (1 + (t + ε) ^ d / Real.log D) ^ t *
    t ^ (H.kappaHat + 1) * H.T sign t

/-- The source parity in `E_N` is exact. -/
theorem errorEnvelope_odd {N : ℕ} (hN : Odd N) (H : Section13HatLayers) (D d s : ℝ) :
    errorEnvelope H N D d s =
      (1 + s ^ d / Real.log D) ^ s * s * H.Tplus s := by
  simp [errorEnvelope, Section13HatLayers.kappaHat, ErrorSign.ofDepth_of_odd hN,
    Section13HatLayers.T]

/-- The source parity in `E_N` is exact. -/
theorem errorEnvelope_even {N : ℕ} (hN : Even N) (H : Section13HatLayers) (D d s : ℝ) :
    errorEnvelope H N D d s =
      (1 + s ^ d / Real.log D) ^ s * s * H.Tminus s := by
  simp [errorEnvelope, Section13HatLayers.kappaHat, ErrorSign.ofDepth_of_even hN,
    Section13HatLayers.T]

/-- Algebraic parity normalization preceding (14.13): the inherited depth
`N-1` uses the sign opposite to depth `N`. -/
theorem equation14_13_source_normalization
    (H : Section13HatLayers) {N : ℕ} (hN : 1 ≤ N) (x d s : ℝ) :
    errorEnvelope H (N - 1) x d (s - 1) =
      (1 + (s - 1) ^ d / Real.log x) ^ (s - 1) *
        (s - 1) *
          H.T (ErrorSign.ofDepth N).opposite (s - 1) := by
  unfold errorEnvelope Section13HatLayers.kappaHat
  rw [ErrorSign.ofDepth_pred_eq_opposite hN]
  norm_num [Real.rpow_one]


/-- The pointwise majorization used to pass from inherited `E_{N-1}` to
`(log D)^(-Δ) q_D^∓`.  Its proof is the genuinely analytic/base-comparison
part immediately before (14.13), so it is represented as a premise. -/
def Claim14_13PointwisePremise
    (H : Section13HatLayers) (N : ℕ) (D d Δ s x : ℝ) : Prop :=
  errorEnvelope H (N - 1) x d (s - 1) * (Real.log x) ^ (-Δ) ≤
    (Real.log D) ^ (-Δ) * qD H (ErrorSign.ofDepth N).opposite D d Δ s


/-- Algebraic identity (14.14), specialized to κ=1. -/
theorem equation14_14
    (H : Section13HatLayers) (sign : ErrorSign) (D d Δ t : ℝ)
    (ht : 1 < t) :
    qD H sign D d Δ t * t =
      (1 + t ^ d / Real.log D) ^ (t - 1) *
        (t - 1) ^ (H.kappaHat + 1) * H.T sign (t - 1) *
          (t / (t - 1)) ^ (1 + Δ) := by
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  have htm0 : 0 < t - 1 := sub_pos.mpr ht
  have hratio : 0 < t / (t - 1) := div_pos ht0 htm0
  rw [qD]
  rw [show H.kappaHat - 1 + 1 = H.kappaHat by ring]
  rw [Real.rpow_add htm0, Real.rpow_add hratio]
  rw [Real.rpow_one, Real.rpow_one]
  field_simp

/-- Algebraic identity (14.15), specialized to κ=1. -/
theorem equation14_15
    (H : Section13HatLayers) (sign : ErrorSign) (D d Δ t : ℝ)
    (ht : 1 < t) :
    lambda H sign D d 1 (t - 1) * (t / (t - 1)) ^ (1 + Δ) =
      qD H sign D d Δ t * t := by
  rw [lambda]
  norm_num
  exact (equation14_14 H sign D d Δ t ht).symm

/-- The shared exponential base is positive on every source range below. -/
private lemma errorBase_pos {D d s : ℝ} (hD : 1 < D) (hs : 0 ≤ s) :
    0 < 1 + s ^ d / Real.log D :=
  add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (Real.rpow_nonneg hs _) (Real.log_pos hD).le)

/-- Positivity of `E_N` from the currently available finite/Section-13 layer
positivity data. -/
theorem errorEnvelope_nonneg
    (H : Section13HatLayers) (N : ℕ) {D d s : ℝ}
    (hD : 1 < D) (hs : 0 ≤ s) (hT : 0 ≤ H.T (ErrorSign.ofDepth N) s) :
    0 ≤ errorEnvelope H N D d s := by
  unfold errorEnvelope
  have hbase : 0 ≤ 1 + s ^ d / Real.log D := (errorBase_pos hD hs).le
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hbase _) (Real.rpow_nonneg hs _)) hT


/-- Positivity of `Λ_ε^±` on the range used in Claim 14.6. -/
theorem lambda_nonneg
    (H : Section13HatLayers) (sign : ErrorSign) {D d ε t : ℝ}
    (hD : 1 < D) (hε : 0 ≤ ε) (ht : 0 ≤ t) (hT : 0 ≤ H.T sign t) :
    0 ≤ lambda H sign D d ε t := by
  unfold lambda
  have hte : 0 ≤ t + ε := add_nonneg ht hε
  have hbase : 0 ≤ 1 + (t + ε) ^ d / Real.log D := (errorBase_pos hD hte).le
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hbase _) (Real.rpow_nonneg ht _)) hT


/-- Strict positivity of `q_D^±` on the range used by Lemma 8.7. -/
theorem qD_pos
    (H : Section13HatLayers) (sign : ErrorSign) {D d Δ s : ℝ}
    (hD : 1 < D) (hs : 1 < s) (hT : 0 < H.T sign (s - 1)) :
    0 < qD H sign D d Δ s := by
  unfold qD
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hsm0 : 0 < s - 1 := sub_pos.mpr hs
  have hbase : 0 < 1 + s ^ d / Real.log D := errorBase_pos hD hs0.le
  exact mul_pos
    (mul_pos
      (mul_pos (Real.rpow_pos_of_pos hbase _) (Real.rpow_pos_of_pos hsm0 _)) hT)
    (Real.rpow_pos_of_pos (div_pos hs0 hsm0) _)

/-- Strict positivity of `Λ_ε^±` for `t>0`, `ε≥0`. -/
theorem lambda_pos
    (H : Section13HatLayers) (sign : ErrorSign) {D d ε t : ℝ}
    (hD : 1 < D) (hε : 0 ≤ ε) (ht : 0 < t) (hT : 0 < H.T sign t) :
    0 < lambda H sign D d ε t := by
  unfold lambda
  have hte : 0 < t + ε := add_pos_of_pos_of_nonneg ht hε
  have hbase : 0 < 1 + (t + ε) ^ d / Real.log D := errorBase_pos hD hte.le
  exact mul_pos
    (mul_pos (Real.rpow_pos_of_pos hbase _) (Real.rpow_pos_of_pos ht _)) hT


/-- Analytic Claim 14.6(i), deliberately left as a named premise. -/
def Claim14_6_MonotoneLambdaPremise
    (H : Section13HatLayers) (D d σ : ℝ) : Prop :=
  ∀ sign ε, ε = 0 ∨ ε = 1 →
    AntitoneOn (lambda H sign D d ε) (Icc (H.betaHat + sign.epsilon) σ)

/-- Analytic Claim 14.6(ii), deliberately left as a named premise. -/
def Claim14_6_MonotoneQPremise
    (H : Section13HatLayers) (D d Δ σ : ℝ) : Prop :=
  ∀ sign : ErrorSign,
    AntitoneOn (fun t => qD H sign.opposite D d Δ t * t)
      (Ioc (H.betaHat + sign.epsilon) σ)


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
