import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87DimensionOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146IntegralClosure
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146LargePackage
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiPowerCoordinates

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-! ## Source-faithful statement of Claim 14.5 (κ = 1) -/

/-- The finite Euler product `V(x)` on the production support, repeated here
because the older base-case temporary module cannot be jointly imported with
the current Lemma-8.7 umbrella without a declaration collision. -/
noncomputable def claim14_5VProduct (S : BoundingSieve) (x : ℝ) : ℝ :=
  ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < x),
    (1 - S.nu p)

/-- The explicit quantity on the right of Claim 14.5 after replacing the
source `≪` by a named multiplicative constant.  At κ=1 this uses the literal
`E_N`, represented by `errorEnvelope`, and the finite Euler product `V(D)`.
The source has `exp (sqrt K)/(σ log D)` and a further `(log D)^(-Δ)`. -/
noncomputable def claim14_5Scale
    (S : BoundingSieve) (H : Section13HatLayers) (N : ℕ)
    (D d Δ σ K s : ℝ) : ℝ :=
  claim14_5VProduct S D * (Real.exp (Real.sqrt K) / (Real.log D * σ)) *
    errorEnvelope H N D d s * (Real.log D) ^ (-Δ)

/-- Exact non-asymptotic interface for Claim 14.5. `Tdisc N D z` is the
(real-parameter) discrete parity sum from the paper; no such object currently
exists in the production API, whose source-faithful discrete model has natural
cutoffs.  `C145` records precisely the implicit absolute constant in `≪`. -/
def Claim14_5Bound
    (Tdisc : ℕ → ℝ → ℝ → ℝ) (S : BoundingSieve) (H : Section13HatLayers)
    (N : ℕ) (D z d Δ σ K s C145 : ℝ) : Prop :=
  Tdisc N D z ≤ C145 * claim14_5Scale S H N D d Δ σ K s

/-- The exact range in which Suzuki invokes Claim 14.5. -/
def Claim14_5Regime (β D σ C1 K ΘK s : ℝ) : Prop :=
  β ≤ s ∧ (Real.log D ≤ C1 * K ^ ΘK ∨ σ ≤ s)

/-- Case I in the source, specialized to κ=1. -/
def Claim14_5CaseI (β : ℝ) (N : ℕ) (s σ : ℝ) : Prop :=
  β + (N % 2 : ℕ) ≤ s ∧ s ≤ σ

/-- Case II in the source.  It exists only at odd depth. -/
def Claim14_5CaseII (β : ℝ) (N : ℕ) (s : ℝ) : Prop :=
  Odd N ∧ β - 1 < s ∧ s ≤ β + 1

/-- After Claim 14.5 removes small `D` and large `s`, Suzuki's parity domain
splits exactly into Case I and Case II.  In particular, Case II is not an
optional analytic branch: it is forced by the open odd parity interval. -/
theorem claim14_5_exact_case_split
    {β D σ C1 K ΘK s : ℝ} {N : ℕ}
    (hdom : s ∈ SuzukiFiniteContinuousLayers.suzukiParityDomainOne β N)
    (hsσ : s ≤ σ) (_hlarge : C1 * K ^ ΘK < Real.log D) :
    Claim14_5CaseI β N s σ ∨ Claim14_5CaseII β N s := by
  rcases Nat.even_or_odd N with hN | hN
  · have hmod : N % 2 = 0 := Nat.even_iff.mp hN
    left
    unfold Claim14_5CaseI
    constructor
    · simpa [SuzukiFiniteContinuousLayers.suzukiParityDomainOne,
        SuzukiFiniteContinuousLayers.KappaOneModel.parityDomain, hmod] using hdom
    · exact hsσ
  · have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    have hleft : β - 1 < s := by
      simpa [SuzukiFiniteContinuousLayers.suzukiParityDomainOne,
        SuzukiFiniteContinuousLayers.KappaOneModel.parityDomain, hmod] using hdom
    by_cases hhigh : β + 1 ≤ s
    · left
      exact ⟨by simpa [hmod] using hhigh, hsσ⟩
    · right
      exact ⟨hN, hleft, le_of_not_ge hhigh⟩

/-- Full range partition used before the induction step: either Claim 14.5
already applies, or one is in exactly Case I/II. -/
theorem claim14_5_regime_or_caseI_or_caseII
    {β D σ C1 K ΘK s : ℝ} {N : ℕ}
    (hdom : s ∈ SuzukiFiniteContinuousLayers.suzukiParityDomainOne β N)
    (hsσor : s ≤ σ ∨ σ ≤ s) :
    Claim14_5Regime β D σ C1 K ΘK s ∨
      Claim14_5CaseI β N s σ ∨ Claim14_5CaseII β N s := by
  by_cases hβs : β ≤ s
  · by_cases hsmall : Real.log D ≤ C1 * K ^ ΘK
    · exact Or.inl ⟨hβs, Or.inl hsmall⟩
    · rcases hsσor with hsσ | hσs
      · exact Or.inr (claim14_5_exact_case_split hdom hsσ (lt_of_not_ge hsmall))
      · exact Or.inl ⟨hβs, Or.inr hσs⟩
  · right
    right
    have hodd : Odd N := by
      rcases Nat.even_or_odd N with heven | hodd
      · have hmod : N % 2 = 0 := Nat.even_iff.mp heven
        have : β ≤ s := by
          simpa [SuzukiFiniteContinuousLayers.suzukiParityDomainOne,
            SuzukiFiniteContinuousLayers.KappaOneModel.parityDomain, hmod] using hdom
        exact False.elim (hβs this)
      · exact hodd
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
    have hleft : β - 1 < s := by
      simpa [SuzukiFiniteContinuousLayers.suzukiParityDomainOne,
        SuzukiFiniteContinuousLayers.KappaOneModel.parityDomain, hmod] using hdom
    exact ⟨hodd, hleft, by linarith⟩

/-! ## Lemma 8.7 connected to Claim 14.6 -/

/-- Global continuous clamp of `q_D`; it agrees with `q_D` on `[τ,∞)` and
allows direct use of the global-continuity interface of Lemma 8.7. -/
noncomputable def qDClamp
    (H : Section13HatLayers) (sign : ErrorSign)
    (D d Δ τ t : ℝ) : ℝ :=
  qD H sign D d Δ (max τ t)

@[simp] theorem qDClamp_eq_of_le
    (H : Section13HatLayers) (sign : ErrorSign) (D d Δ : ℝ)
    {τ t : ℝ} (hτt : τ ≤ t) :
    qDClamp H sign D d Δ τ t = qD H sign D d Δ t := by
  simp [qDClamp, max_eq_right hτt]

lemma qDClamp_conditions_of_claim14_6_ii
    {H : Section13HatLayers} {β D d Δ τ σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hτ : H.betaHat + sign.epsilon < τ) (_hτσ : τ ≤ σ)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ) :
    Continuous (qDClamp H sign.opposite D d Δ τ) ∧
      (∀ t ∈ Icc τ σ, 0 ≤ qDClamp H sign.opposite D d Δ τ t) ∧
      AntitoneOn (fun t => qDClamp H sign.opposite D d Δ τ t * t) (Icc τ σ) := by
  have hτ1 : 1 < τ := by
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    rw [hH.betaHat_eq] at hτ
    linarith [hH.beta_gt_one]
  have hqcont : ContinuousOn (qD H sign.opposite D d Δ) (Ioi 1) := by
    unfold qD
    have hlog : 0 < Real.log D := Real.log_pos hD
    have htpos : ∀ t ∈ Ioi (1 : ℝ), 0 < t := fun t ht => zero_lt_one.trans ht
    have htmpos : ∀ t ∈ Ioi (1 : ℝ), 0 < t - 1 := fun t ht => sub_pos.mpr ht
    have htpow : ContinuousOn (fun t : ℝ => t ^ d) (Ioi 1) :=
      continuousOn_id.rpow continuousOn_const
        (fun t ht => Or.inl (ne_of_gt (htpos t ht)))
    have hbase : ContinuousOn (fun t : ℝ => 1 + t ^ d / Real.log D) (Ioi 1) :=
      continuousOn_const.add (htpow.div_const _)
    have hbasePos : ∀ t ∈ Ioi (1 : ℝ), 0 < 1 + t ^ d / Real.log D := by
      intro t ht
      have : 0 ≤ t ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg (htpos t ht).le _) hlog.le
      linarith
    have houter : ContinuousOn
        (fun t : ℝ => (1 + t ^ d / Real.log D) ^ (t - 1)) (Ioi 1) :=
      hbase.rpow (continuousOn_id.sub continuousOn_const)
        (fun t ht => Or.inl (ne_of_gt (hbasePos t ht)))
    have hshift : ContinuousOn
        (fun t : ℝ => (t - 1) ^ (H.kappaHat - 1 + 1)) (Ioi 1) :=
      (continuousOn_id.sub continuousOn_const).rpow continuousOn_const
        (fun t ht => Or.inl (ne_of_gt (htmpos t ht)))
    have hratio : ContinuousOn (fun t : ℝ => t / (t - 1)) (Ioi 1) :=
      continuousOn_id.div (continuousOn_id.sub continuousOn_const)
        (fun t ht => ne_of_gt (htmpos t ht))
    have hratioPow : ContinuousOn (fun t : ℝ => (t / (t - 1)) ^ Δ) (Ioi 1) :=
      hratio.rpow continuousOn_const (fun t ht =>
        Or.inl (ne_of_gt (div_pos (htpos t ht) (htmpos t ht))))
    have hTshift : ContinuousOn (fun t : ℝ => H.T sign.opposite (t - 1)) (Ioi 1) :=
      (hH.continuous sign.opposite).comp
        (continuousOn_id.sub continuousOn_const) (by
          intro t ht
          exact show 0 < t - 1 from sub_pos.mpr (show 1 < t from ht))
    exact ((houter.mul hshift).mul hTshift).mul hratioPow
  have hcont : Continuous (qDClamp H sign.opposite D d Δ τ) := by
    apply hqcont.comp_continuous
      (continuous_const.max continuous_id)
    intro t
    exact hτ1.trans_le (le_max_left τ t)
  refine ⟨hcont, ?_, ?_⟩
  · intro t ht
    rw [qDClamp_eq_of_le H sign.opposite D d Δ ht.1]
    exact (qD_pos H sign.opposite hD (hτ1.trans_le ht.1)
      (hH.positive sign.opposite (t - 1)
        (sub_pos.mpr (hτ1.trans_le ht.1)))).le
  · intro x hx y hy hxy
    change qDClamp H sign.opposite D d Δ τ y * y ≤
      qDClamp H sign.opposite D d Δ τ x * x
    rw [qDClamp_eq_of_le H sign.opposite D d Δ hx.1,
      qDClamp_eq_of_le H sign.opposite D d Δ hy.1]
    exact hii sign ⟨hτ.trans_le hx.1, hx.2⟩ ⟨hτ.trans_le hy.1, hy.2⟩ hxy

/-- Lemma 8.7 applied to the exact `q_D^∓` of (14.13), with Claim 14.6(ii)
discharging its weighted-antitonicity hypothesis. -/
theorem lemma8_7_qD_of_claim14_6_ii
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D z v w s τ σ K d Δ : ℝ} (sign : ErrorSign)
    (hH : Section13HatContract H β)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hτ : H.betaHat + sign.epsilon < τ) (hτσ : τ ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (qD H sign.opposite D d Δ) ≤
      (1 / s) * (∫ t in τ..σ, qD H sign.opposite D d Δ t) +
        (6 * K ^ 2 * qD H sign.opposite D d Δ τ / Real.log w) * (τ / s) := by
  let Q := qDClamp H sign.opposite D d Δ τ
  obtain ⟨hcont, hnonneg, hanti⟩ :=
    qDClamp_conditions_of_claim14_6_ii hH sign hD hτ hτσ hii
  have h87 := suzukiLemmaEightSevenDimensionOne hD hz2 hv2 hw2 hwv hvz
    hz hv hw hcont hnonneg hanti hK hlocal
  have hτpos : 0 < τ := by
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    rw [hH.betaHat_eq] at hτ
    linarith [hH.beta_gt_one]
  have hcoord : ∀ x ∈ Icc w v, Real.log D / Real.log x ∈ Icc τ σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD hτpos hτσ hv hw hx
  have hprime : suzukiLemmaEightSevenPrimeSum S D w v z Q =
      suzukiLemmaEightSevenPrimeSum S D w v z (qD H sign.opposite D d Δ) := by
    unfold suzukiLemmaEightSevenPrimeSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have ht := hcoord (p : ℝ) ⟨hp'.1, hp'.2.le⟩
    rw [show Q (Real.log D / Real.log p) =
        qD H sign.opposite D d Δ (Real.log D / Real.log p) by
      exact qDClamp_eq_of_le H sign.opposite D d Δ ht.1]
  have hint : (∫ t in τ..σ, Q t) =
      ∫ t in τ..σ, qD H sign.opposite D d Δ t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hτσ]
    intro t ht
    exact qDClamp_eq_of_le H sign.opposite D d Δ ht.1
  rw [hprime, hint, qDClamp_eq_of_le H sign.opposite D d Δ le_rfl] at h87
  exact h87

/-- At κ=1, the normalized endpoint `s⁻¹ Λ₀` is literally the current
source-correct error envelope `E_N`. -/
theorem one_div_mul_lambda_eq_errorEnvelope
    (H : Section13HatLayers) {N : ℕ} {D d s : ℝ} (hs : 0 < s) :
    (1 / s) * lambda H (ErrorSign.ofDepth N) D d 0 s =
      errorEnvelope H N D d s := by
  simp only [lambda, errorEnvelope, Section13HatLayers.kappaHat]
  norm_num [Real.rpow_one]
  field_simp [ne_of_gt hs]

/-- Finite algebraic assembly of (14.18): Lemma 8.7 plus Claim 14.6(i)--(iii)
gives the strict contraction main term `(1-1/σ)^(1-Δ) E_N`; only the explicit
Lemma-8.7 endpoint error remains.  No final Claim 14.5 or Lemma 14.4 assumption
is used. -/
theorem lemma8_7_qD_of_claim14_6_i_ii_iii
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D z v w s τ σ K d Δ : ℝ} {N : ℕ}
    (hH : Section13HatContract H β)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hτ : H.betaHat + (ErrorSign.ofDepth N).epsilon < τ)
    (hβs : H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ s)
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hs : 0 < s) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hi : Claim14_6_MonotoneLambdaPremise H D d σ)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ)
    (hiiiτ :
      (∫ t in τ..σ, qD H (ErrorSign.ofDepth N).opposite D d Δ t) <
        (1 - 1 / σ) ^ (1 - Δ) *
          lambda H (ErrorSign.ofDepth N) D d 0 τ) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (qD H (ErrorSign.ofDepth N).opposite D d Δ) <
      (1 - 1 / σ) ^ (1 - Δ) * errorEnvelope H N D d s +
        (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite D d Δ τ /
          Real.log w) * (τ / s) := by
  let sign := ErrorSign.ofDepth N
  have h87 := lemma8_7_qD_of_claim14_6_ii (S := S) (H := H) (sign := sign)
    hH hD hz2 hv2 hw2 hwv hvz hz hv hw hτ hτσ hK hlocal hii
  have hτdom : τ ∈ Icc (H.betaHat + sign.epsilon) σ := ⟨hτ.le, hτσ⟩
  have hsdom : s ∈ Icc (H.betaHat + sign.epsilon) σ :=
    ⟨hβs, hsτ.trans hτσ⟩
  have hlam : lambda H sign D d 0 τ ≤ lambda H sign D d 0 s :=
    hi sign 0 (Or.inl rfl) hsdom hτdom hsτ
  have hσ1 : 1 < σ := by
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    rw [hH.betaHat_eq] at hτ
    linarith [hH.beta_gt_one]
  have hcut0 : 0 ≤ (1 - 1 / σ) ^ (1 - Δ) := by
    apply Real.rpow_nonneg
    have hσ0 : 0 < σ := zero_lt_one.trans hσ1
    exact (sub_pos.mpr ((div_lt_one hσ0).mpr hσ1)).le
  have hint : (∫ t in τ..σ, qD H sign.opposite D d Δ t) <
      (1 - 1 / σ) ^ (1 - Δ) * lambda H sign D d 0 s :=
    hiiiτ.trans_le (mul_le_mul_of_nonneg_left hlam hcut0)
  have hscaled := mul_lt_mul_of_pos_left hint (one_div_pos.mpr hs)
  have hscaled' : (1 / s) * (∫ t in τ..σ, qD H sign.opposite D d Δ t) <
      (1 - 1 / σ) ^ (1 - Δ) * errorEnvelope H N D d s := by
    calc
      (1 / s) * (∫ t in τ..σ, qD H sign.opposite D d Δ t) <
          (1 / s) * ((1 - 1 / σ) ^ (1 - Δ) * lambda H sign D d 0 s) := hscaled
      _ = (1 - 1 / σ) ^ (1 - Δ) * errorEnvelope H N D d s := by
        dsimp [sign]
        rw [← one_div_mul_lambda_eq_errorEnvelope H hs]
        ring
  dsimp [sign] at h87 hscaled' ⊢
  exact h87.trans_lt (by nlinarith [hscaled'])


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
