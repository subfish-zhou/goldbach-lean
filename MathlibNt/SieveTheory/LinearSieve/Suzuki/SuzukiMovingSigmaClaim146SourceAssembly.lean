import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146Quantitative
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaDecay

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-!
# Source-faithful moving assembly of Claim 14.6(iii)

The source splits at the fixed point `M + 2`.  The compact head is controlled by
Lemma 13.3/(14.2), whereas the moving tail is controlled by the large-`s` DDE
argument.  Proposition 13.1(iii) is used only to make the endpoint value at
`M + 2` be `O(M⁻²)` relative to every starting value in the compact range.

`Section13HatContract` contains only qualitative convergence
`weightedHat → 0`; it has no quantitative rate from which this `M⁻²` estimate
can be selected.  Accordingly the first definition below is the minimal extra
DDE-tail interface.  It is not Claim 14.6(iii), and it is independent of `D`,
`d`, `Δ`, `sourceSigma`, and the `qD` integral.
-/

/-- Minimal quantitative consequence of Proposition 13.1(iii) needed in the
moving proof.  The source gives the stronger `(M log (eM))⁻²` decay; only its
weaker `C M⁻²` consequence, together with the monotone comparison back to every
`3 ≤ s ≤ M`, is retained here. -/
def Proposition131TailDecayContract (H : Section13HatLayers) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (sign : ErrorSign) (M s : ℝ),
    4 ≤ M → 2 + sign.epsilon ≤ s → s ≤ M →
    weightedHat H sign (M + 2) ≤
      (C / M ^ 2) * weightedHat H sign s

/-- The fixed-compact perturbation factors tend uniformly to one.  This tiny
interface records only the factor `2` needed to transfer Proposition 13.1(iii)
from `weightedHat` to `lambda`; it is elementary and separate from the DDE. -/
def FixedCompactPerturbationContract (d M : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    ∀ (sign : ErrorSign) (s : ℝ), 2 + sign.epsilon ≤ s → s ≤ M →
      perturbation D d 0 (M + 2) ≤ 2 * perturbation D d 0 s

/-- Source Lemma 13.3/(14.2), after the fixed compact prefactors have been
absorbed.  The positive first-order saving is deliberately `gap/(4M)`; here
`gap = Δ₀-Δ`, correcting the reversed sign in the last two displays on printed
p. 92.  This is a head estimate, not the final moving claim. -/
def Lemma133WeightedHeadContract
    (H : Section13HatLayers) (d Δ gap M : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    ∀ (sign : ErrorSign) (s : ℝ), 2 + sign.epsilon ≤ s → s ≤ M →
      (∫ t in s..M + 2, qD H sign.opposite D d Δ t) ≤
        (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
          (1 - gap / (4 * M)) * lambda H sign D d 0 s

/-- The already established large-`s` differential/DDE tail, uniform up to the
actual moving source cutoff.  Its left endpoint is fixed before `D` is chosen. -/
def MovingDDEWeightedTailContract
    (H : Section13HatLayers) (d Δ M : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    M + 2 ≤ sourceSigma D d ∧
    (∀ (sign : ErrorSign) (s : ℝ), M ≤ s →
        s ≤ sourceSigma D d →
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
            lambda H sign D d 0 s) ∧
    (∀ (sign : ErrorSign) (s : ℝ), s ≤ M →
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) =
          (∫ t in s..M + 2, qD H sign.opposite D d Δ t) +
          (∫ t in M + 2..sourceSigma D d,
            qD H sign.opposite D d Δ t))

/-- A fixed cutoff chosen solely from the Proposition-13.1 constant and the
positive source gap.  The `16` leaves twice the margin actually needed below. -/
noncomputable def claim146iiiFixedM (C gap : ℝ) : ℝ :=
  max 4 (16 * C / gap + 1)

lemma claim146iiiFixedM_margin {C gap : ℝ}
    (hC : 0 ≤ C) (hgap : 0 < gap) :
    let M := claim146iiiFixedM C gap
    4 ≤ M ∧ 2 * C / M ^ 2 < gap / (4 * M) := by
  dsimp [claim146iiiFixedM]
  let M : ℝ := max 4 (16 * C / gap + 1)
  have hM4 : 4 ≤ M := le_max_left _ _
  have hMpos : 0 < M := by linarith
  have hMlower : 16 * C / gap + 1 ≤ M := le_max_right _ _
  have hcross : 16 * C < gap * M := by
    have hmul := mul_le_mul_of_nonneg_left hMlower hgap.le
    have hident : gap * (16 * C / gap + 1) = 16 * C + gap := by
      field_simp [ne_of_gt hgap]
    rw [hident] at hmul
    linarith
  refine ⟨hM4, ?_⟩
  rw [div_lt_div_iff₀ (sq_pos_of_pos hMpos) (mul_pos (by norm_num) hMpos)]
  nlinarith [sq_nonneg M]

private lemma lambda_pos_of_source_range
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {D d s : ℝ} (hD : 1 < D)
    (hs : 2 + sign.epsilon ≤ s) :
    0 < lambda H sign D d 0 s := by
  have hs1 : 1 < s := by
    cases sign <;> simp [ErrorSign.epsilon] at hs ⊢ <;> linarith
  have hlog : 0 < Real.log D := Real.log_pos hD
  rw [lambda_eq_perturb_mul_weightedHat]
  apply mul_pos
  · apply Real.rpow_pos_of_pos
    have : 0 ≤ s ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg (zero_le_one.trans hs1.le) _) hlog.le
    simpa only [add_zero] using (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 1) this)
  · exact mul_pos (sq_pos_of_pos (zero_lt_one.trans hs1))
      (hH.positive sign s (zero_lt_one.trans hs1))

/-- Proposition 13.1(iii), plus the harmless fixed-compact perturbation bound,
turns the DDE tail endpoint into the required `O(M⁻²)` multiple of the value at
any compact-range starting point. -/
lemma lambda_fixed_endpoint_decay
    {H : Section13HatLayers} {d C M D s : ℝ}
    (sign : ErrorSign) (hM : 4 ≤ M) (hD : 1 < D)
    (hs : 2 + sign.epsilon ≤ s)
    (h131 : weightedHat H sign (M + 2) ≤
      (C / M ^ 2) * weightedHat H sign s)
    (hpert : perturbation D d 0 (M + 2) ≤
      2 * perturbation D d 0 s)
    (hpos : ∀ sign t, 0 < t → 0 < H.T sign t) :
    lambda H sign D d 0 (M + 2) ≤
      (2 * C / M ^ 2) * lambda H sign D d 0 s := by
  have hMpos : 0 < M := by linarith
  have hspos : 0 < s := by
    cases sign <;> simp [ErrorSign.epsilon] at hs <;> linarith
  have hWend : 0 ≤ weightedHat H sign (M + 2) := by
    exact mul_nonneg (sq_nonneg _) (hpos sign (M + 2) (by linarith)).le
  have hPs : 0 ≤ perturbation D d 0 s := by
    exact Real.rpow_nonneg (by
      have hlog := (Real.log_pos hD).le
      have hu : 0 ≤ s ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg hspos.le _) hlog
      simpa [perturbation] using (show 0 ≤ 1 + s ^ d / Real.log D by linarith)) _
  rw [lambda_eq_perturb_mul_weightedHat, lambda_eq_perturb_mul_weightedHat]
  calc
    perturbation D d 0 (M + 2) * weightedHat H sign (M + 2) ≤
        (2 * perturbation D d 0 s) * weightedHat H sign (M + 2) :=
      mul_le_mul_of_nonneg_right hpert hWend
    _ ≤ (2 * perturbation D d 0 s) *
        ((C / M ^ 2) * weightedHat H sign s) :=
      mul_le_mul_of_nonneg_left h131 (mul_nonneg (by norm_num) hPs)
    _ = (2 * C / M ^ 2) *
        (perturbation D d 0 s * weightedHat H sign s) := by ring

/-- Source-faithful head+tail assembly of moving Claim 14.6(iii).

The cutoff is fixed as `M = max 4 (16 C / gap + 1)` before any `D` threshold
is chosen.  Consequently the tail coefficient `2C/M²` is strictly smaller
than the head saving `gap/(4M)`.  The theorem does not package its own
conclusion as a premise: its four inputs are respectively Proposition 13.1
quantitative decay, elementary compact perturbation, Lemma 13.3 weighted head,
and the large-range DDE tail. -/
theorem moving_claim14_6_iii_of_source_contracts
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {d Δ gap : ℝ} (_hΔ : Δ < 1) (hgap : 0 < gap)
    (h131 : Proposition131TailDecayContract H)
    (hpertAll : ∀ C : ℝ, 0 ≤ C →
      FixedCompactPerturbationContract d (claim146iiiFixedM C gap))
    (hheadAll : ∀ C : ℝ, 0 ≤ C →
      Lemma133WeightedHeadContract H d Δ gap (claim146iiiFixedM C gap))
    (htailAll : ∀ C : ℝ, 0 ≤ C →
      MovingDDEWeightedTailContract H d Δ (claim146iiiFixedM C gap)) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ (sign : ErrorSign) (s : ℝ),
        2 + sign.epsilon ≤ s → s ≤ sourceSigma D d →
        (∫ t in s..sourceSigma D d,
            qD H sign.opposite D d Δ t) <
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
            lambda H sign D d 0 s := by
  obtain ⟨C, hC, h131C⟩ := h131
  let M : ℝ := claim146iiiFixedM C gap
  have hmargin := claim146iiiFixedM_margin hC hgap
  change 4 ≤ M ∧ 2 * C / M ^ 2 < gap / (4 * M) at hmargin
  obtain ⟨hM4, hcoef⟩ := hmargin
  obtain ⟨Dp, hDp, hpert⟩ := hpertAll C hC
  obtain ⟨Dh, hDh, hhead⟩ := hheadAll C hC
  obtain ⟨Dt, hDt, htail⟩ := htailAll C hC
  let D₀ : ℝ := max Dp (max Dh Dt)
  refine ⟨D₀, hDp.trans_le (le_max_left _ _), ?_⟩
  intro D hD sign s hs hsσ
  have hDpD : Dp ≤ D := (le_max_left Dp (max Dh Dt)).trans hD
  have hDhD : Dh ≤ D :=
    (le_max_left Dh Dt).trans ((le_max_right Dp (max Dh Dt)).trans hD)
  have hDtD : Dt ≤ D :=
    (le_max_right Dh Dt).trans ((le_max_right Dp (max Dh Dt)).trans hD)
  have hD1 : 1 < D := hDp.trans_le hDpD
  obtain ⟨hMσ, hlarge, hsplit⟩ := htail D hDtD
  by_cases hMs : M ≤ s
  · exact hlarge sign s hMs hsσ
  · have hsM : s ≤ M := (lt_of_not_ge hMs).le
    have hheadD := hhead D hDhD sign s hs hsM
    have hpertD := hpert D hDpD sign s hs hsM
    have hlambdaDecay : lambda H sign D d 0 (M + 2) ≤
        (2 * C / M ^ 2) * lambda H sign D d 0 s :=
      lambda_fixed_endpoint_decay sign hM4 hD1 hs
        (h131C sign M s hM4 hs hsM) hpertD hH.positive
    have htailD := hlarge sign (M + 2) (by linarith) hMσ
    have hsplitD := hsplit sign s hsM
    let K : ℝ := (1 - 1 / sourceSigma D d) ^ (1 - Δ)
    let L : ℝ := lambda H sign D d 0 s
    have hKpos : 0 < K := Real.rpow_pos_of_pos (by
      have hσ1 : 1 < sourceSigma D d := by linarith [hM4, hMσ]
      have hσpos : 0 < sourceSigma D d := zero_lt_one.trans hσ1
      exact sub_pos.mpr ((div_lt_one hσpos).mpr hσ1)) _
    have hK0 : 0 ≤ K := hKpos.le
    have hL : 0 < L := lambda_pos_of_source_range hH sign hD1 hs
    have htailBound :
        (∫ t in M + 2..sourceSigma D d,
            qD H sign.opposite D d Δ t) <
          K * ((2 * C / M ^ 2) * L) := by
      exact htailD.trans_le (mul_le_mul_of_nonneg_left hlambdaDecay hK0)
    rw [hsplitD]
    have hsum :
        K * (1 - gap / (4 * M)) * L +
            K * ((2 * C / M ^ 2) * L) < K * L := by
      have hcoefsum : 1 - gap / (4 * M) + 2 * C / M ^ 2 < 1 := by
        linarith
      calc
        K * (1 - gap / (4 * M)) * L + K * ((2 * C / M ^ 2) * L) =
            (K * L) * (1 - gap / (4 * M) + 2 * C / M ^ 2) := by ring
        _ < (K * L) * 1 := mul_lt_mul_of_pos_left hcoefsum (mul_pos hKpos hL)
        _ = K * L := by ring
    change (∫ t in s..M + 2, qD H sign.opposite D d Δ t) +
        (∫ t in M + 2..sourceSigma D d,
          qD H sign.opposite D d Δ t) < K * L
    exact (add_lt_add_of_le_of_lt (by simpa [K, L, mul_assoc] using hheadD)
      htailBound).trans hsum


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
