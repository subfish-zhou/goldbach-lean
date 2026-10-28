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


/-- A fixed cutoff chosen solely from the Proposition-13.1 constant and the
positive source gap.  The `16` leaves twice the margin actually needed below. -/
noncomputable def claim146iiiFixedM (C gap : ℝ) : ℝ :=
  max 4 (16 * C / gap + 1)


/-- The source weight tends to one for every fixed real exponent. -/
lemma tendsto_source_weight (gap : ℝ) :
    Tendsto (fun σ : ℝ => (1 - 1 / σ) ^ gap) atTop (𝓝 1) := by
  have hinv : Tendsto (fun σ : ℝ => 1 / σ) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  have hbase : Tendsto (fun σ : ℝ => 1 - 1 / σ) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  simpa using hbase.rpow_const (Or.inl one_ne_zero)

/-- The perturbed layer is positive throughout the parity-dependent source range. -/
lemma lambda_pos_of_source_range
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


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
