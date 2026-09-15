import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectMainSubpowerEnergy
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectOuterMassConsumer
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectNormalization

/-! # Actual A/B/C join on one retained prefix

All numerical mass and energy inputs of the normalization consumer are
constructed from fixed-order coefficients and the actual arithmetic
producer. The explicit local scale expressions still require payment.
-/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem direct_retained_prefix_three_terms (k m : ℕ)
    {ε κ δ ρ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ Czero Cnonzero Csecondary Cτ Cjoint Ca Ccoeff Couter : ℝ,
      0 < Czero ∧ 0 < Cnonzero ∧ 0 < Csecondary ∧ 0 < Cτ ∧
      0 < Cjoint ∧ 0 < Ca ∧ 0 < Ccoeff ∧ 0 < Couter ∧
    ∀ (X : ℝ), 1 ≤ X →
    ∀ (N : Finset ℕ) (F : ℕ) (a : ℤ) (x η R S M Z T εSupport : ℝ)
      (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β γ ζ : ℕ → ℝ),
      a ≠ 0 → 0 ≤ R → 0 ≤ S → R ≤ X → S ≤ X → R * S ≤ X →
      0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → (∀ n ∈ N, (n : ℝ) ≤ 2 * T) →
      (∀ n ∈ N, n ≤ F) → (∀ n ∈ N, (n : ℝ) ≤ X) →
      1 < x → η < εSupport → x ^ εSupport ≤ T →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ n, |γ n| ≤ (fouvryTau m n : ℝ)) →
      (∀ n, |ζ n| ≤ (fouvryTau m n : ℝ)) →
      let E := Ccoeff * X ^ ρ
      let W := (E * E) ^ 2
      let Ez := W * (2 ^ j 1 : ℕ) * Czero *
        (wGramResonanceScaleBoxCard K F j : ℝ) * wGramResonanceScaleEnvelope K F j ε
      let Es := wGramSecondaryBaseCountBound K F j *
        (W * wGramSecondaryScaleEnvelope κ δ Cnonzero Csecondary a R S K F j cap)
      let Em := W * wGramDirectMainSubpowerFactor κ δ Cnonzero Ca a R S K j cap *
        wGramMainJointMean δ Cτ Cjoint a K F j
      wBlockAmplitude K j *
        ‖∑ t ∈ wCoprimeFiber x N S
          (wGramPrefix N a x η R S M Z K b j cap positive) c,
          (wExtractedCoefficient (betaClean β a)
            (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ t.1 : ℂ) *
            wExtractedArithmeticPhase a t.2 t.1‖ ≤
        wBlockAmplitude K j *
          Real.sqrt (Couter * X ^ ρ * (8 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * T)) *
          (Real.sqrt Ez + Real.sqrt Es + Real.sqrt Em) := by
  obtain ⟨Czero, Cnonzero, Csecondary, Cτ, Cjoint, Ca,
    hz, hn, hs, ht, hj, haC, henergy⟩ :=
      wSeparatedCorrelationEnergy_direct_main_subpower hε hκ hδ
  obtain ⟨Ccoeff, hc, hcoeff⟩ := direct_fixedOrder_envelopes k m hρ
  obtain ⟨Couter, ho, houter⟩ := direct_outerMass_subpower k m hρ
  refine ⟨Czero, Cnonzero, Csecondary, Cτ, Cjoint, Ca, Ccoeff, Couter,
    hz, hn, hs, ht, hj, haC, hc, ho, ?_⟩
  intro X hX N F a x η R S M Z T εSupport K b j cap positive c β γ ζ
    ha hR hS hRX hSX hRSX hM hZ hNT hNTup hNF hNX hx hη hSupport hβ hγ hζ
  let E := Ccoeff * X ^ ρ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hT : 0 < T := (Real.rpow_pos_of_pos (by linarith : 0 < x) εSupport).trans_le hSupport
  have hN : ∀ n ∈ N, 0 < n := by
    intro n hh
    exact_mod_cast hT.trans_le (hNT n hh)
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hh => (mem_Ioc.mp hh).1
  have hQX : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, (q : ℝ) ≤ X := by
    intro q hh
    exact (Nat.cast_le.mpr (mem_Ioc.mp hh).2).trans
      ((Nat.floor_le (mul_nonneg hR hS)).trans hRSX)
  obtain ⟨hb, _, hzeta, _⟩ := hcoeff X hX N β γ ζ a (highOmegaCutoff x) hNX hβ hγ hζ
  have hzs : ∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ E := by
    intro s hh
    exact hzeta s ((Nat.cast_le.mpr (mem_Ioc.mp hh).2).trans ((Nat.floor_le hS).trans hSX))
  let V := wGramPrefix N a x η R S M Z K b j cap positive
  have hV : V ⊆ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive := by
    intro t hh
    exact (mem_filter.mp hh).1
  have hm := houter X hX (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a x η R S T b K
    j positive V c β γ ζ hN hQ hNX hQX hR hS hRX hSX hT.le hNTup hβ hγ hζ hV
  have he := henergy N F a x η R S M Z T εSupport K b j cap positive c
    (betaClean β a) ζ E E ha hR hS hM hZ hNT hNF hx hη hSupport hE hE hb hzs
  have hlog : 0 ≤ Real.log (2 ^ (j 0 + 1) : ℕ) := by
    apply Real.log_nonneg
    have hp : 0 < (2 : ℕ) ^ (j 0 + 1) := by positivity
    exact_mod_cast (Nat.succ_le_of_lt hp)
  have hcount : 0 ≤ wGramSecondaryBaseCountBound K F j := by
    unfold wGramSecondaryBaseCountBound
    positivity
  have hzEnv := wGramResonanceScaleEnvelope_nonneg K F j ε
  have hsEnv := wGramSecondaryScaleEnvelope_nonneg hn.le κ δ Csecondary a R S K F j cap
  have hmEnv := wGramMainJointMean_nonneg δ Cτ Cjoint a K F j
  have hmFactor : 0 ≤ wGramDirectMainSubpowerFactor κ δ Cnonzero Ca a R S K j cap := by
    unfold wGramDirectMainSubpowerFactor
    positivity
  have he' : wSeparatedCorrelationEnergy x N S V c K (betaClean β a) ζ a ≤
      (E * E) ^ 2 * (2 ^ j 1 : ℕ) * Czero *
        (wGramResonanceScaleBoxCard K F j : ℝ) * wGramResonanceScaleEnvelope K F j ε +
      wGramSecondaryBaseCountBound K F j *
        ((E * E) ^ 2 * wGramSecondaryScaleEnvelope κ δ Cnonzero Csecondary a R S K F j cap) +
      ((E * E) ^ 2 * wGramDirectMainSubpowerFactor κ δ Cnonzero Ca a R S K j cap) *
        wGramMainJointMean δ Cτ Cjoint a K F j := by
    simpa only [add_assoc] using he
  exact directNormalization_actual_cauchy_three hN hQ
    (wGramPrefix_subset N a x η R S M Z K b j cap positive) c j
    (betaClean β a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ
    (by positivity) (by positivity) (by positivity) (by positivity) hm he'

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
