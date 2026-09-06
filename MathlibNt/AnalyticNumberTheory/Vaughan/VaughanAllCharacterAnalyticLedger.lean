

import MathlibNt.AnalyticNumberTheory.LargeSieve.VonMangoldtConductorCorrection
import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit

/-!
 # All-character nonprincipal Vaughan ledger and Type-II scale audit

This module only assembles proved producers.  It keeps the principal character
out, keeps the full prefix maximum on the all-character side, and records that
the currently proved tensor Type-II estimate is only an endpoint estimate.
Consequently no Standard Bombieri--Vinogradov theorem is claimed.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The coefficient `1`, used to specialize Vaughan's identity to `Λ`. -/
def vaughanUnitIntegerCoeff (_ : ℤ) : ℂ := 1

/-- One conductor-weighted primitive prefix-maximal lane. -/
def vaughanConductorPrefixLane (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 Q, imprimitiveConductorWeight Q d *
    ∑ ψ : PrimitiveCharacter d,
      primitiveCharacterPrefixMaxSquare a 0 N d ψ

/-- The closed `Λ`-specific conductor correction, with every `N,Q,log` factor
kept literal. -/
def vaughanLambdaConductorCorrectionScale (N Q : ℕ) : ℝ :=
  2 * (Q : ℝ) ^ 2 *
    (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2

lemma vaughanLambdaCoeff_unit_eq (n : ℤ) :
    vaughanLambdaCoeff vaughanUnitIntegerCoeff n = vonMangoldtIntegerCoeff n := by
  simp [vaughanLambdaCoeff, vaughanUnitIntegerCoeff, vonMangoldtIntegerCoeff]

/-- The real all-character, nonprincipal Vaughan ledger.  This theorem combines
(1) exact conductor grouping, (2) the full prefix-maximal three-piece Vaughan
identity, and (3) the proved `Λ`-specific `Q² polylog` change-level correction.
The principal character is absent from the left side and is not estimated here. -/
theorem weighted_allCharacter_nonprincipal_vaughan_analytic_ledger (N Q u v : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ nonprincipalCharacters q,
        characterPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N) ≤
      6 * (vaughanConductorPrefixLane (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N Q +
        vaughanConductorPrefixLane (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N Q +
        vaughanConductorPrefixLane (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N Q) +
      vaughanLambdaConductorCorrectionScale N Q := by
  have hall := weighted_allCharacter_nonprincipal_vonMangoldt_prefix_ledger N Q
  have hsplit :
      vaughanConductorPrefixLane vonMangoldtIntegerCoeff N Q ≤
        3 * (vaughanConductorPrefixLane
              (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N Q +
          vaughanConductorPrefixLane
              (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N Q +
          vaughanConductorPrefixLane
              (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N Q) := by
    have hcoeff : vaughanLambdaCoeff vaughanUnitIntegerCoeff = vonMangoldtIntegerCoeff :=
      funext vaughanLambdaCoeff_unit_eq
    unfold vaughanConductorPrefixLane
    calc
      _ = ∑ d ∈ Finset.Icc 2 Q, imprimitiveConductorWeight Q d *
          ∑ ψ : PrimitiveCharacter d,
            primitiveCharacterPrefixMaxSquare
              (vaughanLambdaCoeff vaughanUnitIntegerCoeff) 0 N d ψ := by
          rw [hcoeff]
      _ ≤ ∑ d ∈ Finset.Icc 2 Q, imprimitiveConductorWeight Q d *
          ∑ ψ : PrimitiveCharacter d,
            (3 * (primitiveCharacterPrefixMaxSquare
                    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) 0 N d ψ +
                  primitiveCharacterPrefixMaxSquare
                    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) 0 N d ψ +
                  primitiveCharacterPrefixMaxSquare
                    (vaughanSmallCoeff vaughanUnitIntegerCoeff v) 0 N d ψ)) := by
          apply Finset.sum_le_sum
          intro d hd
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro ψ hψ
            exact primitiveCharacterPrefixMaxSquare_le_three _ _ _ _ N d ψ
              (fun n _ => vaughanLambdaCoeff_eq vaughanUnitIntegerCoeff u v n)
          · unfold imprimitiveConductorWeight
            positivity
      _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          ring
  calc
    _ ≤ 2 * vaughanConductorPrefixLane vonMangoldtIntegerCoeff N Q +
        vaughanLambdaConductorCorrectionScale N Q := by
      simpa [vaughanConductorPrefixLane, vaughanLambdaConductorCorrectionScale] using hall
    _ ≤ _ := by linarith only [hsplit]

/-- The exact endpoint-only Type-II scale delivered by the current producers on
one conductor window `C ≤ conductor ≤ 2C` and one Vaughan outer shell `2^k`.
It includes, in order: linear imprimitive transport, outer Möbius Cauchy, the
primitive large-sieve charge, and the unconditional constant-27 tensor moment. -/
def existingTypeIIEndpointWindowScale (N Q C k B : ℕ) : ℝ :=
  ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
    ((2 ^ k : ℕ) : ℝ) *
    ((N : ℝ) +
      (2 * (Nat.ceil (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
        ((2 * C : ℕ) : ℝ) ^ 2) *
    (27 * (B : ℝ) ^ 2 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5)

/-- Actual assembly of the current Type-II producers.  This is deliberately an
endpoint square at `y=N`, not a maximum over all prefixes. -/
theorem weighted_imprimitive_vaughanTypeII_endpoint_window_unconditional
    (N Q C u v k l B : ℕ) (hC : 0 < C)
    (hB : ∀ n ≤ N, ‖(vaughanUnitIntegerCoeff n : ℂ)‖ ≤ (B : ℝ)) :
    (∑ d ∈ Finset.Icc C (2 * C), imprimitiveConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d,
        ‖vaughanTypeIICanonicalBilinearBlock (fun _ => (1 : ℂ))
          N N u v k l d ψ‖ ^ 2) ≤
      existingTypeIIEndpointWindowScale N Q C k B := by
  let F : (d : ℕ) → PrimitiveCharacter d → ℝ := fun d ψ =>
    ‖vaughanTypeIICanonicalBilinearBlock (fun _ => (1 : ℂ))
      N N u v k l d ψ‖ ^ 2
  have htransport := imprimitive_conductor_window_le_weighted_primitive_linear
    F (fun _ _ => sq_nonneg _) Q C hC
  have hprimitive := weighted_primitive_vaughanCanonicalBilinear
    (fun _ => (1 : ℂ)) N N u v k l (2 * C) (Nat.mul_pos (by decide) hC)
  have hmu := vaughanMoebiusCoeffEnergy_le_card
    (vaughanCanonicalDyadicBlock N u k)
  have hcard : ((vaughanCanonicalDyadicBlock N u k).card : ℝ) ≤ (2 ^ k : ℕ) := by
    exact_mod_cast card_vaughanCanonicalDyadicBlock_le_pow N u k
  have htensor := vaughanBilinearTensorEnergy_canonical_le_BVScale_unconditional
    (fun _ => (1 : ℂ)) N N u v k l B (by simpa [vaughanUnitIntegerCoeff] using hB)
  have hls0 : 0 ≤ vaughanBilinearLargeSieveConstant N (2 * C) := by
    unfold vaughanBilinearLargeSieveConstant largeSieveBound
    positivity
  have ht0 : 0 ≤ vaughanBilinearTensorEnergy vaughanMangoldtCoeff
      (fun _ => (1 : ℂ)) N (vaughanCanonicalDyadicBlock N u k)
      (vaughanCanonicalDyadicBlock N v l) := by
    unfold vaughanBilinearTensorEnergy
    positivity
  have hblock :
      (∑ d ∈ Finset.Icc 1 (2 * C), ((d : ℝ) / (d.totient : ℝ)) *
        ∑ ψ : PrimitiveCharacter d, F d ψ) ≤
        ((2 ^ k : ℕ) : ℝ) * vaughanBilinearLargeSieveConstant N (2 * C) *
          (27 * (B : ℝ) ^ 2 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5) := by
    refine hprimitive.trans ?_
    calc
      _ ≤ ((vaughanCanonicalDyadicBlock N u k).card : ℝ) *
          vaughanBilinearLargeSieveConstant N (2 * C) *
          vaughanBilinearTensorEnergy vaughanMangoldtCoeff
            (fun _ => (1 : ℂ)) N (vaughanCanonicalDyadicBlock N u k)
            (vaughanCanonicalDyadicBlock N v l) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hmu hls0) ht0
      _ ≤ ((2 ^ k : ℕ) : ℝ) * vaughanBilinearLargeSieveConstant N (2 * C) *
          (27 * (B : ℝ) ^ 2 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hcard hls0) htensor ht0
            (mul_nonneg (Nat.cast_nonneg _) hls0)
  refine htransport.trans ?_
  unfold existingTypeIIEndpointWindowScale
  rw [vaughanBilinearLargeSieveConstant_eq_explicit N (2 * C)
    (Nat.mul_pos (by decide) hC)] at hblock
  have hfac : 0 ≤ ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) :=
    mul_nonneg (Nat.cast_nonneg (Q / C))
      (conductorHarmonicFactor_nonneg (Q / C))
  have hh := mul_le_mul_of_nonneg_left hblock hfac
  convert hh using 1 <;> first | rfl | ring

/-- Algebraic payment audit: the length term of the primitive large sieve pays
`N` a second time after the tensor moment has already paid its physical row mass
`N`; the outer-shell Cauchy separately pays `2^k`. -/
theorem existingTypeIIEndpointWindowScale_split (N Q C k B : ℕ) :
    existingTypeIIEndpointWindowScale N Q C k B =
      27 * (B : ℝ) ^ 2 * ((Q / C : ℕ) : ℝ) *
        conductorHarmonicFactor (Q / C) * ((2 ^ k : ℕ) : ℝ) *
        Real.log (N + 1 : ℕ) ^ 5 *
        ((N : ℝ) ^ 2 +
          (N : ℝ) *
            ((2 * (Nat.ceil (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
              ((2 * C : ℕ) : ℝ) ^ 2)) := by
  unfold existingTypeIIEndpointWindowScale
  ring

/-- Formal scale obstruction.  Once every non-log factor is at least one, the
current endpoint Type-II route is at least `27 B² N² log(N+1)^5`; hence it cannot
supply an inverse-log saving over the square-mean BV benchmark `B²N²/log^A`.
This is a statement about this produced majorant, not a lower bound on the true
character sum. -/
theorem existingTypeIIEndpointWindowScale_not_BV_saving
    (N Q C k B A : ℕ)
    (hN : 0 < N) (hBC : C ≤ Q) (hC : 0 < C) (hB : 0 < B)
    (hlog : 1 < Real.log (N + 1 : ℕ) ^ A) :
    ¬ existingTypeIIEndpointWindowScale N Q C k B ≤
        (B : ℝ) ^ 2 * (N : ℝ) ^ 2 / Real.log (N + 1 : ℕ) ^ A := by
  have hquot : 1 ≤ Q / C := (Nat.le_div_iff_mul_le hC).2 (by simpa using hBC)
  have hharm : 1 ≤ conductorHarmonicFactor (Q / C) := by
    unfold conductorHarmonicFactor
    calc
      (1 : ℝ) = ∑ e ∈ Finset.Icc (1 : ℕ) 1, (e : ℝ)⁻¹ := by norm_num
      _ ≤ ∑ e ∈ Finset.Icc 1 (Q / C), (e : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right hquot
        · intro e he hnot
          positivity
  have hpow : (1 : ℝ) ≤ (2 ^ k : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have hL : 1 < Real.log (N + 1 : ℕ) := by
    by_contra h
    have hle : Real.log (N + 1 : ℕ) ≤ 1 := le_of_not_gt h
    have hnonneg : 0 ≤ Real.log (N + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))
    exact (not_le_of_gt hlog) (pow_le_one₀ hnonneg hle)
  intro hBV
  have hscale :
      27 * (B : ℝ) ^ 2 * (N : ℝ) ^ 2 * Real.log (N + 1 : ℕ) ^ 5 ≤
        existingTypeIIEndpointWindowScale N Q C k B := by
    rw [existingTypeIIEndpointWindowScale_split]
    have hqR : (1 : ℝ) ≤ ((Q / C : ℕ) : ℝ) := by exact_mod_cast hquot
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hmod0 : 0 ≤
        (2 * (Nat.ceil (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          ((2 * C : ℕ) : ℝ) ^ 2 := by positivity
    have hL50 : 0 ≤ Real.log (N + 1 : ℕ) ^ 5 := by positivity
    have hbase0 : 0 ≤ 27 * (B : ℝ) ^ 2 * Real.log (N + 1 : ℕ) ^ 5 := by positivity
    calc
      27 * (B : ℝ) ^ 2 * (N : ℝ) ^ 2 * Real.log (N + 1 : ℕ) ^ 5 =
          (27 * (B : ℝ) ^ 2 * Real.log (N + 1 : ℕ) ^ 5) * 1 * 1 * 1 *
            (N : ℝ) ^ 2 := by ring
      _ ≤ (27 * (B : ℝ) ^ 2 * Real.log (N + 1 : ℕ) ^ 5) *
          ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
          ((2 ^ k : ℕ) : ℝ) * (N : ℝ) ^ 2 := by gcongr
      _ ≤ 27 * (B : ℝ) ^ 2 * ((Q / C : ℕ) : ℝ) *
          conductorHarmonicFactor (Q / C) * ((2 ^ k : ℕ) : ℝ) *
          Real.log (N + 1 : ℕ) ^ 5 *
          ((N : ℝ) ^ 2 + (N : ℝ) *
            ((2 * (Nat.ceil (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
              ((2 * C : ℕ) : ℝ) ^ 2)) := by
        let P : ℝ := 27 * (B : ℝ) ^ 2 * ((Q / C : ℕ) : ℝ) *
          conductorHarmonicFactor (Q / C) * ((2 ^ k : ℕ) : ℝ) *
          Real.log (N + 1 : ℕ) ^ 5
        have hP0 : 0 ≤ P := by
          dsimp [P]
          positivity
        have hadd : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 + (N : ℝ) *
            ((2 * (Nat.ceil (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
              ((2 * C : ℕ) : ℝ) ^ 2) :=
          le_add_of_nonneg_right (mul_nonneg hN0 hmod0)
        have hh := mul_le_mul_of_nonneg_left hadd hP0
        dsimp [P] at hh
        convert hh using 1 <;> first | rfl | ring
  have hupper := hscale.trans hBV
  have hden : 0 < Real.log (N + 1 : ℕ) ^ A := lt_trans (by norm_num) hlog
  have hBN : 0 < (B : ℝ) ^ 2 * (N : ℝ) ^ 2 := mul_pos (sq_pos_of_pos (by exact_mod_cast hB))
    (sq_pos_of_pos (by exact_mod_cast hN))
  have hright : (B : ℝ) ^ 2 * (N : ℝ) ^ 2 /
      Real.log (N + 1 : ℕ) ^ A < (B : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
    exact div_lt_self hBN hlog
  have hleft : (B : ℝ) ^ 2 * (N : ℝ) ^ 2 <
      27 * (B : ℝ) ^ 2 * (N : ℝ) ^ 2 * Real.log (N + 1 : ℕ) ^ 5 := by
    have hL5 : 1 < Real.log (N + 1 : ℕ) ^ 5 := one_lt_pow₀ hL (by decide)
    nlinarith
  exact (not_lt_of_ge hupper) (hright.trans hleft)

/-- Minimal missing Type-II interface.  Unlike the proved endpoint theorem, this
contract retains the maximum over every prefix before summing over characters
and conductors, and it asks for the inverse-log square-mean scale with no repeated
outer-shell/row-length payment.  It is intentionally a named `Prop`, not asserted
as a theorem. -/
def VaughanTypeIIPrefixTensorRepair (N Q u v A : ℕ) (K : ℝ) : Prop :=
  vaughanConductorPrefixLane
      (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N Q ≤
    K * (N : ℝ) ^ 2 / Real.log (N + 1 : ℕ) ^ A

end

end AnalyticNumberTheory.LargeSieve
