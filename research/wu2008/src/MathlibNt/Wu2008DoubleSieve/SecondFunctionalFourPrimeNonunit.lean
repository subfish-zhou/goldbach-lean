import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitFinite
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitJoinedSource

namespace Wu2008DoubleSieve
open Finset FourthRowPhiOmega2
open scoped Classical
namespace FourPrimeNonunit
open FourPrimeUnit (word)

noncomputable def actualProfiles {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) : Finset Gamma16Profile :=
  profiles N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

noncomputable def actualFibre (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (j : Fin 4) : Gamma16Profile → Finset ℕ :=
  fibre N (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

noncomputable def actualSource {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) : ℝ :=
  source N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

noncomputable def actualEnvelope {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) : ℝ :=
  envelope N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

/-- The accepted four nonunit sums are exactly the original weighted labels. -/
theorem actual_source_eq {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) :
    actualSource N δ p W j = secondFunctionalFourPrimeNonunitSum p N δ W j := rfl

theorem actual_source_labels {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) :
    secondFunctionalFourPrimeNonunitSum p N δ W j =
      ∑ x ∈ labels N W (fun d => wuLocalCutoff N δ d p.S)
        (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
        (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s)
        (word j), (convolutionCoeff W x.1 : ℝ) := source_labels _ _ _ _ _ _ _ _

theorem actual_source_le {i N : ℕ} {δ : ℝ} (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) (j : Fin 4) :
    secondFunctionalFourPrimeNonunitSum p N δ W j ≤ actualEnvelope N δ p W j :=
  source_le_envelope hdpos hN he j

/-- A finite sum of literal last-prime/output-prime fibre cardinalities. -/
theorem actual_envelope_eq {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) :
    actualEnvelope N δ p W j = ∑ x ∈ actualProfiles N δ p W j,
      (convolutionCoeff W x.1 : ℝ) * (actualFibre N δ p j x).card := rfl

end FourPrimeNonunit

noncomputable def secondFunctionalSwitchedGammaLedger (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ W j) +
    (∑ j : Fin 4, FourPrimeNonunit.actualEnvelope N δ p W j) +
    secondFunctionalMotherGammaSum p N δ W 20 + secondFunctionalMotherGammaSum p N δ W 21

theorem secondFunctional_nonunit_ledger_le (p : SecondFunctionalParameters)
    {i N : ℕ} {δ : ℝ} (W : Fin i → Finset ℕ)
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d) (hN : 4 ≤ N) (he : Even N) :
    secondFunctionalNonunitGammaLedger p N δ W ≤ secondFunctionalSwitchedGammaLedger p N δ W := by
  have hsum := sum_le_sum (s := (univ : Finset (Fin 4)))
    (fun j _ => FourPrimeNonunit.actual_source_le p W hdpos hN he j (δ := δ))
  unfold secondFunctionalNonunitGammaLedger secondFunctionalSwitchedGammaLedger
  linarith only [hsum]

/-- The accepted source mother with only Gamma16--19 enlarged, at the same threshold.
This is finite masked switching, not a Buchstab or BV estimate. -/
theorem secondFunctional_fourprime_nonunit_joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
          secondFunctionalSwitchedGammaLedger p N δ (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := secondFunctional_unit_joined_source p hp hs hs3 hS hS5
    k hk hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN he i Δ V hb
  have hN4 := hT4.trans hN
  have hδhalf : δ < 1/2 := by linarith
  exact (hT N hN he i Δ V hb).trans (add_le_add le_rfl
    (secondFunctional_nonunit_ledger_le p (convolutionWuWindows N Δ V)
      (fun _ hd => (omega3_source_support_le_Q (by omega) hδ hδhalf hb hd).1) hN4 he))

end Wu2008DoubleSieve
