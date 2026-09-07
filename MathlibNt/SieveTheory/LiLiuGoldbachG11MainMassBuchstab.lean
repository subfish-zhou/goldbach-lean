import MathlibNt.SieveTheory.LiLiuGoldbachG11MainMassTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG11BuchstabEndpointMass

open scoped BigOperators
open Finset LiLiuPrereqBuchstab

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- An actual-label finite sum, not a prime integral or a numerical evaluation. -/
def goldbachG11BuchstabUpperMass (N : ℕ) (η : ℝ) : ℝ :=
  ∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
    (goldbachG11BuchstabMass ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 +
      η * ((N : ℝ) / goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ))

/-- Consume the nonempty upper endpoint, not the empty epsilon-one window difference. -/
theorem goldbachG11_rough_upper_buchstab (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
        (roughCount ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 : ℝ) ≤
          goldbachG11BuchstabMass ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 +
            η * ((N : ℝ) / goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ) := by
  obtain ⟨N₀, hN₀, hend⟩ :=
    goldbachG11_buchstab_endpoints 1 (by norm_num) (by norm_num) (2 * η) (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN v hv
  have herr := (hend N hN v hv).2.2.2.2.1
  have hhalf : 2 * η / 2 = η := by ring
  rw [hhalf] at herr
  exact (sub_le_iff_le_add'.mp ((le_abs_self _).trans herr))

theorem goldbachG11FullRoughMass_le_buchstabUpper (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG11FullRoughMass N ≤ goldbachG11BuchstabUpperMass N η := by
  obtain ⟨N₀, hN₀, hupper⟩ := goldbachG11_rough_upper_buchstab η hη
  exact ⟨N₀, hN₀, fun N hN => sum_le_sum (hupper N hN)⟩

theorem goldbachG11BuchstabUpperMass_eventually_nonneg (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      0 ≤ goldbachG11BuchstabUpperMass N η := by
  obtain ⟨N₀, hN₀, hupper⟩ := goldbachG11FullRoughMass_le_buchstabUpper η hη
  exact ⟨N₀, hN₀, fun N hN => (goldbachG11FullRoughMass_nonneg N).trans (hupper N hN)⟩

/-- A single threshold precedes every actual window parameter; no factor `1 - epsilon`
survives the passage to the full rough mother. -/
theorem goldbachG11PrimeWindowMainMass_le_buchstabUpper (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ,
      400 * goldbachG11PrimeWindowMainMass N ε ≤
        goldbachG11BuchstabUpperMass N η + 8400 * N / (N : ℝ) ^ (4 / 53 : ℝ) := by
  obtain ⟨N₀, hN₀, hupper⟩ := goldbachG11FullRoughMass_le_buchstabUpper η hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN ε
  exact (goldbachG11PrimeWindowMainMass_le_fullRough (hN₀.trans hN) ε).trans
    (add_le_add (hupper N hN) le_rfl)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig