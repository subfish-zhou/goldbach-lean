import Wu18938Campaign.M1.Confirmed.LabelledDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledSquareCofactor

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real Filter
open scoped Classical Topology

theorem roughBox_labelled_exceptions (m : ℕ) {η δ κ F G ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hκ : 0 < κ)
    (hF : 0 < F) (hG : 0 < G) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ (α : Type) (L : LabelledPhysical.Family α N),
      (∀ e, (∑ x ∈ L.layerFibre e, L.weight x) ≤ F) →
      (∀ ell : ℕ, ell.Prime → L.weightAt ell ≤ G) →
      L.squareRawMass ((N : ℝ) ^ κ) + L.noncoprimePart.primeMass ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,hpay⟩ := roughBox_absolute_power_relative m 1 hη hδ (half_pos he)
    (show 0 < 4 * F by positivity) hκ
  obtain ⟨T1,_,hbad⟩ := roughBox_absolute_power_relative m 1 hη hδ (half_pos he)
    (show 0 < G / log 2 by positivity) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨T2,hpow⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 0 (by norm_num : (0 : ℝ) < 2) hκ)
  obtain ⟨T3,hlog⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 (max T1 (max T2 T3)), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb α L hfibre hout
  let Y := (N : ℝ) ^ κ
  have hY : 2 ≤ Y := by simpa only [pow_zero,mul_one] using hpow N (by omega)
  have hY0 : 0 < Y := by linarith
  have hY1 : 0 < Y - 1 := by linarith
  have hl := hlog N (by omega)
  dsimp only [Function.comp_apply] at hl
  have hs := L.squareRawMass_le hY hF.le hfibre
  have hd : 1 / (Y - 1) ≤ 2 / Y := by
    apply (div_le_div_iff₀ hY1 hY0).mpr
    linarith
  have hs' : L.squareRawMass Y ≤ (ε / 2) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ F * N * (1 + log N) / (Y - 1) := hs
      _ = (F * N * (1 + log N)) * (1 / (Y - 1)) := by ring
      _ ≤ (F * N * (1 + log N)) * (2 / Y) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ (F * N * (2 * log N)) * (2 / Y) := by gcongr; linarith
      _ = (4 * F) * N * log N ^ 1 / (N : ℝ) ^ κ := by dsimp only [Y]; ring
      _ ≤ _ := hpay N (by omega) i Δ V hb
  have hb' := L.noncoprimePart_primeMass_le_log (by omega) hG.le
    (fun ell hell => hout ell (Nat.prime_of_mem_primeFactors hell))
  have hbudget := hbad N (by omega) i Δ V hb
  have heq : (G / log 2) * N * log N ^ 1 / (N : ℝ) ^ (1 : ℝ) = G * log N / log 2 := by
    rw [rpow_one,pow_one]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  rw [heq] at hbudget
  linarith only [hs', hb', hbudget]

end Wu18938Campaign.M1.Confirmed
