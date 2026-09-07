import MathlibNt.SieveTheory.LiLiuGoldbachB10ProductCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Fixed-scale floor transport with a strict exponent gap. Parameters precede the threshold. -/
theorem eventually_rpow_le_scaled_floor_rpow
    (ε t u : ℝ) (hε : 0 < ε) (hu : 0 < u) (htu : t < u) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) ^ t ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ u := by
  have hlim := (tendsto_rpow_neg_atTop (show 0 < u - t by linarith)).comp
    tendsto_natCast_atTop_atTop
  have hexp : -(u - t) = t - u := by ring
  simp only [hexp] at hlim
  have hK : 0 < (ε / 2) ^ u := Real.rpow_pos_of_pos (by positivity) _
  have he := hlim.eventually (gt_mem_nhds hK)
  have hev : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ t ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ u := by
    filter_upwards [he, eventually_ge_atTop (max 2 ⌈2 / ε⌉₊)] with N hp hN
    have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hc : 2 / ε ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2 ⌈2 / ε⌉₊).trans hN)
    have hprod : 2 ≤ ε * (N : ℝ) := by
      have := (div_le_iff₀ hε).mp hc
      nlinarith
    have hfloor : ε / 2 * (N : ℝ) ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) := by
      have hf := Nat.lt_floor_add_one (ε * (N : ℝ))
      nlinarith
    change (N : ℝ) ^ (t - u) < (ε / 2) ^ u at hp
    have hmul := mul_le_mul_of_nonneg_right hp.le (Real.rpow_nonneg hNpos.le u)
    rw [← Real.rpow_add hNpos, sub_add_cancel] at hmul
    calc
      (N : ℝ) ^ t ≤ (ε / 2) ^ u * (N : ℝ) ^ u := hmul
      _ = (ε / 2 * (N : ℝ)) ^ u := (Real.mul_rpow (by positivity) hNpos.le).symm
      _ ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ u := Real.rpow_le_rpow (by positivity) hfloor hu.le
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  exact ⟨max 2 K, le_max_left _ _, fun N hN => hK N ((le_max_right _ _).trans hN)⟩

/-- The actual B10 support fits the smaller Pan endpoint for fixed epsilon and gamma. -/
theorem goldbachC10ProductSupport_scaled_floor_eventually
    (ε γ : ℝ) (hε : 0 < ε) (hγ : γ < (1 : ℝ) / 3) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ b : ℝ, ∀ m : ℕ,
      m ∈ goldbachC10ProductSupport N b ((N : ℝ) ^ γ) →
      (m : ℝ) ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨N₀, hN₀, hscale⟩ := eventually_rpow_le_scaled_floor_rpow ε ((1 + γ) / 2)
    ((2 : ℝ) / 3) hε (by norm_num) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN b m hm
  exact (goldbachC10ProductSupport_le_rpow_half_and_lt_two_thirds
    (hN₀.trans hN) hγ hm).1.trans (hscale N hN)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig