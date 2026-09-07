import MathlibNt.SieveTheory.LiLiuGoldbachG12BandWindows
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12ClippedWindow G12FineGrid G12RoughBoundary
namespace G12BandOutput

def clipMass (N : ℕ) (ε : ℝ) (T V : ℕ → ℝ) : ℝ :=
  mass N (goldbachG12NormalizedCoefficient N) (clampLower N ε T V) (clampUpper N ε V)

def sourceMass (N : ℕ) (ε a : ℝ) : ℝ :=
  clipMass N ε (productLo N (ε/a)) (productLo N (a*ε)) +
    clipMass N ε (productLo N (1/a)) (productLo N 1) +
      clipMass N ε (roughLo a) (top N)

theorem sourceMass_nonneg {N : ℕ} (hN : 2 ≤ N) (ε a : ℝ) : 0 ≤ sourceMass N ε a := by
  unfold sourceMass clipMass
  exact add_nonneg (add_nonneg (mass_nonneg (G12BandOutput.clamp_admissible hN ε _ _))
    (mass_nonneg (G12BandOutput.clamp_admissible hN ε _ _)))
    (mass_nonneg (G12BandOutput.clamp_admissible hN ε _ _))

theorem product_clip_mass_le {N : ℕ} (hN : 4 ≤ N) (ε l u : ℝ) :
    clipMass N ε (productLo N l) (productLo N u) ≤
      bandMass N ε l u + 21*N/(N : ℝ)^(4/53 : ℝ) := by
  rw [clipMass,mass_split]
  exact add_le_add (product_clip_good_le N ε l u)
    (badMass_le hN (G12BandOutput.clamp_admissible (by omega) ε _ _))

theorem rough_clip_mass_le {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) {a : ℝ} (ha : 0 < a) :
    clipMass N ε (roughLo a) (top N) ≤ nearWindowMass N ε a + 21*N/(N : ℝ)^(4/53 : ℝ) := by
  rw [clipMass,mass_split]
  exact add_le_add (rough_clip_good_le N ε ha)
    (badMass_le hN (G12BandOutput.clamp_admissible (by omega) ε _ _))

/-- Three bad-prime transports are paid once, independently of the grid cardinality. -/
theorem sourceMass_le {N : ℕ} (hN : 4 ≤ N) {ε a : ℝ} (ha : 1 < a) (he : 0 < ε) :
    400*sourceMass N ε a ≤
      goldbachG12ThinSum N (fun _ => ε/a) (fun _ => a*ε) +
        goldbachG12ThinSum N (fun _ => 1/a) (fun _ => 1) + nearMass N a +
          25200*N/(N : ℝ)^(4/53 : ℝ) := by
  have hlo : ε/a ≤ a*ε := (div_le_self he.le ha.le).trans
    (le_mul_of_one_le_left he.le ha.le)
  have hhi : 1/a ≤ (1 : ℝ) := (div_le_iff₀ (by linarith : 0 < a)).mpr (by linarith)
  have h₁ := product_clip_mass_le hN ε (ε/a) (a*ε)
  have h₂ := product_clip_mass_le hN ε (1/a) 1
  have h₃ := rough_clip_mass_le hN ε (by linarith : 0 < a)
  have h₄ := bandMass_le_thinSum (N := N) ε _ _ hlo
  have h₅ := bandMass_le_thinSum (N := N) ε _ _ hhi
  have h₆ := nearWindowMass_le_nearMass (N := N) ε a
  unfold sourceMass
  simp only [div_eq_mul_inv] at h₁ h₂ h₃ h₄ h₅ ⊢
  nlinarith only [h₁,h₂,h₃,h₄,h₅,h₆]

theorem bad_transport_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ N ≥ K,
      25200*Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ) ≤ δ := by
  have ht₀ := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).tendsto_div_nhds_zero
  have ht : Tendsto (fun N : ℕ => 25200*(Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero,Function.comp_apply] using
      (ht₀.comp tendsto_natCast_atTop_atTop).const_mul 25200
  have he := ht.eventually (gt_mem_nhds hδ)
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  refine ⟨K,fun N hN => ?_⟩
  have hh := (hK N hN).le
  simpa only [Function.comp_apply,mul_zero,mul_div_assoc] using hh

/-- The complete three-window source mass, including the ungated transport. -/
theorem sourceMass_budget {a ε : ℝ} (ha : 1 < a) (ha2 : a ≤ 2)
    (he : 0 < ε) (he2 : ε ≤ 2/15) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K,
      Real.log (N : ℝ)/(N : ℝ)*(400*sourceMass N ε a) ≤ fullConstant*(a-1)+δ := by
  obtain ⟨K₁,hK₁,hp⟩ := product_bands_integral_budget ha ha2 he he2 (δ/3) (by positivity)
  obtain ⟨K₂,_,hr⟩ := nearMass_budget (δ/3) (by positivity)
  obtain ⟨K₃,hb⟩ := bad_transport_eventually (δ/3) (by positivity)
  refine ⟨max K₁ (max K₂ K₃),by omega,?_⟩
  intro N hN
  have hN4 : 4 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) hn.le
  have hs := mul_le_mul_of_nonneg_left (sourceMass_le hN4 ha he) hl
  have hp' := hp N (by omega)
  have hr' := hr N (by omega) a ha.le
  have hb' := hb N (by omega)
  have heq : Real.log (N : ℝ)/(N : ℝ)*(25200*N/(N : ℝ)^(4/53 : ℝ)) =
      25200*Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ) := by field_simp
  have hc := mul_le_mul_of_nonneg_right
    (le_abs_self ((564383/1000000 : ℝ)*3*goldbachG12PrimeIntegral (fun _ => 1)))
    (sub_nonneg.mpr ha.le)
  unfold fullConstant
  rw [mul_add,mul_add,heq] at hs
  nlinarith only [hs,hp',hr',hb',hc]

end G12BandOutput
