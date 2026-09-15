import MathlibNt.SieveTheory.LiLiuFouvryG9AnalyticDensity

noncomputable section
open Finset Filter
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual weighted Euler mass, retaining all product-dependent exclusions. -/
def fouvryG9RectangleEulerMass (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (P : Finset ℕ) : ℝ :=
  ∑ m ∈ fouvryG9LongProducts N ρ k, ∑ n ∈ fouvryG9RectanglePrimeSupport N ρ k,
    fouvryG9LongAlpha N ρ k m*fouvryG9RectangleBeta N n*
      (∏ p ∈ P, (1-progressionDensity (m*n) p))

/-- The genuine extended upper-sieve factor at the original level and sqrt(N). -/
def fouvryG9UpperFactor (N : ℕ) (Q C K η : ℝ) : ℝ :=
  jr1965F (Real.log Q/Real.log (Real.sqrt N))+
    C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))

/-- Uniform analytic evaluation of every actual rectangle density. The fixed
constants and common threshold precede all cells, products and grids. The
positive Euler correction and the prime-box mass have not been suppressed. -/
theorem fouvryG9RectangleMain_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧
      ∀ δ η : ℝ, 0 ≤ δ → δ < 1/4 → 0 < η → η < 1/8 →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      ∀ e ρ : ℝ, 0 < e → 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      (fouvryG9GridCell N e ρ k).Nonempty →
      let Q := (N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))
      let P := fouvryG9SievePrimes N (Real.sqrt N)
      0 ≤ fouvryG9UpperFactor N Q C K η ∧
      fouvryG9RectangleMain N ρ δ η k P (Real.sqrt N) ≤
        fouvryG9UpperFactor N Q C K η*fouvryG9RectangleEulerMass N ρ k P := by
  obtain ⟨C,hC,K,hK,hden⟩ := g9ProgressionDensity_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro δ η hδ hδu hη hηu
  obtain ⟨Q₀,hQ₀,hupper⟩ := hden η hη hηu
  obtain ⟨Nw,hw⟩ := g9WF_exists_internal_level_gate hδ (by linarith) hη Q₀
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (4/53) (by norm_num))
  refine ⟨max Nw (max Ng 4),?_⟩
  intro N hN hEven e ρ he hρ hρu k hne
  have hNw := (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNg := (le_max_left _ _).trans hrest
  have hN4 : (4 : ℝ) ≤ N := (le_max_right _ _).trans hrest
  have hN0 : (0 : ℝ) < N := by linarith
  have hsix : 6 ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using hg N hNg
  let T := (2/3 : ℝ)*ρ^k.1
  let Q := (N : ℝ)^(5/9-δ)/T^(5/9 : ℝ)
  let P := fouvryG9SievePrimes N (Real.sqrt N)
  obtain ⟨_,_,_,hlo,hhi⟩ := fouvryG9Grid_buffered_geometry he hρ hρu hne
  have hT : 1 ≤ T := by dsimp [T]; linarith
  obtain ⟨_,_,hQq,_,hQN⟩ := hw N T hNw hT hhi
  have hQ4 : 4 ≤ Q := hQ₀.trans hQq
  obtain ⟨hz,hzQ⟩ := g9WF_sqrt_cutoff hN4 hT hhi hδ hδu
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log (Real.sqrt N) := Real.log_pos (by linarith)
  have hcoord : Real.log Q/Real.log (Real.sqrt N) ≤ 2 := by
    apply (div_le_iff₀ hlogz).2
    rw [Real.log_sqrt hN0.le]
    have hlog := Real.log_le_log (by linarith : 0 < Q) hQN
    linarith
  have hfactor : 0 ≤ fouvryG9UpperFactor N Q C K η := by
    unfold fouvryG9UpperFactor
    rw [jr1965F_eq_of_le_three (by linarith)]
    positivity
  refine ⟨hfactor,?_⟩
  have hp : ∀ v : ℕ,
      externalDensity true P (externalInternalLevel Q η) η (Real.sqrt N) (progressionDensity v) ≤
        (∏ p ∈ P, (1-progressionDensity v p))*fouvryG9UpperFactor N Q C K η := by
    intro v
    exact hupper Q hQq v P (fouvryG9SievePrimes_odd hEven _) (Real.sqrt N) hz hzQ
      (fun p hp => (fouvryG9SievePrimes_mem N p _ |>.mp hp).2.2)
  unfold fouvryG9RectangleMain fouvryG9RectangleEulerMass
  simp only [mul_sum]
  apply sum_le_sum
  intro m hm
  apply sum_le_sum
  intro n hn
  have hw : 0 ≤ fouvryG9LongAlpha N ρ k m*fouvryG9RectangleBeta N n :=
    mul_nonneg (fouvryG9LongAlpha_nonneg N ρ k m) (fouvryG9_prime_copN_beta_bounds N n).1
  calc
    _ ≤ (fouvryG9LongAlpha N ρ k m*fouvryG9RectangleBeta N n)*
        ((∏ p ∈ P, (1-progressionDensity (m*n) p))*fouvryG9UpperFactor N Q C K η) :=
      mul_le_mul_of_nonneg_left (hp (m*n)) hw
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
