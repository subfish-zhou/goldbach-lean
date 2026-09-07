import MathlibNt.SieveTheory.LiLiuGoldbachG12BandMass

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12ClippedWindow G12FineGrid G12RoughBoundary
namespace G12BandOutput

def clipOutput (N : ℕ) (ε : ℝ) (T V : ℕ → ℝ) : ℝ :=
  primeOutput N (goldbachG12NormalizedCoefficient N) (clampLower N ε T V) (clampUpper N ε V)

def sourceOutput (N : ℕ) (ε a : ℝ) : ℝ :=
  clipOutput N ε (productLo N (ε/a)) (productLo N (a*ε)) +
    clipOutput N ε (productLo N (1/a)) (productLo N 1) +
      clipOutput N ε (roughLo a) (top N)

/-- Literal entire grid boundary, with the prime-output indicator. -/
def boundaryOutput (ρ : ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  400*∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε), atom N p

def HN (N : ℕ) : ℝ := SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2

theorem HN_nonneg (N : ℕ) : 0 ≤ HN N :=
  div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _))
    (sq_nonneg _)

private theorem union_sum_le (N : ℕ) (A B : Finset (ℕ × ℕ)) :
    (∑ p ∈ A ∪ B, atom N p) ≤ (∑ p ∈ A, atom N p) + ∑ p ∈ B, atom N p := by
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := atom N)
  have hn : 0 ≤ ∑ p ∈ A ∩ B, atom N p := sum_nonneg (fun p _ => atom_nonneg N p)
  linarith

/-- The sieve is invoked on three global windows, never once for every cell. -/
theorem boundaryOutput_le_source {ρ a ε : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (ha : 1 < a) (he : 0 < ε)
    (hmesh : ∀ k ∈ indices ρ N,
      (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ)) :
    boundaryOutput ρ N ε ≤ sourceOutput N ε a := by
  have hsub : (∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε), atom N p) ≤
      ∑ p ∈ cover N ε a, atom N p :=
    sum_le_sum_of_subset_of_nonneg (boundary_subset_cover hN ha he hmesh)
      (fun p _ _ => atom_nonneg N p)
  have h₁ := union_sum_le N
    (pairs N ε (productLo N (ε/a)) (productLo N (a*ε)) ∪
      pairs N ε (productLo N (1/a)) (productLo N 1))
    (pairs N ε (roughLo a) (top N))
  have h₂ := union_sum_le N (pairs N ε (productLo N (ε/a)) (productLo N (a*ε)))
    (pairs N ε (productLo N (1/a)) (productLo N 1))
  have hsum := mul_le_mul_of_nonneg_left
    (hsub.trans (h₁.trans (add_le_add h₂ (le_refl _)))) (by norm_num : (0 : ℝ) ≤ 400)
  simpa only [mul_add,pairs_output_eq,sourceOutput,clipOutput,boundaryOutput,cover] using hsum

/-- There are exactly three additive sieve errors, regardless of the grid size. -/
theorem sourceOutput_uniformEight (t : ℝ) (ht : 0 < t) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∀ ε a : ℝ,
      sourceOutput N ε a ≤
        (8+t)*400*sourceMass N ε a*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
          3*t*HN N := by
  obtain ⟨K,hK,h⟩ := primeOutput_uniformEight t ht
  refine ⟨K,hK,?_⟩
  intro N hN hEven ε a
  have hN2 : 2 ≤ N := by omega
  have h₁ := h N hN hEven _ _ _ ε
    (G12BandOutput.clamp_admissible hN2 ε (productLo N (ε/a)) (productLo N (a*ε)))
  have h₂ := h N hN hEven _ _ _ ε
    (G12BandOutput.clamp_admissible hN2 ε (productLo N (1/a)) (productLo N 1))
  have h₃ := h N hN hEven _ _ _ ε
    (G12BandOutput.clamp_admissible hN2 ε (roughLo a) (top N))
  unfold sourceOutput clipOutput sourceMass clipMass HN
  calc
    _ ≤ _ := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

/-- Universal constant, chosen before all mesh and truncation parameters. -/
def outputConstant : ℝ := 9*fullConstant

theorem outputConstant_pos : 0 < outputConstant := mul_pos (by norm_num) fullConstant_pos

/-- The global source has the actual prime-output scale, not raw mother scale. -/
theorem sourceOutput_budget {a ε : ℝ} (ha : 1 < a) (ha2 : a ≤ 2)
    (he : 0 < ε) (he2 : ε ≤ 2/15) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      sourceOutput N ε a ≤ outputConstant*(a-1)*HN N + δ*HN N := by
  let t : ℝ := min 1 (δ/6)
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htd : t ≤ δ/6 := min_le_right _ _
  obtain ⟨K₁,hK₁,hs⟩ := sourceOutput_uniformEight t ht
  obtain ⟨K₂,_,hm⟩ := sourceMass_budget ha ha2 he he2 (δ/18) (by positivity)
  refine ⟨max K₁ K₂,by omega,?_⟩
  intro N hN hEven
  have hN4 : 4 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmass := hm N (by omega)
  have hout := hs N (by omega) hEven ε a
  have hnorm : 0 ≤ Real.log (N : ℝ)/(N : ℝ)*(400*sourceMass N ε a) :=
    mul_nonneg (div_nonneg hl.le hn.le)
      (mul_nonneg (by norm_num) (sourceMass_nonneg (by omega) ε a))
  have hscale : (8+t)*400*sourceMass N ε a*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) =
      (8+t)*(Real.log (N : ℝ)/(N : ℝ)*(400*sourceMass N ε a))*HN N := by
    unfold HN
    field_simp
  rw [hscale] at hout
  have hm9 : (8+t)*(Real.log (N : ℝ)/(N : ℝ)*(400*sourceMass N ε a)) ≤
      9*(fullConstant*(a-1)+δ/18) :=
    (mul_le_mul_of_nonneg_right (by linarith : 8+t ≤ 9) hnorm).trans
      (mul_le_mul_of_nonneg_left hmass (by norm_num))
  have hb := mul_le_mul_of_nonneg_right hm9 (HN_nonneg N)
  have herr := mul_le_mul_of_nonneg_right (by linarith : 3*t ≤ δ/2) (HN_nonneg N)
  unfold outputConstant
  nlinarith only [hout,hb,herr]

/-- A uniform geometric condition suffices; no analytic bound is assumed on the target. -/
theorem boundaryOutput_budget {a ε : ℝ} (ha : 1 < a) (ha2 : a ≤ 2)
    (he : 0 < ε) (he2 : ε ≤ 2/15) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∀ ρ : ℝ,
      (∀ k ∈ indices ρ N, (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ)) →
      boundaryOutput ρ N ε ≤ outputConstant*(a-1)*HN N + δ*HN N := by
  obtain ⟨K,hK,h⟩ := sourceOutput_budget ha ha2 he he2 δ hδ
  refine ⟨K,hK,?_⟩
  intro N hN hEven ρ hmesh
  exact (boundaryOutput_le_source (by omega) ha he hmesh).trans (h N hN hEven)

/-- Actual rounded fine grid. The cutoff precedes N and its parity proof. -/
theorem fixed_grid_boundaryOutput_budget {ρ a ε : ℝ}
    (hρ : 1 < ρ) (hρa : ρ < a) (ha2 : a ≤ 2) (he : 0 < ε) (he2 : ε ≤ 2/15)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      boundaryOutput ρ N ε ≤ outputConstant*(a-1)*HN N + δ*HN N := by
  obtain ⟨K₁,hK₁,h⟩ := boundaryOutput_budget (hρ.trans hρa) ha2 he he2 δ hδ
  have hg := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (ρ/(a-ρ)))
  obtain ⟨K₂,hK₂⟩ := eventually_atTop.mp hg
  refine ⟨max K₁ K₂,by omega,?_⟩
  intro N hN hEven
  apply h N (by omega) hEven ρ
  intro k _
  apply short_ratio_of_rounding hρ hρa.le
  have hh : ρ/(a-ρ) ≤ (lowCut N : ℝ) :=
    (hK₂ N (by omega)).trans (Nat.le_ceil _)
  have hh' := (div_le_iff₀ (sub_pos.mpr hρa)).mp hh
  simpa only [mul_comm] using hh'

theorem exists_fixed_boundaryOutput_constant : ∃ C > 0, ∀ ρ a ε : ℝ,
    1 < ρ → ρ < a → a ≤ 2 → 0 < ε → ε ≤ 2/15 → ∀ δ : ℝ, 0 < δ →
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      boundaryOutput ρ N ε ≤ C*(a-1)*HN N + δ*HN N := by
  exact ⟨outputConstant,outputConstant_pos,fun _ _ _ hρ hρa ha2 he he2 δ hδ =>
    fixed_grid_boundaryOutput_budget hρ hρa ha2 he he2 δ hδ⟩

/-- Mesh is selected before N: arbitrarily small actual entire-boundary output. -/
theorem exists_small_mesh (τ : ℝ) (hτ : 0 < τ) :
    ∃ ρ a : ℝ, 1 < ρ ∧ ρ < a ∧ a ≤ 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 2/15 →
      ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → boundaryOutput ρ N ε ≤ τ*HN N := by
  let d : ℝ := min (1/2) (τ/(2*outputConstant))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hτ (by positivity [outputConstant_pos]))
  have hd1 : d ≤ 1/2 := min_le_left _ _
  have hdτ : outputConstant*d ≤ τ/2 := by
    have h := (le_div_iff₀ (by positivity [outputConstant_pos] : 0 < 2*outputConstant)).mp
      (show d ≤ τ/(2*outputConstant) from min_le_right _ _)
    linarith
  refine ⟨1+d/2,1+d,by linarith,by linarith,by linarith,?_⟩
  intro ε he he2
  obtain ⟨K,hK,h⟩ := fixed_grid_boundaryOutput_budget
    (by linarith : 1 < 1+d/2) (by linarith : 1+d/2 < 1+d)
    (by linarith : 1+d ≤ 2) he he2 (τ/2) (by positivity)
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have hout := h N hN hEven
  have hpay := mul_le_mul_of_nonneg_right hdτ (HN_nonneg N)
  nlinarith only [hout,hpay]

/-- Expanded actual-output headline: every physical atom and both logarithms are visible. -/
theorem actual_boundary_output_constant : ∃ C > 0, ∀ ρ a ε : ℝ,
    1 < ρ → ρ < a → a ≤ 2 → 0 < ε → ε ≤ 2/15 → ∀ δ : ℝ, 0 < δ →
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      (400*∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε),
        goldbachG12NormalizedCoefficient N p.1 *
          (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) ≤
        C*(a-1)*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) +
          δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  simpa only [boundaryOutput,atom,HN] using exists_fixed_boundaryOutput_constant

end G12BandOutput
