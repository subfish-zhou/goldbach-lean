import MathlibNt.Wu2008DoubleSieve.SingleUpperHCoarseLimit

namespace Wu2008DoubleSieve.SingleUpperHCoarseChoice
open Finset Set Real Filter MeasureTheory
open SingleUpperHSource SingleUpperHIntegral SingleUpperHPrimeQuadrature SingleUpperHCoarseLimit
open scoped Classical Topology

/-- Choose the coarse mesh before every arithmetic threshold. -/
theorem exists_small_mesh {δ h : ℝ} (hh : 0 < h) :
    ∃ n : ℕ, coarseMesh δ n < h := by
  let W : ℝ := ((1/2-δ)/2)-truncatedSixthLowerAlpha/2
  obtain ⟨n,hn⟩ := exists_nat_gt (W/h)
  refine ⟨n,?_⟩
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr
  have he := (div_lt_iff₀ hh).mp hn
  change W < h*((n : ℝ)+1)
  nlinarith only [he,hh]

/-- A genuine coarse prime upper bound with all mesh and source slack selected
before N. The prime sum still needs the separate fine-packing comparison. -/
theorem coarse_prime_upper {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ n : ℕ, ∃ η : ℝ, 0 < η ∧
      coarseMesh δ n ≤ truncatedSixthLowerAlpha/2 ∧
      coarseMesh δ n ≤ truncatedSixthLowerAlpha-1/15 ∧
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
        coarsePrimeMass δ η n N ≤
          (∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), effectiveKernel δ t)+ε := by
  let M := effective δ (argument δ (truncatedSixthLowerAlpha/2))
  have hab : truncatedSixthLowerAlpha/2 ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hM : 0 ≤ M := effective_slab_nonneg hδ hδhi ⟨le_rfl,hab⟩
  let h := min (truncatedSixthLowerAlpha/2)
    (min (truncatedSixthLowerAlpha-1/15) (ε/(2400*(M+1))))
  have hh : 0 < h := by
    dsimp [h]
    apply lt_min (by norm_num [truncatedSixthLowerAlpha])
    apply lt_min (by norm_num [truncatedSixthLowerAlpha])
    exact div_pos hε (by positivity)
  obtain ⟨n,hn⟩ := exists_small_mesh (δ := δ) hh
  have hma : coarseMesh δ n ≤ truncatedSixthLowerAlpha/2 :=
    hn.le.trans (min_le_left _ _)
  have hrest : coarseMesh δ n ≤ min (truncatedSixthLowerAlpha-1/15) (ε/(2400*(M+1))) :=
    hn.le.trans (min_le_right _ _)
  have hmb := hrest.trans (min_le_left _ _)
  have hme := hrest.trans (min_le_right _ _)
  let η := ε/800
  have hη : 0 < η := by dsimp [η]; positivity
  have hbudget : 600*coarseMesh δ n*M + 200*η ≤ ε/2 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2400*(M+1))).mp hme
    have hp := mesh_pos hδhi n
    dsimp [η]
    nlinarith only [h,hp]
  let C : ℕ → ℝ := fun i => effective δ (argument δ (coarseNode δ n (i-1)))+η
  obtain ⟨T,hT,hQ⟩ := finite_coarse_prime_quadrature (range (n+1)) C (half_pos hε)
  refine ⟨n,η,hη,hma,hmb,T,hT,?_⟩
  intro N hN
  have hquad := hQ N hN δ hδhi (clippedNode δ n) (fun i => clippedNode δ n (i+1)) (by
    intro i hi
    have hin := mem_range.mp hi
    refine ⟨?_,?_,?_⟩
    · exact (show (1/15 : ℝ) ≤ truncatedSixthLowerAlpha-coarseMesh δ n by linarith).trans
        (le_max_left _ _)
    · exact max_le_max le_rfl ((node_mono hδhi n) (by omega))
    · have hb : (1/2-δ)/2 ≤ (1/3 : ℝ) := by linarith
      apply le_trans _ hb
      apply max_le
      · have hp := mesh_pos hδhi n
        norm_num [truncatedSixthLowerAlpha] at *
        linarith
      · exact (node_mem hδhi (by omega)).2)
  have hi := coarse_integral_upper hδ hδhi hη.le hma
  change |coarsePrimeMass δ η n N-coarseIntegral δ η n| < ε/2 at hquad
  have hq := (abs_lt.mp hquad).2
  change coarseIntegral δ η n ≤ _+600*coarseMesh δ n*M+200*η at hi
  linarith only [hq,hi,hbudget]

end Wu2008DoubleSieve.SingleUpperHCoarseChoice
