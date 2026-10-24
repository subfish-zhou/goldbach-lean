import WR2GammaHighLowerTripleSource

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve WuSource.SrcSingle LowerTripleGrouped HighBoxRecovery Real Finset
open scoped Classical

theorem window_lower {N d q : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hm : d ∈ boxConvolutionSupport (windows j N))
    (hq : q ∈ primeWindow N (wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
      (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s)) :
    q.Prime ∧ (N : ℝ)^highEta ≤ q := by
  have hp := mem_primeWindow.mp hq
  have hm' := hm
  rw [support_eq] at hm'
  have hg := prime_geometry j hN hd hh hm'
  have hpar := row_analytic j
  have hs : 0 < (Wu04RemainingCore.row j).S := by linarith [hpar.three_le_S]
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have he : highEta ≤ 10*highEta*(1/(Wu04RemainingCore.row j).S) := by
    have ht : 1 ≤ 10/(Wu04RemainingCore.row j).S := (le_div_iff₀ hs).mpr (by linarith [hpar.S_le_five])
    have := mul_le_mul_of_nonneg_left ht (by norm_num [highEta] : 0 ≤ highEta)
    calc
      highEta = highEta*1 := by ring
      _ ≤ highEta*(10/(Wu04RemainingCore.row j).S) := this
      _ = 10*highEta*(1/(Wu04RemainingCore.row j).S) := by ring
  refine ⟨hp.1, ?_⟩
  calc
    (N : ℝ)^highEta ≤ (N : ℝ)^(10*highEta*(1/(Wu04RemainingCore.row j).S)) :=
      rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) he
    _ = ((N : ℝ)^(10*highEta))^(1/(Wu04RemainingCore.row j).S) := rpow_mul hn _ _
    _ ≤ wuLocalCutoff N δ d (Wu04RemainingCore.row j).S :=
      rpow_le_rpow (by positivity) hg.2.2.2.2.2.2.1 (by positivity)
    _ ≤ q := hp.2.2.1

/-- Every physical label has a positive cofactor with a uniform power gap. -/
theorem source_geometry {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) {x : Label}
    (hx : x ∈ (sourceFamily j N δ k).labels) :
    PhysicalGeometry N highEta (sourceFamily j N δ k) x := by
  obtain ⟨hm,_,hq,_⟩ := (mem_labels x).mp hx
  have hlarge := window_lower j hN hd hh hm hq
  have hg := (sourceFamily j N δ k).geometry x hx
  have hpos : 0 < cofactor x := hg.1
  have hqu : (x.2.2.1 : ℝ) ≤ (sourceFamily j N δ k).upper x :=
    (le_max_left _ _).trans hg.2.2.1
  have hcap : cofactor x*x.2.2.1 ≤ N := by
    exact_mod_cast (mul_le_mul_of_nonneg_left hqu (Nat.cast_nonneg (cofactor x))).trans hg.2.2.2
  have hle : cofactor x ≤ N := (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N : ℝ)^highEta ≤ cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (cofactor_divisors x).2.2)
  exact ⟨hpos,hle,hpow,omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1,hlarge.2.trans (le_max_left _ _),hg.2.2.1,hg.2.2.2⟩

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.source_geometry
