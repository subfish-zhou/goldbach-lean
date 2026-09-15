import MathlibNt.Wu2008DoubleSieve.FourRoughGeometry

/-! The actual uniform rough theorem is consumed before all prime labels.
The full reciprocal label mass is retained in the additive tolerance budget. -/
namespace Wu2008DoubleSieve.FourRoughClosedMass
open Finset Set Real LiLiuPrereqBuchstab TruncatedFourPhysical
open scoped Classical
noncomputable section

def mainTerm (N : ℕ) (q : Quad) : ℝ :=
  density (coord N q.1) (coord N q.2.1) (coord N q.2.2.1) (coord N q.2.2.2) /
    fourModulusProduct q
def mainMass (N : ℕ) (S : Finset Quad) : ℝ := ∑ q ∈ S, mainTerm N q
def reciprocalMass (S : Finset Quad) : ℝ := ∑ q ∈ S, 1 / (fourModulusProduct q : ℝ)

theorem actual_primes_lower {N a b c d : ℕ}
    (hq : (a,b,c,d) ∈ labels10 N ∪ labels11 N) :
    a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧ (N : ℝ)^alpha ≤ b := by
  have hw : 0 ≤ (N : ℝ)^beta := rpow_nonneg (Nat.cast_nonneg N) _
  have hv : 0 ≤ (N : ℝ)^lam / c := div_nonneg (rpow_nonneg (Nat.cast_nonneg N) _) (Nat.cast_nonneg c)
  rcases mem_union.mp hq with ht | ht
  · obtain ⟨ha,hb,hc,hd⟩ := mem_labels.mp ht
    obtain ⟨hpa,hla,_⟩ := (mem_primesIcc hw).mp ha
    obtain ⟨hpb,hlab,_⟩ := (mem_primesIcc hw).mp hb
    exact ⟨hpa,hpb,((mem_primesIcc hw).mp hc).1,((mem_primesIcc hw).mp hd).1,hla.trans hlab⟩
  · obtain ⟨ha,hb,hc,hd⟩ := mem_labels.mp ht
    obtain ⟨hpa,hla,_⟩ := (mem_primesIcc hw).mp ha
    obtain ⟨hpb,hlab,_⟩ := (mem_primesIcc hw).mp hb
    exact ⟨hpa,hpb,((mem_primesIcc hw).mp hc).1,((mem_primesIcc hv).mp hd).1,hla.trans hlab⟩

theorem log_ratio_identity {N a b c d : ℕ} (hN : 1 < N)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime) :
    log ((N : ℝ) / fourModulusProduct (a,b,c,d)) / log (b : ℝ) =
    parameter (coord N a) (coord N b) (coord N c) (coord N d) := by
  have hn : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hN)).ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne_zero
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne_zero
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne_zero
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne_zero
  simp only [fourModulusProduct, Nat.cast_mul]
  rw [log_div hN0 (by positivity), log_mul (by positivity : (a : ℝ)*b*c ≠ 0) hd0,
    log_mul (by positivity : (a : ℝ)*b ≠ 0) hc0, log_mul ha0 hb0]
  unfold parameter coord
  field_simp
  ring

theorem actual_size_range {N a b c d : ℕ} (hN : 1 < N)
    (hq : (a,b,c,d) ∈ labels10 N ∪ labels11 N) :
    (N : ℝ) / fourModulusProduct (a,b,c,d) ≤ N ∧
    (b : ℝ) ≤ (N : ℝ) / fourModulusProduct (a,b,c,d) := by
  obtain ⟨ha,hb,hc,hd,_⟩ := actual_primes_lower hq
  have hD : 0 < fourModulusProduct (a,b,c,d) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos) hd.pos
  have hD1 : (1 : ℝ) ≤ fourModulusProduct (a,b,c,d) := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < fourModulusProduct (a,b,c,d) := by exact_mod_cast hD
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.pos
  have hlb : 0 < log (b : ℝ) := log_pos (by exact_mod_cast hb.one_lt)
  refine ⟨(div_le_iff₀ hD0).mpr (by nlinarith), ?_⟩
  have hu := (actual_parameters hN hq).2
  rw [← log_ratio_identity hN ha hb hc hd] at hu
  have hlog := (le_div_iff₀ hlb).mp hu
  apply (log_le_log_iff hb0 (div_pos hN0 hD0)).mp
  linarith

theorem pointwise_normalization {N a b c d : ℕ} (hN : 1 < N)
    (hq : (a,b,c,d) ∈ labels10 N ∪ labels11 N) (tau : ℝ) :
    (buchstab (log ((N : ℝ) / fourModulusProduct (a,b,c,d)) / log (b : ℝ))+tau) *
      ((N : ℝ) / fourModulusProduct (a,b,c,d)) / log (b : ℝ) =
    ((N : ℝ)/log N) *
      (mainTerm N (a,b,c,d) + (tau / coord N b) / fourModulusProduct (a,b,c,d)) := by
  obtain ⟨ha,hb,hc,hd,_⟩ := actual_primes_lower hq
  rw [log_ratio_identity hN ha hb hc hd]
  have hn : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hN)).ne'
  have hlb : log (b : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hb.one_lt)).ne'
  unfold mainTerm density coord
  field_simp

/-- One threshold simultaneously controls both complete closed four-prime domains. -/
theorem actual_pointwise_upper {tau : ℝ} (htau : 0 < tau) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ q ∈ labels10 N ∪ labels11 N,
      ((cofactor N q).card : ℝ) ≤ ((N : ℝ)/log N) *
        (mainTerm N q + (tau/alpha) / fourModulusProduct q) := by
  obtain ⟨T,hT,hbound⟩ := NonunitRoughUniform.uniform_upper fixed_geometry.2.1 htau
  refine ⟨T,hT,?_⟩
  rintro N hNT ⟨a,b,c,d⟩ hq
  have hN : 1 < N := by omega
  obtain ⟨ha,hb,hc,hd,hlower⟩ := actual_primes_lower hq
  obtain ⟨hxN,hbx⟩ := actual_size_range hN hq
  have hs := (hbound N hNT _ _ hxN hlower).2 hbx
  change ((cofactor N (a,b,c,d)).card : ℝ) ≤ _ at hs
  rw [pointwise_normalization hN hq tau] at hs
  apply hs.trans
  have hy := (actual_parameters hN hq).1
  have he := div_le_div_of_nonneg_left htau.le fixed_geometry.2.1 hy
  have hD : (0 : ℝ) ≤ fourModulusProduct (a,b,c,d) := Nat.cast_nonneg _
  have hscale : 0 ≤ (N : ℝ)/log N := div_nonneg (Nat.cast_nonneg N)
    (log_pos (by exact_mod_cast hN)).le
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right (div_le_div_of_nonneg_right he hD) _) hscale

/-- No width-relative error: every closed atom is charged its full reciprocal weight. -/
theorem actual_main_upper {tau : ℝ} (htau : 0 < tau) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    rawMass10 N ≤ ((N : ℝ)/log N) *
      (mainMass N (labels10 N)+(tau/alpha)*reciprocalMass (labels10 N)) ∧
    rawMass11 N ≤ ((N : ℝ)/log N) *
      (mainMass N (labels11 N)+(tau/alpha)*reciprocalMass (labels11 N)) := by
  obtain ⟨T,hT,hbound⟩ := actual_pointwise_upper htau
  refine ⟨T,hT,?_⟩
  intro N hN
  have hs (S : Finset Quad) (hS : S ⊆ labels10 N ∪ labels11 N) :
      mass N S ≤ ((N : ℝ)/log N) * (mainMass N S+(tau/alpha)*reciprocalMass S) := by
    calc
      mass N S ≤ ∑ q ∈ S, ((N : ℝ)/log N) *
          (mainTerm N q + (tau/alpha)/fourModulusProduct q) :=
        sum_le_sum fun q hq => hbound N hN q (hS hq)
      _ = _ := by
        rw [← mul_sum]
        congr 1
        simp only [mainMass, reciprocalMass, sum_add_distrib, mul_sum, mul_one_div]
  exact ⟨hs _ subset_union_left, hs _ subset_union_right⟩

end
end Wu2008DoubleSieve.FourRoughClosedMass
