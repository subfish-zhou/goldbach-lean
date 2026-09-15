import Wu08RecoveryStrips

noncomputable section
open Finset Real Set LiLiuPrereqBuchstab
open scoped Classical
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.SmallBoundaryRecovery
open FourRoughClosedMass SmallGrid SmallBoundary

def smallClosed (N : ℕ) (e : Bool) : Finset SmallGrid.Quad :=
  (labelSet N e).filter fun q => (q.1 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ)

theorem smallClosed_nonneg {N : ℕ} (hN : 1 < N) {e : Bool} {q : SmallGrid.Quad}
    (hq : q ∈ smallClosed N e) : 0 ≤ unshiftedTerm N q := by
  have hlabel := (mem_filter.mp hq).1
  have hf := F_actual hN e hlabel
  have hcap : 0 < cap (coord N q.2.1) := fixed_geometry.2.1.trans_le (cap_mem _).1
  have hF : 0 ≤ F (coord N q.1) (coord N q.2.1) (coord N q.2.2.1) (coord N q.2.2.2) := by
    unfold F clippedDensity
    exact div_nonneg (buchstab_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _))) hcap.le
  unfold unshiftedTerm
  rw [← hf]
  exact div_nonneg (mul_nonneg (atomWeight_nonneg _ _) hF) (Nat.cast_nonneg _)

theorem interior_mem {N : ℕ} {e : Bool} {ρ : ℝ} (hN : (4 : ℝ) ≤ N)
    (hρ : 1 < ρ) {q : SmallGrid.Quad} (hq : q ∈ effectiveQuads N e ρ)
    (ha : FourRoughClosedMass.alpha ≤ coord N q.1)
    (hu : coord N q.1 ≤ 1/10) (hab : coord N q.1 ≤ coord N q.2.1) :
    q ∈ smallClosed N e := by
  have hn : 1 < N := by exact_mod_cast (show (1 : ℝ) < N by linarith)
  obtain ⟨hr,hw⟩ := mem_filter.mp hq
  obtain ⟨pa,pb,pc,pd,_,_,_,hbc,hc,hcd,hd⟩ := relaxed_coordinates hN hρ hr hw
  have hca : coord N q.1 ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta :=
    ⟨ha,hu.trans Large.cutoff_geometry.1.2⟩
  have hcc : coord N q.2.2.1 ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta :=
    ⟨ha.trans (hab.trans hbc),hc⟩
  have hma := coord_mem_closed hn pa ha hca.2
  have hmb := coord_mem_closed hn pb hab (hbc.trans hc)
  have hmc := coord_mem_closed hn pc hbc hc
  rw [rpow_coord hn pa.pos] at hmb
  rw [rpow_coord hn pb.pos] at hmc
  have hmd : q.2.2.2 ∈ primesIcc ((N : ℝ)^(lower e (coord N q.2.2.1)))
      ((N : ℝ)^(upper e (coord N q.2.2.1))) := by
    apply coord_mem_closed hn pd
    · cases e
      · simpa only [lower,Bool.false_eq_true,↓reduceIte,cap_eq hcc] using hcd
      · exact hd.1
    · cases e
      · exact hd
      · simpa only [upper,↓reduceIte,cap_eq hcc] using hd.2
  obtain ⟨hl,hh⟩ := last_windows hn pc.pos hcc e
  rw [hl,hh] at hmd
  apply mem_filter.mpr
  refine ⟨mem_labels.mpr ⟨hma,hmb,hmc,hmd⟩,?_⟩
  exact (rpow_coord hn pa.pos).symm.trans_le
    (rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) hu)

theorem small_first_primes {N : ℕ} (hN : 1 < N) :
    (primesIcc ((N : ℝ)^FourRoughClosedMass.alpha) ((N : ℝ)^FourRoughClosedMass.beta)).filter
      (fun a : ℕ => (a : ℝ) ≤ (N : ℝ)^(1/10 : ℝ)) =
      primesIcc ((N : ℝ)^FourRoughClosedMass.alpha) ((N : ℝ)^(1/10 : ℝ)) := by
  have hp : (N : ℝ)^(1/10 : ℝ) ≤ (N : ℝ)^FourRoughClosedMass.beta :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) Large.cutoff_geometry.1.2
  ext a
  simp only [mem_filter,mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) FourRoughClosedMass.beta),
    mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) (1/10 : ℝ))]
  constructor
  · rintro ⟨⟨ha,hl,_⟩,hu⟩; exact ⟨ha,hl,hu⟩
  · rintro ⟨ha,hl,hu⟩; exact ⟨⟨ha,hl,hu.trans hp⟩,hu⟩

theorem smallClosed_nested {N : ℕ} (hN : 1 < N) (e : Bool) :
    (∑ q ∈ smallClosed N e, unshiftedTerm N q) =
      ∑ a ∈ primesIcc ((N : ℝ)^FourRoughClosedMass.alpha) ((N : ℝ)^(1/10 : ℝ)),
      ∑ b ∈ primesIcc a ((N : ℝ)^FourRoughClosedMass.beta),
      ∑ c ∈ primesIcc b ((N : ℝ)^FourRoughClosedMass.beta),
      ∑ d ∈ primesIcc (if e then (N : ℝ)^FourRoughClosedMass.beta else c)
        (if e then (N : ℝ)^lam/c else (N : ℝ)^FourRoughClosedMass.beta),
        atomWeight N a*density (coord N a) (coord N b) (coord N c) (coord N d)/(a*b*c*d : ℝ) := by
  rw [smallClosed,sum_filter,labelSet]
  have nested (f : SmallGrid.Quad → ℝ) (l u : ℕ → ℝ) :
      (∑ q ∈ FourRoughClosedMass.labels N l u, f q) =
        ∑ a ∈ primesIcc ((N : ℝ)^FourRoughClosedMass.alpha) ((N : ℝ)^FourRoughClosedMass.beta),
        ∑ b ∈ primesIcc a ((N : ℝ)^FourRoughClosedMass.beta),
        ∑ c ∈ primesIcc b ((N : ℝ)^FourRoughClosedMass.beta),
        ∑ d ∈ primesIcc (l c) (u c), f (a,b,c,d) := by
    simp only [FourRoughClosedMass.labels,sum_map,sum_sigma]
    rfl
  rw [nested,← small_first_primes hN,sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : (a : ℝ) ≤ (N : ℝ)^(1/10 : ℝ)
  · simp only [ha,↓reduceIte,unshiftedTerm,quadProduct,Nat.cast_mul]
  · simp only [ha,↓reduceIte,sum_const_zero]

/-- The weight is precisely 36/5/(1-x), not a constant replacement. -/
theorem smallClosed_eq_Q {N : ℕ} (hN : 1 < N) (e : Bool) :
    (∑ q ∈ smallClosed N e, unshiftedTerm N q) = SmallQuadrature.Q N e := by
  rw [smallClosed_nested hN e]
  unfold SmallQuadrature.Q primeOrderedClosedSum
  apply sum_congr rfl
  intro a ha
  have hca0 := closed_coord hN ha
  have hca : coord N a ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta :=
    ⟨hca0.1,hca0.2.trans Large.cutoff_geometry.1.2⟩
  have hpa := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) (1/10 : ℝ))).mp ha).1
  have haold : a ∈ primesIcc ((N : ℝ)^FourRoughClosedMass.alpha) ((N : ℝ)^FourRoughClosedMass.beta) :=
    (mem_filter.mp ((small_first_primes hN).symm ▸ ha)).1
  have hw : atomWeight N a = SmallQuadrature.W (coord N a) := by
    unfold atomWeight SmallQuadrature.W
    change (36/5)/(1-min (coord N a) (1/10)) = (36/5)/(1-coord N a)
    rw [min_eq_left hca0.2]
  rw [hw]
  unfold Q1 primeOrderedClosedSum
  simp only [← coord_eq_log]
  rw [cap_eq hca,rpow_coord hN hpa.pos,mul_sum,sum_div]
  apply sum_congr rfl
  intro b hb
  have hcb := prime_row_coord hN hca hpa.pos hb
  have hpb := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) FourRoughClosedMass.beta)).mp hb).1
  unfold Q2 primeOrderedClosedSum
  simp only [← coord_eq_log]
  rw [cap_eq hcb,rpow_coord hN hpb.pos,sum_div,mul_sum,sum_div]
  apply sum_congr rfl
  intro c hc
  have hcc := prime_row_coord hN hcb hpb.pos hc
  have hpc := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) FourRoughClosedMass.beta)).mp hc).1
  unfold Q3 primeOrderedClosedSum
  simp only [← coord_eq_log]
  obtain ⟨hl,hu⟩ := last_windows hN hpc.pos hcc e
  rw [hl,hu,sum_div,sum_div,mul_sum,sum_div]
  apply sum_congr rfl
  intro d hd
  have hq : (a,b,c,d) ∈ labelSet N e := mem_labels.mpr ⟨haold,hb,hc,hd⟩
  rw [F_actual hN e hq]
  ring

#check smallClosed
#print axioms smallClosed
#check smallClosed_nonneg
#print axioms smallClosed_nonneg
#check interior_mem
#print axioms interior_mem
#check small_first_primes
#print axioms small_first_primes
#check smallClosed_nested
#print axioms smallClosed_nested
#check smallClosed_eq_Q
#print axioms smallClosed_eq_Q
end Wu08FirstPrimeFour.SmallBoundaryRecovery
