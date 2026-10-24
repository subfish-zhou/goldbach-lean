import WR2GammaHighLowerTripleR2
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRoughMassFinite

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped LowerTripleGroupedFinite Finset LiLiuPrereqBuchstab
open scoped Classical

def roughFamily (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) : LabelledPhysical.Family Label N :=
  (sourceFamily j N δ k).restrictLabels profileRough

theorem mem_rough_labels (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) (x : Label) :
    x ∈ (roughFamily j N δ k).labels ↔ x ∈ (sourceFamily j N δ k).labels ∧ profileRough x := mem_filter

/-- Preserve the actual prime mass while separating square and noncoprime exceptions. -/
theorem prime_mass_split {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    (sourceFamily j N δ k).primeMass ≤ (roughFamily j N δ k).primeMass+
      (sourceFamily j N δ k).squareRawMass ((N : ℝ)^HighBoxRecovery.highEta)+
      (sourceFamily j N δ k).noncoprimePart.primeMass := by
  apply LabelledPhysical.Family.primeMass_le_restrict_add_square_add_bad
  intro x hx hc hn
  have hs := (mem_labels x).mp hx |>.2.2.2.2.2.2.2.1
  exact masked_good_nonrough_square hs hc hn (relative_rough j k hN hd hh hx)

theorem actual_atom_iff (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) (d n : ℕ) (t : PrimeTriple) :
    ((d,t.1,t.2.1,n) ∈ (roughFamily j N δ k).labels ∧
      t.2.2 ∈ (roughFamily j N δ k).primes (d,t.1,t.2.1,n)) ↔
    d ∈ boxConvolutionSupport (windows j N) ∧
      t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d ∧
      n ∈ roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1 := by
  let L := roughFamily j N δ k
  constructor
  · rintro ⟨hx,hr⟩
    obtain ⟨hlabel,hrough⟩ := (mem_rough_labels j N δ k _).mp hx
    obtain ⟨hd,hp,hq,hnN,hpq,hpre,hn,_,_⟩ := (LowerTripleGrouped.mem_labels _).mp hlabel
    have hr' : t.2.2 < N+1 ∧ t.2.2.Prime ∧
        LowerTripleGrouped.lower (fun d => (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.1)
          (d,t.1,t.2.1,n) < t.2.2 ∧
        (t.2.2 : ℝ) ≤ LowerTripleGrouped.upper N
          (fun d => (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.2) (d,t.1,t.2.1,n) := by
      exact ⟨mem_range.mp (mem_filter.mp hr).1,(mem_filter.mp hr).2⟩
    have ht : t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d := mem_primeTriples.mpr
      ⟨hp,hq,hr'.1,hpq,hpre,hr'.2.1,hr'.2.2.1,hr'.2.2.2.trans (min_le_left _ _)⟩
    have hdp : 0 < d := boxConvolutionSupport_pos
      (fun _ _ h => (mem_primeWindow.mp h).1.pos) hd
    refine ⟨hd,ht,?_⟩
    rw [← residual_dictionary N _ _ (tupleProduct_pos hdp ht), mem_filter, mem_range]
    exact ⟨hnN,hn,hrough,(cofactor_tuple d n t) ▸ L.output_le hx hr⟩
  · rintro ⟨hd,ht,hnr⟩
    have hdp : 0 < d := boxConvolutionSupport_pos
      (fun _ _ h => (mem_primeWindow.mp h).1.pos) hd
    have hD := tupleProduct_pos hdp ht
    rw [← residual_dictionary N _ _ hD, mem_filter, mem_range] at hnr
    obtain ⟨hnN,hn,hrough,hcap⟩ := hnr
    obtain ⟨hp,hq,hrN,hpq,hpre,hr,hl,hu⟩ := mem_primeTriples.mp ht
    have hE : 0 < LowerTripleGrouped.cofactor (d,t.1,t.2.1,n) :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdp (mem_primeWindow.mp hp).1.pos)
        (mem_primeWindow.mp hq).1.pos) hn
    have hER : (0 : ℝ) < LowerTripleGrouped.cofactor (d,t.1,t.2.1,n) := by exact_mod_cast hE
    have hcap' : LowerTripleGrouped.cofactor (d,t.1,t.2.1,n)*t.2.2 ≤ N := by
      rwa [cofactor_tuple]
    have hub : (t.2.2 : ℝ) ≤ LowerTripleGrouped.upper N
        (fun d => (LowerTripleGrouped.actualBands N δ (Wu04RemainingCore.row j) k d).2.2.2.2.2) (d,t.1,t.2.1,n) :=
      le_min hu ((le_div_iff₀ hER).mpr (by rw [mul_comm]; exact_mod_cast hcap'))
    constructor
    · apply (mem_rough_labels j N δ k _).mpr
      exact ⟨(LowerTripleGrouped.mem_labels _).mpr
        ⟨hd,hp,hq,hnN,hpq,hpre,hn,rough_full_mask N d t.1 t.2.1 n
          (mem_primeWindow.mp hq).1 hrough,hl.le.trans hub⟩,hrough⟩
    · change t.2.2 ∈ omega3ProfilePrimes N _ _
      exact mem_filter.mpr ⟨mem_range.mpr hrN,hr,hl,hub⟩

theorem rough_mass_triple_dictionary (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) :
    (roughFamily j N δ k).mass =
      ∑ d ∈ boxConvolutionSupport (windows j N),
        (convolutionCoeff (windows j N) d : ℝ) *
        ∑ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d,
          ((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).card : ℝ) := by
  let L := roughFamily j N δ k
  let W := windows j N
  let A := L.labels.sigma L.primes
  let B := (boxConvolutionSupport W).sigma fun d =>
    (actualPrimeTriples N δ (Wu04RemainingCore.row j) k d).sigma fun t =>
      roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1
  have hm : ∀ x, x ∈ A ↔ regroup x ∈ B := by
    rintro ⟨⟨d,p,q,n⟩,r⟩
    simpa only [A,B,regroup,mem_sigma,L,W] using actual_atom_iff j N δ k d n (p,q,r)
  have hsum : (∑ x ∈ A, (convolutionCoeff W x.1.1 : ℝ)) =
      ∑ y ∈ B, (convolutionCoeff W y.1 : ℝ) := by
    apply sum_bij (fun x _ => regroup x)
    · intro x hx
      exact (hm x).mp hx
    · intro x _ y _ hxy
      exact (ungroup_regroup x).symm.trans ((congrArg ungroup hxy).trans (ungroup_regroup y))
    · intro y hy
      refine ⟨ungroup y, (hm _).mpr ?_,regroup_ungroup y⟩
      simpa only [regroup_ungroup] using hy
    · intro x _
      rfl
  simpa only [A,B,sum_sigma,sum_const,card_sigma,Nat.cast_sum,nsmul_eq_mul,mul_comm,mul_sum,L,W,
    LabelledPhysical.Family.mass, roughFamily,
    LabelledPhysical.Family.restrictLabels, sourceFamily,
    LowerTripleGrouped.family] using hsum


end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.prime_mass_split
#print axioms WuPaper.R2GammaHigh.LowerTriple.rough_mass_triple_dictionary
