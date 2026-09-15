import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRoughPurification
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughMassFinite

namespace Wu2008DoubleSieve.LowerTripleGroupedFinite
open Finset LiLiuPrereqBuchstab
open scoped Classical

abbrev PrimeTriple := ℕ × ℕ × ℕ

def tupleProduct (d : ℕ) (t : PrimeTriple) : ℕ := d*t.1*t.2.1*t.2.2

/-- Original physical r endpoints, not the unshifted source interval. -/
noncomputable def primeTriples (N : ℕ) (a f lo hi : ℝ) (pre : ℕ → ℕ → Prop) :
    Finset PrimeTriple :=
  ((primeWindow N a f).product ((primeWindow N a f).product (range (N+1)))).filter
    fun t => t.1 < t.2.1 ∧ pre t.1 t.2.1 ∧ t.2.2.Prime ∧
      max (t.2.1 : ℝ) (lo-1) < t.2.2 ∧ (t.2.2 : ℝ) ≤ hi

theorem mem_primeTriples {N : ℕ} {a f lo hi : ℝ} {pre : ℕ → ℕ → Prop}
    {t : PrimeTriple} : t ∈ primeTriples N a f lo hi pre ↔
    t.1 ∈ primeWindow N a f ∧ t.2.1 ∈ primeWindow N a f ∧ t.2.2 < N+1 ∧
    t.1 < t.2.1 ∧ pre t.1 t.2.1 ∧ t.2.2.Prime ∧
    max (t.2.1 : ℝ) (lo-1) < t.2.2 ∧ (t.2.2 : ℝ) ≤ hi := by
  simp only [primeTriples, mem_filter, Finset.product_eq_sprod, mem_product, mem_range]
  tauto

theorem tupleProduct_pos {N d : ℕ} {a f lo hi : ℝ} {pre : ℕ → ℕ → Prop}
    {t : PrimeTriple} (hd : 0 < d) (ht : t ∈ primeTriples N a f lo hi pre) :
    0 < tupleProduct d t := by
  obtain ⟨hp,hq,_,_,_,hr,_,_⟩ := mem_primeTriples.mp ht
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd
    (mem_primeWindow.mp hp).1.pos) (mem_primeWindow.mp hq).1.pos) hr.pos

theorem cofactor_tuple (d n : ℕ) (t : PrimeTriple) :
    LowerTripleGrouped.cofactor (d,t.1,t.2.1,n)*t.2.2 = n*tupleProduct d t := by
  simp only [LowerTripleGrouped.cofactor, tupleProduct]
  ring

/-- The inclusive residual dictionary keeps n=1. -/
theorem residual_dictionary (N D q : ℕ) (hD : 0 < D) :
    ((range (N+1)).filter fun n => 0 < n ∧ Rough (q : ℝ) n ∧ n*D ≤ N) =
      roughNumbers ((N : ℝ)/D) q := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  ext n
  rw [mem_filter, mem_range, mem_roughNumbers, le_div_iff₀ hDR]
  have hc : (n : ℝ)*D ≤ N ↔ n*D ≤ N := by exact_mod_cast Iff.rfl
  rw [hc]
  constructor
  · rintro ⟨_,hn,hr,hcap⟩
    exact ⟨hn,hcap,hr⟩
  · rintro ⟨hn,hcap,hr⟩
    exact ⟨Nat.lt_succ_of_le ((Nat.le_mul_of_pos_right n hD).trans hcap),hn,hr,hcap⟩

/-- Rough n implies the full original E-mask: d,p are masked and q is the boundary. -/
theorem rough_full_mask (N d p q n : ℕ) (hq : q.Prime) (hn : Rough (q : ℝ) n) :
    Sifted (d*p*N) (LowerTripleGrouped.cofactor (d,p,q,n)) q := by
  intro s hs hcop hsq hdiv
  change s ∣ d*p*q*n at hdiv
  rcases hs.dvd_mul.mp hdiv with hdiv | hdiv
  · rcases hs.dvd_mul.mp hdiv with hdiv | hdiv
    · have hM : s ∣ d*p*N := dvd_mul_of_dvd_left hdiv N
      exact hs.not_dvd_one ((hcop.gcd_eq_one) ▸ Nat.dvd_gcd (dvd_refl s) hM)
    · have he : s = q := (Nat.dvd_prime hq).mp hdiv |>.resolve_left hs.ne_one
      subst s
      exact (lt_irrefl (q : ℝ)) hsq
  · exact (not_le_of_gt hsq) (hn s hs hdiv)

noncomputable def actualPrimeTriples (N : ℕ) (δ : ℝ) (P : SecondFunctionalParameters)
    (j : Fin 6) (d : ℕ) : Finset PrimeTriple :=
  primeTriples N (wuLocalCutoff N δ d P.S) (wuLocalCutoff N δ d P.s)
    (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.1
    (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.2
    (LowerTripleGrouped.actualPre N δ P j d)

/-- Exact label/physical-prime membership, including range and feasibility recovery. -/
theorem actual_atom_iff {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) (d n : ℕ) (t : PrimeTriple) :
    ((d,t.1,t.2.1,n) ∈ (LowerTripleGrouped.roughFamily N δ Δ V P j).labels ∧
      t.2.2 ∈ (LowerTripleGrouped.roughFamily N δ Δ V P j).primes (d,t.1,t.2.1,n)) ↔
    d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
      t ∈ actualPrimeTriples N δ P j d ∧
      n ∈ roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1 := by
  let L := LowerTripleGrouped.roughFamily N δ Δ V P j
  constructor
  · rintro ⟨hx,hr⟩
    obtain ⟨hlabel,hrough⟩ := (LowerTripleGrouped.mem_roughFamily_labels P j _).mp hx
    obtain ⟨hd,hp,hq,hnN,hpq,hpre,hn,_,_⟩ := (LowerTripleGrouped.mem_labels _).mp hlabel
    have hr' : t.2.2 < N+1 ∧ t.2.2.Prime ∧
        LowerTripleGrouped.lower (fun d => (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.1)
          (d,t.1,t.2.1,n) < t.2.2 ∧
        (t.2.2 : ℝ) ≤ LowerTripleGrouped.upper N
          (fun d => (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.2) (d,t.1,t.2.1,n) := by
      exact ⟨mem_range.mp (mem_filter.mp hr).1,(mem_filter.mp hr).2⟩
    have ht : t ∈ actualPrimeTriples N δ P j d := mem_primeTriples.mpr
      ⟨hp,hq,hr'.1,hpq,hpre,hr'.2.1,hr'.2.2.1,hr'.2.2.2.trans (min_le_left _ _)⟩
    have hdp : 0 < d := boxConvolutionSupport_pos
      (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd
    refine ⟨hd,ht,?_⟩
    rw [← residual_dictionary N _ _ (tupleProduct_pos hdp ht), mem_filter, mem_range]
    exact ⟨hnN,hn,hrough,(cofactor_tuple d n t) ▸ L.output_le hx hr⟩
  · rintro ⟨hd,ht,hnr⟩
    have hdp : 0 < d := boxConvolutionSupport_pos
      (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd
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
        (fun d => (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.2) (d,t.1,t.2.1,n) :=
      le_min hu ((le_div_iff₀ hER).mpr (by rw [mul_comm]; exact_mod_cast hcap'))
    constructor
    · apply (LowerTripleGrouped.mem_roughFamily_labels P j _).mpr
      exact ⟨(LowerTripleGrouped.mem_labels _).mpr
        ⟨hd,hp,hq,hnN,hpq,hpre,hn,rough_full_mask N d t.1 t.2.1 n
          (mem_primeWindow.mp hq).1 hrough,hl.le.trans hub⟩,hrough⟩
    · change t.2.2 ∈ omega3ProfilePrimes N _ _
      exact mem_filter.mpr ⟨mem_range.mpr hrN,hr,hl,hub⟩

/-- A coordinate permutation, never an image under the product map. -/
def regroup (x : Σ _ : LowerTripleGrouped.Label, ℕ) : Σ _ : ℕ, Σ _ : PrimeTriple, ℕ :=
  ⟨x.1.1,(x.1.2.1,x.1.2.2.1,x.2),x.1.2.2.2⟩

def ungroup (y : Σ _ : ℕ, Σ _ : PrimeTriple, ℕ) : Σ _ : LowerTripleGrouped.Label, ℕ :=
  ⟨(y.1,y.2.1.1,y.2.1.2.1,y.2.2),y.2.1.2.2⟩

theorem ungroup_regroup (x : Σ _ : LowerTripleGrouped.Label, ℕ) :
    ungroup (regroup x) = x := by
  rcases x with ⟨⟨d,p,q,n⟩,r⟩
  rfl

theorem regroup_ungroup (y : Σ _ : ℕ, Σ _ : PrimeTriple, ℕ) :
    regroup (ungroup y) = y := by
  rcases y with ⟨d,⟨⟨p,q,r⟩,n⟩⟩
  rfl

/-- Exact finite reordering of the canonical rough raw mass with sigma appearing once. -/
theorem rough_mass_triple_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) :
    (LowerTripleGrouped.roughFamily N δ Δ V P j).mass =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ∑ t ∈ actualPrimeTriples N δ P j d,
          ((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).card : ℝ) := by
  let L := LowerTripleGrouped.roughFamily N δ Δ V P j
  let W := convolutionWuWindows N Δ V
  let A := L.labels.sigma L.primes
  let B := (boxConvolutionSupport W).sigma fun d =>
    (actualPrimeTriples N δ P j d).sigma fun t =>
      roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1
  have hm : ∀ x, x ∈ A ↔ regroup x ∈ B := by
    rintro ⟨⟨d,p,q,n⟩,r⟩
    simpa only [A,B,regroup,mem_sigma,L,W] using actual_atom_iff N δ Δ V P j d n (p,q,r)
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
    LabelledPhysical.Family.mass, LowerTripleGrouped.roughFamily,
    LabelledPhysical.Family.restrictLabels, LowerTripleGrouped.sourceFamily,
    LowerTripleGrouped.family] using hsum

/-- The complete six-band finite dictionary, with no union or product-image deduplication. -/
theorem six_rough_mass_triple_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) :
    (∑ j : Fin 6, (LowerTripleGrouped.roughFamily N δ Δ V P j).mass) =
      ∑ j : Fin 6, ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ∑ t ∈ actualPrimeTriples N δ P j d,
          ((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).card : ℝ) := by
  exact sum_congr rfl (fun j _ => rough_mass_triple_dictionary N δ Δ V P j)

/-- The original residual fibre is inclusive, not erase-one. -/
theorem original_residual_fibre_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) (d : ℕ) (t : PrimeTriple)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (ht : t ∈ actualPrimeTriples N δ P j d) :
    ((range (N+1)).filter fun n =>
      (d,t.1,t.2.1,n) ∈ (LowerTripleGrouped.roughFamily N δ Δ V P j).labels ∧
      t.2.2 ∈ (LowerTripleGrouped.roughFamily N δ Δ V P j).primes (d,t.1,t.2.1,n)) =
      roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1 := by
  ext n
  rw [mem_filter,actual_atom_iff]
  simp only [hd,ht,true_and]
  exact and_iff_right_of_imp (fun h => by
    have hpos : 0 < d := boxConvolutionSupport_pos
      (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd
    rw [← residual_dictionary N _ _ (tupleProduct_pos hpos ht)] at h
    exact (mem_filter.mp h).1)

/-- Exact unit indicator, valid also when D>N or N=0. -/
theorem one_mem_roughNumbers_iff (N D q : ℕ) (hD : 0 < D) :
    1 ∈ roughNumbers ((N : ℝ)/D) q ↔ D ≤ N := by
  rw [← residual_dictionary N D q hD,mem_filter,mem_range]
  have hr : Rough (q : ℝ) 1 := LowerTripleGrouped.profileRough_one 1 1 q
  simp only [zero_lt_one,one_mul,hr,true_and]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by omega,h⟩

theorem residual_card_unit_nonunit (N D q : ℕ) (hD : 0 < D) :
    ((roughNumbers ((N : ℝ)/D) q).card : ℝ) =
      (if D ≤ N then 1 else 0) + (((roughNumbers ((N : ℝ)/D) q).erase 1).card : ℝ) := by
  by_cases h : D ≤ N
  · have hm := (one_mem_roughNumbers_iff N D q hD).mpr h
    have hc := card_erase_add_one hm
    rw [if_pos h]
    exact_mod_cast hc.symm.trans (Nat.add_comm _ _)
  · have hm := mt (one_mem_roughNumbers_iff N D q hD).mp h
    simp only [if_neg h,erase_eq_of_notMem hm,zero_add]

noncomputable def unitMass {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ t ∈ actualPrimeTriples N δ P j d, if tupleProduct d t ≤ N then 1 else 0

noncomputable def nonunitMass {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ t ∈ actualPrimeTriples N δ P j d,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ)

/-- No unit term is discarded or declared paid. -/
theorem rough_mass_unit_nonunit {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) :
    (LowerTripleGrouped.roughFamily N δ Δ V P j).mass =
      unitMass N δ Δ V P j + nonunitMass N δ Δ V P j := by
  rw [rough_mass_triple_dictionary]
  unfold unitMass nonunitMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← mul_add,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro t ht
  exact residual_card_unit_nonunit N _ _ (tupleProduct_pos
    (boxConvolutionSupport_pos (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd) ht)

/-- Six original overlapping bands are summed separately with their full sigma weights. -/
theorem six_rough_mass_unit_nonunit {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) :
    (∑ j : Fin 6, (LowerTripleGrouped.roughFamily N δ Δ V P j).mass) =
      (∑ j : Fin 6, unitMass N δ Δ V P j) + ∑ j : Fin 6, nonunitMass N δ Δ V P j := by
  simp_rw [rough_mass_unit_nonunit]
  exact sum_add_distrib

end Wu2008DoubleSieve.LowerTripleGroupedFinite
