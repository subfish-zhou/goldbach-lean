import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitRoughPurification
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughMassFinite

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset LiLiuPrereqBuchstab
open scoped Classical

/-- Coordinates are p3,p2,p1,q; the residual is an independent summation variable. -/
abbrev PrimeTuple := ℕ × ℕ × ℕ × ℕ

def tupleList (t : PrimeTuple) : List ℕ := [t.2.2.1,t.2.1,t.1,t.2.2.2]
def tupleProduct (d : ℕ) (t : PrimeTuple) : ℕ := d*t.2.2.1*t.2.1*t.1*t.2.2.2

def prefixOK (b c e : ℝ) (cs : List ℕ) (t : PrimeTuple) : Prop :=
  t.2.2.1 < t.2.1 ∧ t.2.1 < t.1 ∧
    [t.2.2.1,t.2.1,t.1].map (secondFunctionalMotherColour b c e) = cs.take 3

def lastOK (lo hi : ℝ) (t : PrimeTuple) : Prop :=
  t.2.2.2.Prime ∧ t.1 < t.2.2.2 ∧ lo ≤ (t.2.2.2 : ℝ) ∧ (t.2.2.2 : ℝ) ≤ hi

/-- The first three windows retain copN; q has the original closed band and no copN. -/
noncomputable def primeTuples (N : ℕ) (a b c e f lo hi : ℝ) (cs : List ℕ) :
    Finset PrimeTuple :=
  ((primeWindow N a f).product ((primeWindow N a f).product
    ((primeWindow N a f).product (range (N+1))))).filter fun t =>
      prefixOK b c e cs t ∧ lastOK lo hi t

theorem mem_primeTuples {N : ℕ} {a b c e f lo hi : ℝ} {cs : List ℕ} {t : PrimeTuple} :
    t ∈ primeTuples N a b c e f lo hi cs ↔
      t.1 ∈ primeWindow N a f ∧ t.2.1 ∈ primeWindow N a f ∧
      t.2.2.1 ∈ primeWindow N a f ∧ t.2.2.2 ≤ N ∧
      prefixOK b c e cs t ∧ lastOK lo hi t := by
  simp only [primeTuples, mem_filter, Finset.product_eq_sprod, mem_product,
    mem_range, Nat.lt_succ_iff]
  tauto

theorem tupleProduct_pos {N d : ℕ} {a b c e f lo hi : ℝ} {cs : List ℕ}
    (hd : 0 < d) {t : PrimeTuple} (ht : t ∈ primeTuples N a b c e f lo hi cs) :
    0 < tupleProduct d t := by
  obtain ⟨h3,h2,h1,_,_,hq⟩ := mem_primeTuples.mp ht
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd
    (mem_primeWindow.mp h1).1.pos) (mem_primeWindow.mp h2).1.pos)
    (mem_primeWindow.mp h3).1.pos) hq.1.pos

theorem cofactor_tuple (d n : ℕ) (t : PrimeTuple) :
    gamma16Cofactor ⟨d,t.1,t.2.1,t.2.2.1,n⟩ * t.2.2.2 = n*tupleProduct d t := by
  simp only [gamma16Cofactor, tupleProduct]
  ring

/-- Exact residual dictionary, with neither a primality test on n nor a scalar hypothesis. -/
theorem residual_dictionary (N D p3 : ℕ) (hD : 0 < D) :
    ((range (N+1)).filter fun n => 2 ≤ n ∧ Rough (p3 : ℝ) n ∧ n*D ≤ N) =
      (roughNumbers ((N : ℝ)/D) p3).erase 1 :=
  HighNonunit.residual_dictionary N D p3 hD

/-- Roughness supplies the original masked sieve; q>p3 supplies the redundant cap. -/
theorem rough_atom_iff (N d n : ℕ) (t : PrimeTuple) (cs : List ℕ) (b c e lo hi : ℝ) :
    (2 ≤ n ∧ Sifted (d*t.2.2.1*t.2.1*N) n t.1 ∧
      prefixOK b c e cs t ∧ gamma16Cofactor ⟨d,t.1,t.2.1,t.2.2.1,n⟩*t.1 ≤ N) ∧
      lastOK lo hi t ∧ gamma16Cofactor ⟨d,t.1,t.2.1,t.2.2.1,n⟩*t.2.2.2 ≤ N ∧
      Rough (t.1 : ℝ) n ↔
    (prefixOK b c e cs t ∧ lastOK lo hi t) ∧
      2 ≤ n ∧ Rough (t.1 : ℝ) n ∧ n*tupleProduct d t ≤ N := by
  rw [← cofactor_tuple]
  constructor
  · rintro ⟨⟨hn,_,hp,_⟩,hq,hcap,hr⟩
    exact ⟨⟨hp,hq⟩,hn,hr,hcap⟩
  · rintro ⟨⟨hp,hq⟩,hn,hr,hcap⟩
    exact ⟨⟨hn,HighNonunit.rough_sifted _ _ _ hr,hp,
      (Nat.mul_le_mul_left _ hq.2.1.le).trans hcap⟩,hq,hcap,hr⟩

theorem tupleList_length (t : PrimeTuple) : (tupleList t).length = 4 := rfl

theorem tupleProduct_literal (d : ℕ) (t : PrimeTuple) :
    tupleProduct d t = d * (tupleList t).prod := by
  simp only [tupleProduct, tupleList, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

/-- The original profile/raw-prime fibre is literally the erased rough-number set. -/
theorem original_residual_fibre_dictionary {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) (d : ℕ) (t : PrimeTuple)
    (hd : d ∈ boxConvolutionSupport W) (hdpos : 0 < d)
    (ht : t ∈ primeTuples N (a d) (b d) (c d) (e d) (f d)
      (lastLower c e cs d) (lastUpper e f cs d) cs) :
    ((range (N+1)).filter fun n =>
      (⟨d,t.1,t.2.1,t.2.2.1,n⟩ : Gamma16Profile) ∈ profiles N W a b c e f cs ∧
      profileRough ⟨d,t.1,t.2.1,t.2.2.1,n⟩ ∧
      t.2.2.2 ∈ rawFibre N c e f cs ⟨d,t.1,t.2.1,t.2.2.1,n⟩) =
      (roughNumbers ((N : ℝ)/tupleProduct d t) t.1).erase 1 := by
  rw [← residual_dictionary N _ _ (tupleProduct_pos hdpos ht)]
  obtain ⟨h3,h2,h1,hqN,hpre,hlast⟩ := mem_primeTuples.mp ht
  ext n
  simp only [mem_filter, mem_range, mem_profiles, rawFibre, profileRough]
  have hq : t.2.2.2 < N+1 := Nat.lt_succ_of_le hqN
  have ha := rough_atom_iff N d n t cs (b d) (c d) (e d)
    (lastLower c e cs d) (lastUpper e f cs d)
  obtain ⟨h12,h23,hcol⟩ := hpre
  obtain ⟨hprime,h34,hlo,hhi⟩ := hlast
  simp only [prefixOK, lastOK, h12, h23, hcol, hprime, h34, hlo, hhi,
    true_and, and_true] at ha
  simp only [hd, h3, h2, h1, hq, h12, h23, hcol, hprime, h34, hlo, hhi,
    true_and]
  tauto

/-- Exact finite Fubini over the full original labels, without identifying products. -/
theorem rough_profiles_dictionary {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (∑ x ∈ profiles N W a b c e f cs, ∑ _q ∈ rawFibre N c e f cs x,
      if profileRough x then (convolutionCoeff W x.1 : ℝ) else 0) =
    ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ t ∈ primeTuples N (a d) (b d) (c d) (e d) (f d)
        (lastLower c e cs d) (lastUpper e f cs d) cs,
        (((roughNumbers ((N : ℝ)/tupleProduct d t) t.1).erase 1).card : ℝ) := by
  have hres : ∀ d ∈ boxConvolutionSupport W,
      ∀ t ∈ primeTuples N (a d) (b d) (c d) (e d) (f d)
        (lastLower c e cs d) (lastUpper e f cs d) cs,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.1).erase 1).card : ℝ) =
        ∑ n ∈ range (N+1),
          if 2 ≤ n ∧ Rough (t.1 : ℝ) n ∧ n*tupleProduct d t ≤ N then 1 else 0 := by
    intro d hd' t ht
    rw [← residual_dictionary N _ _ (tupleProduct_pos (hd d hd') ht), sum_boole]
  simp only [profiles, sum_sigma, sum_filter]
  apply sum_congr rfl
  intro d hd'
  rw [sum_congr rfl (hres d hd'), mul_sum]
  simp only [mul_sum, primeTuples, sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply sum_congr rfl
  intro p3 _
  apply sum_congr rfl
  intro p2 _
  apply sum_congr rfl
  intro p1 _
  simp only [rawFibre, sum_filter]
  simp_rw [HighNonunit.ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro n _
  have ha := rough_atom_iff N d n (p3,p2,p1,q) cs (b d) (c d) (e d)
    (lastLower c e cs d) (lastUpper e f cs d)
  simp only [mul_ite, mul_one, mul_zero, ← ite_and]
  apply if_congr
  · simpa only [and_assoc, prefixOK, lastOK, profileRough] using ha
  · rfl
  · rfl

noncomputable def actualPrimeTuples (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (j : Fin 4) (d : ℕ) : Finset PrimeTuple :=
  primeTuples N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.kappa1)
    (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3)
    (wuLocalCutoff N δ d p.s)
    (lastLower (fun d => wuLocalCutoff N δ d p.kappa2)
      (fun d => wuLocalCutoff N δ d p.kappa3) (FourPrimeUnit.word j) d)
    (lastUpper (fun d => wuLocalCutoff N δ d p.kappa3)
      (fun d => wuLocalCutoff N δ d p.s) (FourPrimeUnit.word j) d) (FourPrimeUnit.word j)

/-- The canonical raw mass, including all convolution decompositions and deleted empty fibres. -/
theorem rough_mass_tuple_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    (roughFamily N δ Δ V p j).mass =
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ∑ t ∈ actualPrimeTuples N δ p j d,
        (((roughNumbers ((N : ℝ)/tupleProduct d t) t.1).erase 1).card : ℝ) := by
  let W := convolutionWuWindows N Δ V
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun _ h => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) h
  rw [roughFamily_mass_dictionary]
  have hh := rough_profiles_dictionary N W
    (fun d => wuLocalCutoff N δ d p.S) (fun d => wuLocalCutoff N δ d p.kappa1)
    (fun d => wuLocalCutoff N δ d p.kappa2) (fun d => wuLocalCutoff N δ d p.kappa3)
    (fun d => wuLocalCutoff N δ d p.s) (FourPrimeUnit.word j) hd
  simpa only [actualProfiles, actualRawFibre, actualPrimeTuples, sum_filter,
    sum_ite_irrel, sum_const_zero, sum_const, nsmul_eq_mul, mul_comm, W] using hh

end Wu2008DoubleSieve.FourPrimeNonunit
