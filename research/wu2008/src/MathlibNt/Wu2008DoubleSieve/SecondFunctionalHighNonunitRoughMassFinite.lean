import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughFamily

namespace Wu2008DoubleSieve.HighNonunit
open Finset
open scoped Classical
open LiLiuPrereqBuchstab

/-- The residual is not one of the prime labels. -/
abbrev PrimeTuple := List ℕ × (ℕ × ℕ)

def tupleList (t : PrimeTuple) : List ℕ := t.1 ++ [t.2.1,t.2.2]
def tupleProduct (d : ℕ) (t : PrimeTuple) : ℕ := d * (tupleList t).prod

def prefixOK (b c e : ℝ) (cs pre : List ℕ) (p : ℕ) : Prop :=
  (pre ++ [p]).Pairwise (· < ·) ∧
  (pre ++ [p]).map (secondFunctionalMotherColour b c e) = cs.take (cs.length-1)

def lastOK (e f : ℝ) (p q : ℕ) : Prop :=
  q.Prime ∧ p < q ∧ e ≤ (q : ℝ) ∧ (q : ℝ) ≤ f

/-- Complete ordered labels. Only the last prime has a closed upper endpoint and no copN. -/
noncomputable def primeTuples (N : ℕ) (a b c e f : ℝ) (cs : List ℕ) : Finset PrimeTuple :=
  ((secondFunctionalMotherTuples (primeWindow N a f) (cs.length-2)).product
    ((primeWindow N a f).product (range (N+1)))).filter fun t =>
      prefixOK b c e cs t.1 t.2.1 ∧ lastOK e f t.2.1 t.2.2

theorem mem_primeTuples {N : ℕ} {a b c e f : ℝ} {cs : List ℕ} {t : PrimeTuple} :
    t ∈ primeTuples N a b c e f cs ↔
    t.1 ∈ secondFunctionalMotherTuples (primeWindow N a f) (cs.length-2) ∧
    t.2.1 ∈ primeWindow N a f ∧ t.2.2 ≤ N ∧
    prefixOK b c e cs t.1 t.2.1 ∧ lastOK e f t.2.1 t.2.2 := by
  rcases t with ⟨pre,p,q⟩
  simp only [primeTuples, mem_filter, Finset.product_eq_sprod, Finset.mem_product, mem_range, Nat.lt_succ_iff]
  tauto

theorem tuple_length {N : ℕ} {a b c e f : ℝ} {cs : List ℕ} {t : PrimeTuple}
    (hcs : 2 ≤ cs.length) (ht : t ∈ primeTuples N a b c e f cs) :
    (tupleList t).length = cs.length := by
  have hh := ((secondFunctionalMother_tuple_mem _ _ _).mp
    (mem_primeTuples.mp ht).1).1
  simp only [tupleList, List.length_append, List.length_cons, List.length_nil]
  omega

theorem rough_sifted (M p n : ℕ) (h : Rough (p : ℝ) n) : Sifted M n p := by
  intro r hr _ hrp hrd
  exact (not_le_of_gt hrp) (h r hr hrd)

theorem cofactor_tuple (d n : ℕ) (t : PrimeTuple) :
    cofactor ⟨d,t.1,t.2.1,n⟩ * t.2.2 = n * tupleProduct d t := by
  simp only [cofactor, tupleProduct, tupleList, List.prod_append, List.prod_cons,
    List.prod_nil]
  ring

/-- Exact erase-one dictionary, including zero and unit edge cases. -/
theorem mem_nonunit_rough {x y : ℝ} {n : ℕ} :
    n ∈ (roughNumbers x y).erase 1 ↔ 2 ≤ n ∧ (n : ℝ) ≤ x ∧ Rough y n := by
  rw [mem_erase, mem_roughNumbers]
  constructor
  · rintro ⟨hn, hp, hx, hr⟩
    exact ⟨by omega, hx, hr⟩
  · rintro ⟨hn, hx, hr⟩
    exact ⟨by omega, by omega, hx, hr⟩

theorem residual_dictionary (N D p : ℕ) (hD : 0 < D) :
    ((range (N+1)).filter fun n => 2 ≤ n ∧ Rough (p : ℝ) n ∧ n*D ≤ N) =
      (roughNumbers ((N : ℝ)/D) p).erase 1 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  ext n
  rw [mem_filter, mem_range, mem_nonunit_rough, le_div_iff₀ hDR]
  have hc : (n : ℝ) * D ≤ N ↔ n*D ≤ N := by exact_mod_cast Iff.rfl
  rw [hc]
  constructor
  · rintro ⟨_,hn,hr,hcap⟩
    exact ⟨hn,hcap,hr⟩
  · rintro ⟨hn,hcap,hr⟩
    exact ⟨Nat.lt_succ_of_le ((Nat.le_mul_of_pos_right n hD).trans hcap),hn,hr,hcap⟩

theorem tupleProduct_pos {N d : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hd : 0 < d) {t : PrimeTuple} (ht : t ∈ primeTuples N a b c e f cs) :
    0 < tupleProduct d t := by
  obtain ⟨hpre,hp,_,_,hq⟩ := mem_primeTuples.mp ht
  apply Nat.mul_pos hd
  apply List.prod_pos
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (mem_primeWindow.mp
      (((secondFunctionalMother_tuple_mem _ _ _).mp hpre).2.2 r hr)).1.pos
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (mem_primeWindow.mp hp).1.pos
    · exact hq.1.pos

/-- The two inner filters agree pointwise; the redundant penultimate cap is derived. -/
theorem rough_atom_iff (N d p n q : ℕ) (pre cs : List ℕ) (b c e f : ℝ) :
    (2 ≤ n ∧ Sifted (d*pre.prod*N) n p ∧
      prefixOK b c e cs pre p ∧ cofactor ⟨d,pre,p,n⟩*p ≤ N) ∧
      lastOK e f p q ∧ cofactor ⟨d,pre,p,n⟩*q ≤ N ∧ Rough (p : ℝ) n ↔
    (prefixOK b c e cs pre p ∧ lastOK e f p q) ∧
      2 ≤ n ∧ Rough (p : ℝ) n ∧ n*tupleProduct d (pre,p,q) ≤ N := by
  rw [← cofactor_tuple]
  constructor
  · rintro ⟨⟨hn,_,hpre,_⟩,hq,hcap,hr⟩
    exact ⟨⟨hpre,hq⟩,hn,hr,hcap⟩
  · rintro ⟨⟨hpre,hq⟩,hn,hr,hcap⟩
    exact ⟨⟨hn,rough_sifted _ _ _ hr,hpre,
      (Nat.mul_le_mul_left _ hq.2.1.le).trans hcap⟩,hq,hcap,hr⟩

theorem ite_sum_zero {α : Type*} (s : Finset α) (P : Prop) [Decidable P] (g : α → ℝ) :
    (if P then ∑ x ∈ s, g x else 0) = ∑ x ∈ s, if P then g x else 0 := by
  by_cases h : P <;> simp [h]

/-- Exact finite Fubini on complete labels, with the original convolution weight once. -/
theorem rough_profiles_dictionary {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (∑ x ∈ profiles N W a b c e f cs, ∑ _q ∈ rawFibre N e f x,
      if profileRough x then (convolutionCoeff W x.1 : ℝ) else 0) =
    ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ t ∈ primeTuples N (a d) (b d) (c d) (e d) (f d) cs,
        (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ) := by
  have hres : ∀ d ∈ boxConvolutionSupport W,
      ∀ t ∈ primeTuples N (a d) (b d) (c d) (e d) (f d) cs,
      (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ) =
        ∑ n ∈ range (N+1),
          if 2 ≤ n ∧ Rough (t.2.1 : ℝ) n ∧ n*tupleProduct d t ≤ N then 1 else 0 := by
    intro d hd' t ht
    rw [← residual_dictionary N _ _ (tupleProduct_pos (hd d hd') ht), sum_boole]
  simp only [profiles, sum_sigma, sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply sum_congr rfl
  intro d hd'
  have hs := sum_congr rfl (hres d hd')
  rw [hs, mul_sum]
  simp only [mul_sum]
  simp only [primeTuples, sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply sum_congr rfl
  intro pre _
  apply sum_congr rfl
  intro p _
  simp only [rawFibre, sum_filter]
  simp_rw [ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro n _
  -- All remaining tests are decidable predicates on the same four coordinates.
  have ha := rough_atom_iff N d p n q pre cs (b d) (c d) (e d) (f d)
  simp only [mul_ite, mul_one, mul_zero, ← ite_and]
  apply if_congr
  · simpa only [and_assoc, prefixOK, lastOK, profileRough] using ha
  · rfl
  · rfl

/-- Geometry deletion is removed with the accepted arbitrary-test dictionary. -/
theorem roughFamily_mass_dictionary {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high : Bool) :
    (roughFamily N δ Δ V p high).mass =
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ∑ t ∈ primeTuples N (wuLocalCutoff N δ d p.S)
        (wuLocalCutoff N δ d p.kappa1) (wuLocalCutoff N δ d p.kappa2)
        (wuLocalCutoff N δ d p.kappa3) (wuLocalCutoff N δ d p.s) (word high),
        (((roughNumbers ((N : ℝ)/tupleProduct d t) t.2.1).erase 1).card : ℝ) := by
  let W := convolutionWuWindows N Δ V
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun _ h => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) h
  have hh := actualFamily_test_dictionary (N := N) (δ := δ) p W high hd
    (fun x _ => if profileRough x then (convolutionCoeff W x.1 : ℝ) else 0)
  have hm : (roughFamily N δ Δ V p high).mass =
      ∑ x ∈ actualProfiles N δ p W high, ∑ q ∈ actualRawFibre N δ p x,
        if profileRough x then (convolutionCoeff W x.1 : ℝ) else 0 := by
    rw [← hh]
    simp only [roughFamily, sourceFamily, LabelledPhysical.Family.mass,
      LabelledPhysical.Family.restrictLabels, sum_filter, sum_const, nsmul_eq_mul]
    apply sum_congr rfl
    intro x _
    by_cases hx : profileRough x <;> simp [hx, actualFamily, physicalFamily, LabelledPhysical.Family.primes, W, mul_comm]
  rw [hm]
  exact rough_profiles_dictionary N W _ _ _ _ _ _ hd

theorem high_tuple_length {N : ℕ} {a b c e f : ℝ} (high : Bool) {t : PrimeTuple}
    (ht : t ∈ primeTuples N a b c e f (word high)) :
    (tupleList t).length = if high then 6 else 5 := by
  have hh := tuple_length (cs := word high) (by
    cases high <;> simp [word, HighUnitSource.word20, HighUnitSource.word21]) ht
  cases high <;> simpa [word, HighUnitSource.word20, HighUnitSource.word21] using hh

end Wu2008DoubleSieve.HighNonunit
