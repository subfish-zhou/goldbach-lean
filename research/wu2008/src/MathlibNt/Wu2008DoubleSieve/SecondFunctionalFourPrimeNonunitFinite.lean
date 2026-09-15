import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitCore

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset
open scoped Classical
open FourPrimeUnit (word word_length word_last)

/-- Restored source: M=N; no coprimality with d is added. -/
noncomputable def labels {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : Finset (Σ _ : ℕ, Σ _ : List ℕ, ℕ) :=
  (boxConvolutionSupport W).sigma fun d =>
    ((secondFunctionalMotherTuples (primeWindow N (a d) (f d)) cs.length).filter
      fun l => l.map (secondFunctionalMotherColour (b d) (c d) (e d)) = cs).sigma
      (secondFunctionalFourPrimeNonunitCarrier N d)

def encode (N : ℕ) (x : Σ _ : ℕ, Σ _ : List ℕ, ℕ) : Σ _ : Gamma16Profile, ℕ :=
  ⟨⟨x.1, x.2.1.getD 2 0, x.2.1.getD 1 0, x.2.1.getD 0 0, (N-x.2.2)/(x.1*x.2.1.prod)⟩,
    x.2.1.getD 3 0⟩

theorem carrier_le {N d ell : ℕ} {l : List ℕ}
    (h : ell ∈ secondFunctionalFourPrimeNonunitCarrier N d l) : ell ≤ N := by
  have h' := (mem_filter.mp (mem_filter.mp h).1).1
  exact Nat.le_of_lt_succ (mem_range.mp h')

theorem encode_injOn {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} (hlen : cs.length = 4) :
    Set.InjOn (encode N) (labels N W a b c e f cs) := by
  rintro ⟨d,l,ell⟩ hx ⟨d',l',ell'⟩ hy he
  obtain ⟨_, hx⟩ := mem_sigma.mp hx
  obtain ⟨hl, hell⟩ := mem_sigma.mp hx
  obtain ⟨_, hy⟩ := mem_sigma.mp hy
  obtain ⟨hl', hell'⟩ := mem_sigma.mp hy
  have len := ((secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl).1).1
  have len' := ((secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl').1).1
  rw [hlen] at len len'
  obtain ⟨p,q,r,t,rfl⟩ := List.length_eq_four.mp len
  obtain ⟨p',q',r',t',rfl⟩ := List.length_eq_four.mp len'
  have hd : d = d' := congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.1.1) he
  have hp : p = p' := congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.1.2.2.2.1) he
  have hq : q = q' := congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.1.2.2.1) he
  have hr : r = r' := congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.1.2.1) he
  have ht : t = t' := congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.2) he
  subst d'; subst p'; subst q'; subst r'; subst t'
  have hn : (N-ell)/(d*[p,q,r,t].prod) = (N-ell')/(d*[p,q,r,t].prod) :=
    congrArg (fun x : Σ _ : Gamma16Profile, ℕ => x.1.2.2.2.2) he
  obtain ⟨hle,_,hdv,_⟩ := carrier_data hell
  obtain ⟨hle',_,hdv',_⟩ := carrier_data hell'
  dsimp only at hle hle' hdv hdv'
  have hv := Nat.mul_div_cancel' hdv
  have hv' := Nat.mul_div_cancel' hdv'
  rw [hn] at hv
  have heq : ell = ell' := by omega
  subst ell'

  rfl

/-- Finite nonunit profiles retaining the original excluded-prime mask. -/
noncomputable def profiles {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : Finset Gamma16Profile :=
  (boxConvolutionSupport W).sigma fun d =>
    (primeWindow N (a d) (f d)).sigma fun p3 =>
    (primeWindow N (a d) (f d)).sigma fun p2 =>
    (primeWindow N (a d) (f d)).sigma fun p1 =>
    (range (N+1)).filter fun n => 2 ≤ n ∧
      Sifted (d*p1*p2*N) n p3 ∧ p1 < p2 ∧ p2 < p3 ∧
      [p1,p2,p3].map (secondFunctionalMotherColour (b d) (c d) (e d)) = cs.take 3 ∧
      gamma16Cofactor ⟨d,p3,p2,p1,n⟩ * p3 ≤ N

/-- Closed last-prime band with the genuine output-prime test. -/
noncomputable def fibre (N : ℕ) (c e f : ℕ → ℝ) (cs : List ℕ)
    (x : Gamma16Profile) : Finset ℕ :=
  (range (N+1)).filter fun p => p.Prime ∧ x.2.1 < p ∧
    (if cs.getD 3 0 = 2 then c x.1 else e x.1) ≤ (p : ℝ) ∧
    (p : ℝ) ≤ (if cs.getD 3 0 = 2 then e x.1 else f x.1) ∧
    gamma16Cofactor x * p ≤ N ∧ (N-gamma16Cofactor x*p).Prime

theorem mem_profiles {i N d p1 p2 p3 n : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} :
    (⟨d,p3,p2,p1,n⟩ : Gamma16Profile) ∈ profiles N W a b c e f cs ↔
    d ∈ boxConvolutionSupport W ∧ p3 ∈ primeWindow N (a d) (f d) ∧
    p2 ∈ primeWindow N (a d) (f d) ∧ p1 ∈ primeWindow N (a d) (f d) ∧
    n < N+1 ∧ 2 ≤ n ∧ Sifted (d*p1*p2*N) n p3 ∧ p1 < p2 ∧ p2 < p3 ∧
    [p1,p2,p3].map (secondFunctionalMotherColour (b d) (c d) (e d)) = cs.take 3 ∧
    gamma16Cofactor ⟨d,p3,p2,p1,n⟩ * p3 ≤ N := by
  simp only [profiles, mem_sigma, mem_filter, mem_range]

theorem inclusion {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (heven : Even N) (j : Fin 4) :
    (labels N W a b c e f (word j)).image (encode N) ⊆
      (profiles N W a b c e f (word j)).sigma (fibre N c e f (word j)) := by
  intro y hy
  obtain ⟨⟨d,l,ell⟩, hx, rfl⟩ := mem_image.mp hy
  obtain ⟨hd, hx⟩ := mem_sigma.mp hx
  obtain ⟨hl, hell⟩ := mem_sigma.mp hx
  obtain ⟨htup,hcol⟩ := mem_filter.mp hl
  obtain ⟨hlen,hord,hm⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp htup
  rw [word_length] at hlen
  obtain ⟨p1,p2,p3,p4,rfl⟩ := List.length_eq_four.mp hlen
  have h1 := hm p1 (by simp)
  have h2 := hm p2 (by simp)
  have h3 := hm p3 (by simp)
  have h4 := hm p4 (by simp)
  have ho : p1 < p2 ∧ p2 < p3 ∧ p3 < p4 := by
    simp [List.pairwise_cons] at hord
    exact ⟨hord.1.1, hord.2.1.1, hord.2.2⟩
  let n := (N-ell)/(d*[p1,p2,p3,p4].prod)
  have hmpos : 0 < d * [p1,p2,p3,p4].prod := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_pos (hdpos d hd) (Nat.mul_pos (mem_primeWindow.mp h1).1.pos
      (Nat.mul_pos (mem_primeWindow.mp h2).1.pos
        (Nat.mul_pos (mem_primeWindow.mp h3).1.pos (mem_primeWindow.mp h4).1.pos)))
  obtain ⟨hn2,hnN,hprod0,hrecover⟩ := carrier_quotient hN heven hmpos hell
  have hprod : gamma16Cofactor ⟨d,p3,p2,p1,n⟩ * p4 = N-ell := by
    simpa [gamma16Cofactor, n, mul_assoc, mul_left_comm, mul_comm] using hprod0
  have hcap : gamma16Cofactor ⟨d,p3,p2,p1,n⟩ * p4 ≤ N := by
    rw [hprod]
    exact Nat.sub_le _ _
  have hout : (N-gamma16Cofactor ⟨d,p3,p2,p1,n⟩*p4).Prime := by
    rw [hprod, Nat.sub_sub_self (carrier_data hell).1]
    exact (carrier_data hell).2.1
  have hmask : Sifted (d*p1*p2*N) n p3 := carrier_mask hell
  have hpref : [p1,p2,p3].map (secondFunctionalMotherColour (b d) (c d) (e d)) =
      (word j).take 3 := by
    rw [← hcol]
    rfl
  have hlast : secondFunctionalMotherColour (b d) (c d) (e d) p4 =
      (word j).getD 3 0 := by rw [← hcol]; rfl
  have hlower : (if (word j).getD 3 0 = 2 then c d else e d) ≤ (p4 : ℝ) := by
    rcases word_last j with h | h <;> rw [h] at hlast ⊢
    · simp only [if_true]
      unfold secondFunctionalMotherColour at hlast
      split_ifs at hlast <;> first | omega | linarith
    · simp only [show (3 : ℕ) ≠ 2 by omega, if_false]
      unfold secondFunctionalMotherColour at hlast
      split_ifs at hlast <;> first | omega | linarith
  have hupper : (p4 : ℝ) ≤ (if (word j).getD 3 0 = 2 then e d else f d) := by
    split_ifs with hh
    · rw [hh] at hlast
      unfold secondFunctionalMotherColour at hlast
      split_ifs at hlast <;> first | omega | linarith
    · exact (mem_primeWindow.mp h4).2.2.2.le
  apply mem_sigma.mpr
  refine ⟨mem_profiles.mpr ⟨hd,h3,h2,h1,Nat.lt_succ_of_le hnN,hn2,hmask,ho.1,ho.2.1,hpref,?_⟩, ?_⟩
  · exact (Nat.mul_le_mul_left _ ho.2.2.le).trans hcap
  · apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, (mem_primeWindow.mp h4).1, ho.2.2, hlower,hupper,hcap,hout⟩
    have hco : 0 < gamma16Cofactor ⟨d,p3,p2,p1,n⟩ := by
      change 0 < d*n*p1*p2*p3
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hdpos d hd) (lt_of_lt_of_le (by decide : 0 < 2) hn2))
        (mem_primeWindow.mp h1).1.pos) (mem_primeWindow.mp h2).1.pos)
        (mem_primeWindow.mp h3).1.pos
    exact Nat.lt_succ_of_le ((Nat.le_mul_of_pos_left _ hco).trans hcap)



/-- The coefficient is attached to each original label, without quotienting products. -/
noncomputable def source {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    FourPrimeUnit.prefixTerm false N d (a d) (b d) (c d) (e d) (f d) cs

noncomputable def envelope {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : ℝ :=
  ∑ x ∈ profiles N W a b c e f cs,
    (convolutionCoeff W x.1 : ℝ) * (fibre N c e f cs x).card

theorem source_labels {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) :
    source N W a b c e f cs =
      ∑ x ∈ labels N W a b c e f cs, (convolutionCoeff W x.1 : ℝ) := by
  simp only [source, labels, sum_sigma]
  simp only [FourPrimeUnit.prefixTerm, sum_const, nsmul_eq_mul, Bool.false_eq_true, if_false, sum_filter, mul_sum]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro l _
  split_ifs <;> ring

theorem source_le_envelope {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (heven : Even N) (j : Fin 4) : source N W a b c e f (word j) ≤ envelope N W a b c e f (word j) := by
  rw [source_labels]
  calc
    _ = ∑ y ∈ (labels N W a b c e f (word j)).image (encode N),
        (convolutionCoeff W y.1.1 : ℝ) := by
      rw [sum_image (encode_injOn (word_length j))]
      rfl
    _ ≤ ∑ y ∈ (profiles N W a b c e f (word j)).sigma (fibre N c e f (word j)),
        (convolutionCoeff W y.1.1 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (inclusion hdpos hN heven j) (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by
      simp only [sum_sigma, sum_const, nsmul_eq_mul, envelope]
      apply sum_congr rfl
      intro x _
      ring


/-- The closed cap is partitioned into a strict part and its retained atom. -/
theorem fibre_atom_partition (N : ℕ) (c e f : ℕ → ℝ) (cs : List ℕ)
    (x : Gamma16Profile) :
    ((fibre N c e f cs x).filter (fun p : ℕ => (p : ℝ) <
      (if cs.getD 3 0 = 2 then e x.1 else f x.1))).card +
    ((fibre N c e f cs x).filter (fun p : ℕ => (p : ℝ) =
      (if cs.getD 3 0 = 2 then e x.1 else f x.1))).card =
    (fibre N c e f cs x).card := by
  have he : (fibre N c e f cs x).filter (fun p : ℕ => (p : ℝ) =
      (if cs.getD 3 0 = 2 then e x.1 else f x.1)) =
      (fibre N c e f cs x).filter (fun p : ℕ => ¬(p : ℝ) <
      (if cs.getD 3 0 = 2 then e x.1 else f x.1)) := by
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨hp,h⟩
      exact ⟨hp, by rw [h]; exact lt_irrefl _⟩
    · rintro ⟨hp,h⟩
      exact ⟨hp, le_antisymm (mem_filter.mp hp).2.2.2.2.1 (le_of_not_gt h)⟩
  rw [he]
  exact card_filter_add_card_filter_not _

/-- Even when e=f, a colour-three closed fibre retains precisely its cap atom. -/
theorem fibre_zero_width {N : ℕ} {c e f : ℕ → ℝ} {cs : List ℕ}
    {x : Gamma16Profile} (hlast : cs.getD 3 0 = 3) (hef : e x.1 = f x.1) (p : ℕ) :
    p ∈ fibre N c e f cs x ↔ p ≤ N ∧ p.Prime ∧ x.2.1 < p ∧
      (p : ℝ) = f x.1 ∧ gamma16Cofactor x * p ≤ N ∧
      (N-gamma16Cofactor x*p).Prime := by
  simp only [fibre, mem_filter, mem_range, Nat.lt_succ_iff, hlast,
    show (3 : ℕ) ≠ 2 by omega, if_false, hef]
  constructor
  · rintro ⟨hp,hpr,ho,hlo,hhi,hcap⟩
    exact ⟨hp,hpr,ho,le_antisymm hhi hlo,hcap⟩
  · rintro ⟨hp,hpr,ho,he,hcap⟩
    exact ⟨hp,hpr,ho,he.ge,he.le,hcap⟩

/-- Full literal source-label membership, including every colour and source screen. -/
theorem mem_labels {i N d ell : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs l : List ℕ} :
    (⟨d,l,ell⟩ : Σ _ : ℕ, Σ _ : List ℕ, ℕ) ∈ labels N W a b c e f cs ↔
      d ∈ boxConvolutionSupport W ∧
      (l ∈ secondFunctionalMotherTuples (primeWindow N (a d) (f d)) cs.length ∧
        l.map (secondFunctionalMotherColour (b d) (c d) (e d)) = cs) ∧
      ell ∈ secondFunctionalFourPrimeNonunitCarrier N d l := by
  simp only [labels, mem_sigma, mem_filter]

/-- No weights are changed by the label-preserving finite switch. -/
theorem sigma_labels_le {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) (j : Fin 4)
    (σ : ℕ → ℝ) (hσ : ∀ d, 0 ≤ σ d) :
    (∑ x ∈ labels N W a b c e f (word j), σ x.1) ≤
      ∑ x ∈ profiles N W a b c e f (word j), σ x.1 * (fibre N c e f (word j) x).card := by
  calc
    _ = ∑ y ∈ (labels N W a b c e f (word j)).image (encode N), σ y.1.1 := by
      rw [sum_image (encode_injOn (word_length j))]
      rfl
    _ ≤ ∑ y ∈ (profiles N W a b c e f (word j)).sigma (fibre N c e f (word j)), σ y.1.1 :=
      sum_le_sum_of_subset_of_nonneg (inclusion hdpos hN he j) (fun y _ _ => hσ y.1.1)
    _ = _ := by
      simp only [sum_sigma, sum_const, nsmul_eq_mul]
      apply sum_congr rfl
      intro x _
      ring

end Wu2008DoubleSieve.FourPrimeNonunit

