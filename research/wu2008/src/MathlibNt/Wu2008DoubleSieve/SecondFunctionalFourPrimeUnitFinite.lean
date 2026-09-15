import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherCarriers
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitPayment

namespace Wu2008DoubleSieve
open Finset
open scoped Classical

noncomputable def secondFunctionalFourPrimeUnitCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  (secondFunctionalMotherPrefixCarrier N d l).filter fun ell => N - ell = d * l.prod

noncomputable def secondFunctionalFourPrimeNonunitCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  (secondFunctionalMotherPrefixCarrier N d l).filter fun ell => N - ell ≠ d * l.prod

theorem secondFunctionalFourPrimeUnit_partition (N d : ℕ) (l : List ℕ) :
    (secondFunctionalFourPrimeUnitCarrier N d l).card +
      (secondFunctionalFourPrimeNonunitCarrier N d l).card =
      (secondFunctionalMotherPrefixCarrier N d l).card := by
  exact Finset.card_filter_add_card_filter_not _

theorem secondFunctionalFourPrimeUnit_unique {N d ell ell' : ℕ} {l : List ℕ}
    (h : ell ∈ secondFunctionalFourPrimeUnitCarrier N d l)
    (h' : ell' ∈ secondFunctionalFourPrimeUnitCarrier N d l)
    (hle : ell ≤ N) (hle' : ell' ≤ N) : ell = ell' := by
  have he := (mem_filter.mp h).2
  have he' := (mem_filter.mp h').2
  omega


namespace FourPrimeUnit

/-- Only the four actual dictionary words, including 2233. -/
def word (j : Fin 4) : List ℕ :=
  match j with
  | ⟨0, _⟩ => [2,2,2,2]
  | ⟨1, _⟩ => [2,2,2,3]
  | ⟨2, _⟩ => [2,2,3,3]
  | ⟨3, _⟩ => [1,3,3,3]

theorem word_length (j : Fin 4) : (word j).length = 4 := by
  fin_cases j <;> rfl

theorem word_dictionary (j : Fin 4) :
    secondFunctionalMotherGammaWords (16 + j.val) = [word j] := by
  fin_cases j <;> rfl

theorem word_last (j : Fin 4) : (word j).getD 3 0 = 2 ∨ (word j).getD 3 0 = 3 := by
  fin_cases j <;> simp [word]

noncomputable def prefixTerm (unit : Bool) (N d : ℕ)
    (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow N a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e) = cs then
      (if unit then (secondFunctionalFourPrimeUnitCarrier N d l).card
        else (secondFunctionalFourPrimeNonunitCarrier N d l).card : ℕ) else 0

theorem prefix_partition (N d : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    prefixTerm true N d a b c e f cs + prefixTerm false N d a b c e f cs =
      secondFunctionalMotherPrefixTerm N d N a b c e f cs := by
  unfold prefixTerm secondFunctionalMotherPrefixTerm
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro l _
  by_cases h : l.map (secondFunctionalMotherColour b c e) = cs
  · simp only [h, if_true, Bool.false_eq_true, if_false]
    exact_mod_cast secondFunctionalFourPrimeUnit_partition N d l
  · simp [h]

theorem gamma_partition (N d : ℕ) (a b c e f : ℝ) (j : Fin 4) :
    prefixTerm true N d a b c e f (word j) +
      prefixTerm false N d a b c e f (word j) =
      secondFunctionalMotherGamma N d N a b c e f (16 + j.val) := by
  rw [prefix_partition]
  fin_cases j <;> simp [word, secondFunctionalMotherGamma, secondFunctionalMotherGammaWords]

/-- Restored source: M=N; no coprimality with d is added. -/
noncomputable def labels {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : Finset (Σ _ : ℕ, Σ _ : List ℕ, ℕ) :=
  (boxConvolutionSupport W).sigma fun d =>
    ((secondFunctionalMotherTuples (primeWindow N (a d) (f d)) cs.length).filter
      fun l => l.map (secondFunctionalMotherColour (b d) (c d) (e d)) = cs).sigma
      (secondFunctionalFourPrimeUnitCarrier N d)

def encode (x : Σ _ : ℕ, Σ _ : List ℕ, ℕ) : Σ _ : Gamma16Profile, ℕ :=
  ⟨⟨x.1, x.2.1.getD 2 0, x.2.1.getD 1 0, x.2.1.getD 0 0, 1⟩,
    x.2.1.getD 3 0⟩

theorem carrier_le {N d ell : ℕ} {l : List ℕ}
    (h : ell ∈ secondFunctionalFourPrimeUnitCarrier N d l) : ell ≤ N := by
  have h' := (mem_filter.mp (mem_filter.mp h).1).1
  exact Nat.le_of_lt_succ (mem_range.mp h')

theorem encode_injOn {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} (hlen : cs.length = 4) :
    Set.InjOn encode (labels N W a b c e f cs) := by
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
  have heq := secondFunctionalFourPrimeUnit_unique hell hell' (carrier_le hell) (carrier_le hell')
  change ell = ell' at heq
  subst ell'
  rfl

/-- First three original half-open windows; no strengthened profile screen. -/
noncomputable def profiles {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : Finset Gamma16Profile :=
  (boxConvolutionSupport W).sigma fun d =>
    (primeWindow N (a d) (f d)).sigma fun p3 =>
    (primeWindow N (a d) (f d)).sigma fun p2 =>
    (primeWindow N (a d) (f d)).sigma fun p1 =>
    ({1} : Finset ℕ).filter fun n => p1 < p2 ∧ p2 < p3 ∧
      [p1,p2,p3].map (secondFunctionalMotherColour (b d) (c d) (e d)) = cs.take 3 ∧
      gamma16Cofactor ⟨d,p3,p2,p1,n⟩ * p3 ≤ N

/-- Prime-only closed last band: no output-prime or coprimality screen. -/
noncomputable def fibre (N : ℕ) (c e f : ℕ → ℝ) (cs : List ℕ)
    (x : Gamma16Profile) : Finset ℕ :=
  (range (N+1)).filter fun p => p.Prime ∧ x.2.1 < p ∧
    (if cs.getD 3 0 = 2 then c x.1 else e x.1) ≤ (p : ℝ) ∧
    (p : ℝ) ≤ (if cs.getD 3 0 = 2 then e x.1 else f x.1) ∧
    gamma16Cofactor x * p ≤ N

theorem mem_profiles {i N d p1 p2 p3 n : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} :
    (⟨d,p3,p2,p1,n⟩ : Gamma16Profile) ∈ profiles N W a b c e f cs ↔
    d ∈ boxConvolutionSupport W ∧ p3 ∈ primeWindow N (a d) (f d) ∧
    p2 ∈ primeWindow N (a d) (f d) ∧ p1 ∈ primeWindow N (a d) (f d) ∧
    n = 1 ∧ p1 < p2 ∧ p2 < p3 ∧
    [p1,p2,p3].map (secondFunctionalMotherColour (b d) (c d) (e d)) = cs.take 3 ∧
    gamma16Cofactor ⟨d,p3,p2,p1,n⟩ * p3 ≤ N := by
  simp only [profiles, mem_sigma, mem_filter, mem_singleton]

theorem inclusion {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (j : Fin 4) :
    (labels N W a b c e f (word j)).image encode ⊆
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
  have hprod : gamma16Cofactor ⟨d,p3,p2,p1,1⟩ * p4 = N-ell := by
    have heq := (mem_filter.mp hell).2
    simpa [gamma16Cofactor, mul_assoc] using heq.symm
  have hcap : gamma16Cofactor ⟨d,p3,p2,p1,1⟩ * p4 ≤ N := by
    rw [hprod]
    exact Nat.sub_le _ _
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
  refine ⟨mem_profiles.mpr ⟨hd,h3,h2,h1,rfl,ho.1,ho.2.1,hpref,?_⟩, ?_⟩
  · exact (Nat.mul_le_mul_left _ ho.2.2.le).trans hcap
  · apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, (mem_primeWindow.mp h4).1, ho.2.2, hlower,hupper,hcap⟩
    have hco : 0 < gamma16Cofactor ⟨d,p3,p2,p1,1⟩ := by
      simp only [gamma16Cofactor, mul_one]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hdpos d hd)
        (mem_primeWindow.mp h1).1.pos) (mem_primeWindow.mp h2).1.pos)
        (mem_primeWindow.mp h3).1.pos
    exact Nat.lt_succ_of_le ((Nat.le_mul_of_pos_left _ hco).trans hcap)


/-- The coefficient is attached to each original label, without quotienting products. -/
noncomputable def source {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    prefixTerm true N d (a d) (b d) (c d) (e d) (f d) cs

noncomputable def envelope {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : ℝ :=
  ∑ x ∈ profiles N W a b c e f cs,
    (convolutionCoeff W x.1 : ℝ) * (fibre N c e f cs x).card

theorem source_labels {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) :
    source N W a b c e f cs =
      ∑ x ∈ labels N W a b c e f cs, (convolutionCoeff W x.1 : ℝ) := by
  simp only [source, labels, sum_sigma]
  simp only [prefixTerm, sum_const, nsmul_eq_mul, if_true, sum_filter, mul_sum]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro l _
  split_ifs <;> ring

theorem source_le_envelope {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (j : Fin 4) : source N W a b c e f (word j) ≤ envelope N W a b c e f (word j) := by
  rw [source_labels]
  calc
    _ = ∑ y ∈ (labels N W a b c e f (word j)).image encode,
        (convolutionCoeff W y.1.1 : ℝ) := by
      rw [sum_image (encode_injOn (word_length j))]
      rfl
    _ ≤ ∑ y ∈ (profiles N W a b c e f (word j)).sigma (fibre N c e f (word j)),
        (convolutionCoeff W y.1.1 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (inclusion hdpos j) (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by
      simp only [sum_sigma, sum_const, nsmul_eq_mul, envelope]
      apply sum_congr rfl
      intro x _
      ring

theorem profiles_unit {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} {x : Gamma16Profile}
    (hx : x ∈ profiles N W a b c e f cs) : x.2.2.2.2 = 1 := by
  rcases x with ⟨d,p3,p2,p1,n⟩
  exact (mem_profiles.mp hx).2.2.2.2.1

theorem profiles_filter {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) :
    (profiles N W a b c e f cs).filter (fun x => x.2.2.2.2 = 1) =
      profiles N W a b c e f cs := filter_eq_self.mpr (fun _ hx => profiles_unit hx)

theorem profiles_geometry {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} {x : Gamma16Profile}
    (hx : x ∈ profiles N W a b c e f cs) :
    x.1 ∈ boxConvolutionSupport W ∧
    (0 < x.2.1 ∧ (x.2.1 : ℝ) ≤ f x.1) ∧
    (0 < x.2.2.1 ∧ (x.2.2.1 : ℝ) ≤ f x.1) ∧
    (0 < x.2.2.2.1 ∧ (x.2.2.2.1 : ℝ) ≤ f x.1) := by
  rcases x with ⟨d,p3,p2,p1,n⟩
  obtain ⟨hd,h3,h2,h1,_⟩ := mem_profiles.mp hx
  exact ⟨hd, ⟨(mem_primeWindow.mp h3).1.pos, (mem_primeWindow.mp h3).2.2.2.le⟩,
    ⟨(mem_primeWindow.mp h2).1.pos, (mem_primeWindow.mp h2).2.2.2.le⟩,
    ⟨(mem_primeWindow.mp h1).1.pos, (mem_primeWindow.mp h1).2.2.2.le⟩⟩

theorem fibre_geometry {N : ℕ} {c e f : ℕ → ℝ} {cs : List ℕ}
    {x : Gamma16Profile} {p : ℕ} (hef : e x.1 ≤ f x.1)
    (hp : p ∈ fibre N c e f cs x) : 0 < p ∧ (p : ℝ) ≤ f x.1 := by
  obtain ⟨_,hprime,_,_,hhi,_⟩ := mem_filter.mp hp
  refine ⟨hprime.pos, ?_⟩
  split_ifs at hhi
  · exact hhi.trans hef
  · exact hhi

theorem envelope_nonneg {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : 0 ≤ envelope N W a b c e f cs :=
  sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem source_nonneg {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : 0 ≤ source N W a b c e f cs := by
  rw [source_labels]
  exact sum_nonneg fun _ _ => Nat.cast_nonneg _

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
      (p : ℝ) = f x.1 ∧ gamma16Cofactor x * p ≤ N := by
  simp only [fibre, mem_filter, mem_range, Nat.lt_succ_iff, hlast,
    show (3 : ℕ) ≠ 2 by omega, if_false, hef]
  constructor
  · rintro ⟨hp,hpr,ho,hlo,hhi,hcap⟩
    exact ⟨hp,hpr,ho,le_antisymm hhi hlo,hcap⟩
  · rintro ⟨hp,hpr,ho,he,hcap⟩
    exact ⟨hp,hpr,ho,he.ge,he.le,hcap⟩

theorem source_zero_width {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {j : Fin 4}
    (hlast : (word j).getD 3 0 = 3) (hef : ∀ d, e d = f d) :
    source N W a b c e f (word j) = 0 := by
  rw [source_labels]
  have he : labels N W a b c e f (word j) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨d,l,ell⟩ hx
    obtain ⟨_, hx⟩ := mem_sigma.mp hx
    obtain ⟨hl,_⟩ := mem_sigma.mp hx
    obtain ⟨htup,hcol⟩ := mem_filter.mp hl
    obtain ⟨hlen,_,hm⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp htup
    rw [word_length] at hlen
    obtain ⟨p,q,r,t,rfl⟩ := List.length_eq_four.mp hlen
    have ht := (mem_primeWindow.mp (hm t (by simp))).2.2.2
    have hc : secondFunctionalMotherColour (b d) (c d) (e d) t = 3 := by
      have heq := congrArg (fun l : List ℕ => l.getD 3 0) hcol
      exact heq.trans hlast
    unfold secondFunctionalMotherColour at hc
    rw [hef d] at hc
    simp [ht] at hc
    split_ifs at hc <;> omega
  rw [he, sum_empty]

end FourPrimeUnit

end Wu2008DoubleSieve
