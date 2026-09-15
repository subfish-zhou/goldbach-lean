import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitFinite
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceCore

namespace Wu2008DoubleSieve.HighNonunit
open Finset
open scoped Classical

/-- The whole initial list is retained, with the penultimate prime and residual quotient. -/
abbrev Profile := Σ _ : ℕ, Σ _ : List ℕ, ℕ × ℕ

def cofactor (x : Profile) : ℕ := x.1 * x.2.2.2 * (x.2.1 ++ [x.2.2.1]).prod

theorem take_penultimate (pre : List ℕ) (p q : ℕ) :
    (pre ++ [p,q]).take ((pre ++ [p,q]).length - 2) = pre := by simp

theorem get_penultimate (pre : List ℕ) (p q : ℕ) :
    (pre ++ [p,q]).getD ((pre ++ [p,q]).length - 2) 0 = p := by
  simp

/-- The original unscaled carrier for any prefix, with the original mask. -/
theorem prefix_carrier (N d : ℕ) (pre : List ℕ) (p q : ℕ) :
    secondFunctionalMotherPrefixCarrier N d (pre ++ [p,q]) =
      sourceSieveCarrier N (d * (pre ++ [p,q]).prod) (d * pre.prod * N) p := by
  simp only [secondFunctionalMotherPrefixCarrier, fourthRowMotherPrefixCarrier,
    take_penultimate, get_penultimate]

/-- Mask descent never deletes the N factor. -/
theorem carrier_mask {N d ell p q : ℕ} {pre : List ℕ}
    (h : ell ∈ secondFunctionalFourPrimeNonunitCarrier N d (pre ++ [p,q])) :
    Sifted (d * pre.prod * N) ((N-ell)/(d*(pre ++ [p,q]).prod)) p := by
  have hs := (mem_filter.mp h).1
  rw [prefix_carrier] at hs
  obtain ⟨_,_,hd,hz⟩ := mem_filter.mp hs
  rw [← Nat.mul_div_cancel' hd] at hz
  exact ((sifted_mul_iff _ _ _ _).mp hz).2

/-- Quotient conversion requires only the two last primes, not coprimality with N. -/
theorem prefix_quotient_carrier {N d p q : ℕ} (pre : List ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    secondFunctionalMotherPrefixCarrier N d (pre ++ [p,q]) =
      sieveCarrier N (d * (pre ++ [p,q]).prod) (d * pre.prod * N) p := by
  rw [prefix_carrier]
  simpa [List.prod_append, mul_assoc, mul_comm, mul_left_comm] using
    (source_strict_triple_carrier (N := N) (a := d*pre.prod) hp hq hpq)

/-- Structural decomposition has no prime enumeration or fixed arity. -/
theorem split_last_two {l : List ℕ} (h : 2 ≤ l.length) :
    ∃ pre p q, l = pre ++ [p,q] := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    cases l with
    | nil => simp at h
    | cons b t =>
      cases t with
      | nil => exact ⟨[],a,b,rfl⟩
      | cons c t =>
        obtain ⟨pre,p,q,he⟩ := ih (by simp)
        exact ⟨a :: pre,p,q,by simp [he]⟩

def encode (N : ℕ) (x : Σ _ : ℕ, Σ _ : List ℕ, ℕ) : Σ _ : Profile, ℕ :=
  ⟨⟨x.1, x.2.1.take (x.2.1.length-2),
    x.2.1.getD (x.2.1.length-2) 0, (N-x.2.2)/(x.1*x.2.1.prod)⟩,
    x.2.1.getD (x.2.1.length-1) 0⟩

theorem encode_append (N d ell p q : ℕ) (pre : List ℕ) :
    encode N ⟨d,pre ++ [p,q],ell⟩ =
      ⟨⟨d,pre,p,(N-ell)/(d*(pre ++ [p,q]).prod)⟩,q⟩ := by
  simp [encode]

theorem encode_injOn {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} (hlen : 2 ≤ cs.length) :
    Set.InjOn (encode N) (FourPrimeNonunit.labels N W a b c e f cs) := by
  rintro ⟨d,l,ell⟩ hx ⟨d',l',ell'⟩ hy he
  obtain ⟨_,⟨ht,_⟩,hell⟩ := FourPrimeNonunit.mem_labels.mp hx
  obtain ⟨_,⟨ht',_⟩,hell'⟩ := FourPrimeNonunit.mem_labels.mp hy
  have hl := ((secondFunctionalMother_tuple_mem _ _ _).mp ht).1
  have hl' := ((secondFunctionalMother_tuple_mem _ _ _).mp ht').1
  obtain ⟨pre,p,q,rfl⟩ := split_last_two (hl.symm ▸ hlen)
  obtain ⟨pre',p',q',rfl⟩ := split_last_two (hl'.symm ▸ hlen)
  simp only [encode_append] at he
  have hd : d = d' := congrArg (fun x : Σ _ : Profile, ℕ => x.1.1) he
  have hpre : pre = pre' := congrArg (fun x : Σ _ : Profile, ℕ => x.1.2.1) he
  have hp : p = p' := congrArg (fun x : Σ _ : Profile, ℕ => x.1.2.2.1) he
  have hq : q = q' := congrArg (fun x : Σ _ : Profile, ℕ => x.2) he
  subst d'; subst pre'; subst p'; subst q'
  have hn : (N-ell)/(d*(pre ++ [p,q]).prod) = (N-ell')/(d*(pre ++ [p,q]).prod) :=
    congrArg (fun x : Σ _ : Profile, ℕ => x.1.2.2.2) he
  obtain ⟨hle,_,hdv,_⟩ := FourPrimeNonunit.carrier_data hell
  obtain ⟨hle',_,hdv',_⟩ := FourPrimeNonunit.carrier_data hell'
  have hv := Nat.mul_div_cancel' hdv
  have hv' := Nat.mul_div_cancel' hdv'
  rw [hn] at hv
  have heq : ell = ell' := by omega
  subst ell'
  rfl

/-- Only prefix data, residual roughness and geometry occur here; no output-prime gate. -/
noncomputable def profiles {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : Finset Profile :=
  (boxConvolutionSupport W).sigma fun d =>
    (secondFunctionalMotherTuples (primeWindow N (a d) (f d)) (cs.length-2)).sigma fun pre =>
      ((primeWindow N (a d) (f d)).product (range (N+1))).filter fun pn =>
        2 ≤ pn.2 ∧ Sifted (d*pre.prod*N) pn.2 pn.1 ∧
        (pre ++ [pn.1]).Pairwise (· < ·) ∧
        (pre ++ [pn.1]).map (secondFunctionalMotherColour (b d) (c d) (e d)) =
          cs.take (cs.length-1) ∧ cofactor ⟨d,pre,pn⟩ * pn.1 ≤ N

/-- The last prime and complementary output prime are both tested in the closed fibre. -/
noncomputable def fibre (N : ℕ) (e f : ℕ → ℝ) (x : Profile) : Finset ℕ :=
  (range (N+1)).filter fun q => q.Prime ∧ x.2.2.1 < q ∧
    e x.1 ≤ (q : ℝ) ∧ (q : ℝ) ≤ f x.1 ∧
    cofactor x * q ≤ N ∧ (N-cofactor x*q).Prime

/-- All prime coordinates, not just their product, pass to the closed envelope. -/
theorem inclusion {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) (hcs : 2 ≤ cs.length)
    (hlast : cs.getD (cs.length-1) 0 = 3) :
    (FourPrimeNonunit.labels N W a b c e f cs).image (encode N) ⊆
      (profiles N W a b c e f cs).sigma (fibre N e f) := by
  intro y hy
  obtain ⟨⟨d,l,ell⟩,hx,rfl⟩ := mem_image.mp hy
  obtain ⟨hd,⟨ht,hcol⟩,hell⟩ := FourPrimeNonunit.mem_labels.mp hx
  obtain ⟨hlen,hord,hm⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp ht
  obtain ⟨pre,p,q,rfl⟩ := split_last_two (hlen.symm ▸ hcs)
  rw [encode_append]
  have hp := hm p (by simp)
  have hq := hm q (by simp)
  have ho := List.pairwise_append.mp hord
  have hpq : p < q := by simpa using ho.2.1
  have hpreord := ho.1
  have hpreford : (pre ++ [p]).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hpreord, by simp, ?_⟩
    intro t ht u hu
    have hu' : u = p := by simpa using hu
    subst u
    exact ho.2.2 t ht p (by simp)
  have hpre : pre ∈ secondFunctionalMotherTuples (primeWindow N (a d) (f d))
      (cs.length-2) := by
    apply (secondFunctionalMother_tuple_mem _ _ _).mpr
    refine ⟨by simp [← hlen], hpreord, ?_⟩
    intro t ht
    exact hm t (List.mem_append_left _ ht)
  have hprefixcol : (pre ++ [p]).map (secondFunctionalMotherColour (b d) (c d) (e d)) =
      cs.take (cs.length-1) := by
    rw [← hcol]
    simp [List.take_append]
  have hqcol : secondFunctionalMotherColour (b d) (c d) (e d) q = 3 := by
    rw [← hcol] at hlast
    simpa using hlast
  have hprodpos : 0 < (pre ++ [p,q]).prod := by
    apply List.prod_pos
    intro t ht
    exact (mem_primeWindow.mp (hm t ht)).1.pos
  have hmpos : 0 < d * (pre ++ [p,q]).prod := Nat.mul_pos (hdpos d hd) hprodpos
  let n := (N-ell)/(d*(pre ++ [p,q]).prod)
  obtain ⟨hn2,hnN,hprod0,_⟩ := FourPrimeNonunit.carrier_quotient hN he hmpos hell
  have hprod : cofactor ⟨d,pre,p,n⟩ * q = N-ell := by
    simpa [cofactor, n, List.prod_append, mul_assoc, mul_left_comm, mul_comm] using hprod0
  have hcap : cofactor ⟨d,pre,p,n⟩ * q ≤ N := hprod.le.trans (Nat.sub_le _ _)
  have hout : (N-cofactor ⟨d,pre,p,n⟩*q).Prime := by
    rw [hprod, Nat.sub_sub_self (FourPrimeNonunit.carrier_data hell).1]
    exact (FourPrimeNonunit.carrier_data hell).2.1
  have hco : 0 < cofactor ⟨d,pre,p,n⟩ := by
    have hdiff : 0 < N-ell := by
      have hlt := omega3_prime_output_lt hN he (FourPrimeNonunit.carrier_data hell).2.1
        (FourPrimeNonunit.carrier_data hell).1
      omega
    exact Nat.pos_of_mul_pos_right (hprod.symm ▸ hdiff)
  apply mem_sigma.mpr
  constructor
  · apply mem_sigma.mpr
    refine ⟨hd,mem_sigma.mpr ⟨hpre,mem_filter.mpr ⟨?_,hn2,carrier_mask hell,
      hpreford,hprefixcol,?_⟩⟩⟩
    · exact mem_product.mpr ⟨hp,mem_range.mpr (Nat.lt_succ_of_le hnN)⟩
    · exact (Nat.mul_le_mul_left _ hpq.le).trans hcap
  · apply mem_filter.mpr
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_mul_of_pos_left _ hco).trans hcap)),
      (mem_primeWindow.mp hq).1,hpq,HighUnitSource.colour_three hqcol,
      (mem_primeWindow.mp hq).2.2.2.le,hcap,hout⟩

/-- The strict source-window cap is enlarged only by inclusion. -/
theorem strict_fibre_subset (N : ℕ) (e f : ℕ → ℝ) (x : Profile) :
    (fibre N e f x).filter (fun q : ℕ => (q : ℝ) < f x.1) ⊆ fibre N e f x :=
  filter_subset _ _

/-- The closed cap is its strict part plus the retained endpoint atom. -/
theorem fibre_atom_partition (N : ℕ) (e f : ℕ → ℝ) (x : Profile) :
    ((fibre N e f x).filter (fun q : ℕ => (q : ℝ) < f x.1)).card +
      ((fibre N e f x).filter (fun q : ℕ => (q : ℝ) = f x.1)).card =
      (fibre N e f x).card := by
  have hatom : (fibre N e f x).filter (fun q : ℕ => (q : ℝ) = f x.1) =
      (fibre N e f x).filter (fun q : ℕ => ¬(q : ℝ) < f x.1) := by
    ext q
    simp only [mem_filter]
    constructor
    · rintro ⟨hq,h⟩
      exact ⟨hq, by rw [h]; exact lt_irrefl _⟩
    · rintro ⟨hq,h⟩
      exact ⟨hq, le_antisymm (mem_filter.mp hq).2.2.2.2.1 (le_of_not_gt h)⟩
  rw [hatom]
  exact card_filter_add_card_filter_not _

/-- A zero-width closed fibre is the endpoint atom, not the empty set. -/
theorem fibre_zero_width {N : ℕ} {e f : ℕ → ℝ} {x : Profile}
    (hef : e x.1 = f x.1) (q : ℕ) :
    q ∈ fibre N e f x ↔ q ≤ N ∧ q.Prime ∧ x.2.2.1 < q ∧
      (q : ℝ) = f x.1 ∧ cofactor x*q ≤ N ∧ (N-cofactor x*q).Prime := by
  simp only [fibre, mem_filter, mem_range, Nat.lt_succ_iff, hef]
  constructor
  · rintro ⟨hq,hpr,ho,hlo,hhi,hcap⟩
    exact ⟨hq,hpr,ho,le_antisymm hhi hlo,hcap⟩
  · rintro ⟨hq,hpr,ho,h,hcap⟩
    exact ⟨hq,hpr,ho,h.ge,h.le,hcap⟩

end Wu2008DoubleSieve.HighNonunit
