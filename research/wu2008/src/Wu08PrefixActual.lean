import Wu08PrefixSelberg

noncomputable section
open Finset Real
open scoped Classical
open Wu2008DoubleSieve
open U8Literal.SmallProduct U8Literal.SmallProduct.TwoDimensional
namespace Wu08FirstPrimeFour.Prefix

def product (x : Physical) : ℕ := fourModulusProduct x.1*x.2
def primes (x : Physical) : Fin 4 → ℕ := ![x.1.1,x.1.2.1,x.1.2.2.1,x.1.2.2.2]
def multiplicity : ℝ := (1/truncatedSixthLowerAlpha)^4

theorem product_data {N : ℕ} {e : Bool} {x : Physical}
    (hx : x ∈ LastPrimeFour.original N e) :
    0 < product x ∧ product x < N ∧ (N-product x).Prime ∧
      LiLiuPrereqBuchstab.Rough (LastPrimeFour.z N) (product x) := by
  rcases x with ⟨⟨a,b,c,d⟩,n⟩
  obtain ⟨ha,_,hza,hb,_,hc,_,hab,hbc,_,hn,hr,hd,_,hcd,_,_,hs,hout⟩ :=
    LastPrimeFour.original_data hx
  have hid : product ⟨(a,b,c,d),n⟩ = LastPrimeFour.cofactor (a,b,c,n)*d := by
    simp only [product,fourModulusProduct,LastPrimeFour.cofactor]
    ring
  have hp : 0 < product ⟨(a,b,c,d),n⟩ := by
    dsimp [product,fourModulusProduct]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos) hd.pos)
      (by omega)
  refine ⟨hp,hid ▸ hs,hid ▸ hout,?_⟩
  intro p hpp hpm
  have hzb : LastPrimeFour.z N ≤ (b : ℝ) := hza.trans (by exact_mod_cast hab.le)
  have hzc : LastPrimeFour.z N ≤ (c : ℝ) := hzb.trans (by exact_mod_cast hbc.le)
  have hzd : LastPrimeFour.z N ≤ (d : ℝ) := hzc.trans (by exact_mod_cast hcd.le)
  change p ∣ a*b*c*d*n at hpm
  rcases hpp.dvd_mul.mp hpm with hpm | hpn
  · rcases hpp.dvd_mul.mp hpm with hpm | hpd
    · rcases hpp.dvd_mul.mp hpm with hpm | hpc
      · rcases hpp.dvd_mul.mp hpm with hpa | hpb
        · exact (ha.eq_one_or_self_of_dvd p hpa |>.resolve_left hpp.ne_one).symm ▸ hza
        · exact (hb.eq_one_or_self_of_dvd p hpb |>.resolve_left hpp.ne_one).symm ▸ hzb
      · exact (hc.eq_one_or_self_of_dvd p hpc |>.resolve_left hpp.ne_one).symm ▸ hzc
    · exact (hd.eq_one_or_self_of_dvd p hpd |>.resolve_left hpp.ne_one).symm ▸ hzd
  · exact hzb.trans (hr p hpp hpn)

theorem product_prime_divisors {N : ℕ} {e : Bool} {x : Physical}
    (hx : x ∈ LastPrimeFour.original N e) : ∀ j : Fin 4,
    (primes x j).Prime ∧ primes x j ∣ product x ∧
      (N : ℝ)^truncatedSixthLowerAlpha ≤ primes x j := by
  rcases x with ⟨⟨a,b,c,d⟩,n⟩
  obtain ⟨ha,_,hza,hb,_,hc,_,hab,hbc,_,_,_,hd,_,hcd,_⟩ :=
    LastPrimeFour.original_data hx
  have hzb : (N : ℝ)^truncatedSixthLowerAlpha ≤ (b : ℝ) :=
    hza.trans (by exact_mod_cast hab.le)
  have hzc : (N : ℝ)^truncatedSixthLowerAlpha ≤ (c : ℝ) :=
    hzb.trans (by exact_mod_cast hbc.le)
  have hzd : (N : ℝ)^truncatedSixthLowerAlpha ≤ (d : ℝ) :=
    hzc.trans (by exact_mod_cast hcd.le)
  have hda : a ∣ a*b*c*d*n := dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right a b) c) d) n
  have hdb : b ∣ a*b*c*d*n := dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left b a) c) d) n
  have hdc : c ∣ a*b*c*d*n := dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_left c (a*b)) d) n
  have hdd : d ∣ a*b*c*d*n := dvd_mul_of_dvd_left (dvd_mul_left d (a*b*c)) n
  simp only [primes,Fin.forall_fin_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.forall_fin_zero,and_true,product,fourModulusProduct]
  exact ⟨⟨ha,hda,hza⟩,⟨hb,hdb,hzb⟩,⟨hc,hdc,hzc⟩,hd,hdd,hzd⟩

theorem primes_fibre_injective {N : ℕ} {e : Bool} (S : Finset Physical)
    (hS : S ⊆ LastPrimeFour.original N e) (m : ℕ) :
    Set.InjOn primes (S.filter fun x => product x=m) := by
  rintro ⟨⟨a,b,c,d⟩,n⟩ hx ⟨⟨a',b',c',d'⟩,n'⟩ hy h
  obtain ⟨hx,hmx⟩ := mem_filter.mp hx
  obtain ⟨_,hmy⟩ := mem_filter.mp hy
  have ha : a=a' := congrFun h 0
  have hb : b=b' := congrFun h 1
  have hc : c=c' := congrFun h 2
  have hd : d=d' := congrFun h 3
  subst a'; subst b'; subst c'; subst d'
  have hp : 0 < fourModulusProduct (a,b,c,d) :=
    Nat.pos_of_mul_pos_right (product_data (hS hx)).1
  have hn : n=n' := Nat.eq_of_mul_eq_mul_left hp (hmx.trans hmy.symm)
  subst n'
  rfl

/-- Uniform four-prime label multiplicity; the arbitrary rough residual is
recovered by multiplication cancellation, not assumed prime or squarefree. -/
theorem product_fibre_bound {N : ℕ} {e : Bool} (hN : 1 < N) (S : Finset Physical)
    (hS : S ⊆ LastPrimeFour.original N e) (m : ℕ) :
    ((S.filter fun x => product x=m).card : ℝ) ≤ multiplicity := by
  by_cases hh : (S.filter fun x => product x=m).Nonempty
  · obtain ⟨x,hx⟩ := hh
    obtain ⟨hx,hmx⟩ := mem_filter.mp hx
    have hd := product_data (hS hx)
    apply omega3_prime_labels_card_le _ primes (primes_fibre_injective S hS m) hN
      (hmx ▸ hd.1) (hmx ▸ hd.2.1.le)
      (by norm_num [truncatedSixthLowerAlpha])
    intro y hy j
    obtain ⟨hy,hmy⟩ := mem_filter.mp hy
    simpa only [← hmy] using product_prime_divisors (hS hy) j
  · rw [not_nonempty_iff_eq_empty.mp hh,card_empty,Nat.cast_zero]
    unfold multiplicity
    positivity

theorem smallPrefix_product_maps {N : ℕ} {e : Bool} {ξ Z : ℝ}
    (hZ : Z ≤ LastPrimeFour.z N) (hZo : Z ≤ (1-ξ)*N) :
    Set.MapsTo product (smallPrefix N e ξ) (siftedProducts N ξ Z) := by
  intro x hx
  obtain ⟨hx,hcut⟩ := mem_filter.mp hx
  obtain ⟨hx,_⟩ := mem_filter.mp hx
  have hd := product_data hx
  have hcut' : (product x : ℝ) ≤ ξ*N := by
    simpa only [product,firstProduct,not_lt] using hcut
  have hi : product x ∈ interval N ξ (1,1) := by
    apply mem_filter.mpr
    simpa only [Prod.fst,Prod.snd,one_mul] using
      And.intro (mem_range.mpr (by omega : product x < N+1))
        (And.intro (Nat.succ_le_of_lt hd.1) (And.intro hd.2.1 hcut'))
  apply mem_filter.mpr
  refine ⟨hi,?_⟩
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hp,hpZ⟩ := mem_sievePrimes.mp hp
  have hpm : ¬p ∣ product x := fun h =>
    (not_lt_of_ge (hd.2.2.2 p hp h)) (hpZ.trans_le hZ)
  have hpo : p < N-product x := by
    have hout : (1-ξ)*N ≤ (N-product x : ℕ) := by
      rw [Nat.cast_sub hd.2.1.le]
      nlinarith only [hcut']
    exact_mod_cast hpZ.trans_le (hZo.trans hout)
  have hc1 := (hp.coprime_iff_not_dvd.mpr hpm).symm
  have hc2 := Nat.coprime_of_lt_prime hp.ne_zero hpo hd.2.2.1
  simpa only [twoLinear,Prod.fst,Prod.snd,one_mul,id_eq] using hc1.mul_left hc2

/-- An actual finite prefix bound in the unchanged singular-series variable N.
Every original tuple is counted, including all strict order/product faces. -/
theorem smallPrefix_selberg_upper {N : ℕ} {e : Bool} (hN : 1 < N) (he : Even N)
    {ξ Z R : ℝ} (hξ : 0 ≤ ξ) (hR : 1 ≤ R)
    (hZ : Z ≤ LastPrimeFour.z N) (hZo : Z ≤ (1-ξ)*N) :
    ((smallPrefix N e ξ).card : ℝ) ≤ multiplicity *
      (ξ*N / denominator N Z R + 2*(R+1)^2*R^4) := by
  have hS : smallPrefix N e ξ ⊆ LastPrimeFour.original N e :=
    (filter_subset _ _).trans (filter_subset _ _)
  have hmaps := smallPrefix_product_maps (e := e) hZ hZo
  have hf := card_eq_sum_card_fiberwise hmaps
  have hmult : 0 ≤ multiplicity := by unfold multiplicity; positivity
  calc
    _ = ∑ m ∈ siftedProducts N ξ Z,
        (((smallPrefix N e ξ).filter fun x => product x=m).card : ℝ) := by
      rw [hf,Nat.cast_sum]
    _ ≤ ∑ _m ∈ siftedProducts N ξ Z, multiplicity :=
      sum_le_sum fun m _ => product_fibre_bound hN _ hS m
    _ = multiplicity * (siftedProducts N ξ Z).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (siftedProducts_upper N he hξ hR) hmult

#print axioms product_fibre_bound
#print axioms smallPrefix_selberg_upper
end Wu08FirstPrimeFour.Prefix
