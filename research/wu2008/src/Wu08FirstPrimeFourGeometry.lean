import MathlibNt.Wu2008DoubleSieve.LastPrimeFourPhysicalMap
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKGoldbachRectangle

noncomputable section
open Finset Real
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace Wu08FirstPrimeFour

abbrev Long := ℕ × ℕ × ℕ × ℕ
abbrev Physical := TruncatedFourPhysical.Label

def longProduct (t : Long) : ℕ := t.1*t.2.1*t.2.2.1*t.2.2.2
def longPart (x : Physical) : Long := (x.1.2.1,x.1.2.2.1,x.1.2.2.2,x.2)
def shortPart (x : Physical) : ℕ := x.1.1
def firstSwitch (x : Physical) : Long × ℕ := (longPart x,shortPart x)

/-- The short variable is now a=p1; the rough n remains in the long coefficient. -/
theorem firstSwitch_injective : Function.Injective firstSwitch := by
  rintro ⟨⟨a,b,c,d⟩,n⟩ ⟨⟨a',b',c',d'⟩,n'⟩ h
  have hlong := congrArg Prod.fst h
  have ha := congrArg Prod.snd h
  have hb := congrArg Prod.fst hlong
  have hc := congrArg (fun t : Long => t.2.1) hlong
  have hd := congrArg (fun t : Long => t.2.2.1) hlong
  have hn := congrArg (fun t : Long => t.2.2.2) hlong
  dsimp only [firstSwitch,longPart,shortPart] at ha hb hc hd hn
  subst a'; subst b'; subst c'; subst d'; subst n'
  rfl

theorem firstProduct (x : Physical) :
    longProduct (longPart x)*shortPart x = fourModulusProduct x.1*x.2 := by
  rcases x with ⟨⟨a,b,c,d⟩,n⟩
  simp only [longProduct,longPart,shortPart,fourModulusProduct]
  ring

/-- Independent of the first prime, output primality, and the AP modulus.
No rough cofactor is assumed prime or squarefree. -/
def longLabels (N : ℕ) (e : Bool) : Finset Long :=
  ((range (N+1)) ×ˢ (range (N+1)) ×ˢ (range (N+1)) ×ˢ (range (N+1))).filter
    fun t => t.1.Prime ∧ t.1.Coprime N ∧
      t.2.1.Prime ∧ t.2.1.Coprime N ∧ t.2.2.1.Prime ∧ t.2.2.1.Coprime N ∧
      t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ (t.2.1 : ℝ) < LastPrimeFour.w N ∧
      (e = true → LastPrimeFour.w N ≤ t.2.2.1) ∧
      (t.2.2.1 : ℝ) < (if e then LastPrimeFour.v N / t.2.1 else LastPrimeFour.w N) ∧
      1 < t.2.2.2 ∧ LiLiuPrereqBuchstab.Rough (t.1 : ℝ) t.2.2.2

theorem longLabels_positive {N : ℕ} {e : Bool} {t : Long}
    (ht : t ∈ longLabels N e) :
    0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 := by
  obtain ⟨_,hb,_,hc,_,hd,_,_,_,_,_,_,hn,_⟩ := mem_filter.mp ht
  exact ⟨hb.pos,hc.pos,hd.pos,by omega⟩

theorem original_long_mem {N : ℕ} {e : Bool} {x : Physical}
    (hx : x ∈ LastPrimeFour.original N e) : longPart x ∈ longLabels N e := by
  rcases x with ⟨⟨a,b,c,d⟩,n⟩
  obtain ⟨ha,_,_,hb,hbN,hc,hcN,hab,hbc,hcw,hn,hr,hd,hdN,hcd,hwd,hcap,hs,_⟩ :=
    LastPrimeFour.original_data hx
  have hprod : b*c*d*n*a < N := by
    change a*b*c*n*d < N at hs
    nlinarith only [hs]
  have hbpos := hb.pos
  have hcpos := hc.pos
  have hdpos := hd.pos
  have hnpos : 0 < n := by omega
  have hm : 0 < b*c*d*n := by positivity
  have hmN : b*c*d*n ≤ N := (Nat.le_mul_of_pos_right _ ha.pos).trans hprod.le
  have hbN' : b ≤ N := (Nat.le_mul_of_pos_right _ (show 0 < c*d*n by positivity)).trans
    (by simpa only [Nat.mul_assoc] using hmN)
  have hcN' : c ≤ N := (Nat.le_mul_of_pos_right _ (show 0 < b*d*n by positivity)).trans
    (by nlinarith only [hmN])
  have hdN' : d ≤ N := (Nat.le_mul_of_pos_right _ (show 0 < b*c*n by positivity)).trans
    (by nlinarith only [hmN])
  have hnN : n ≤ N := (Nat.le_mul_of_pos_left _ (show 0 < b*c*d by positivity)).trans hmN
  apply mem_filter.mpr
  refine ⟨?_,hb,hbN,hc,hcN,hd,hdN,hbc,hcd,hcw,hwd,hcap,hn,hr⟩
  simp only [longPart,mem_product,mem_range]
  omega

def products (L : Finset Long) : Finset ℕ := L.image longProduct
def alpha (L : Finset Long) (m : ℕ) : ℝ := ((L.filter fun t => longProduct t=m).card : ℝ)

theorem alpha_nonneg (L : Finset Long) (m : ℕ) : 0 ≤ alpha L m := by
  unfold alpha
  positivity

/-- Signed regrouping retains all (b,c,d,n) fibres, including composite n. -/
theorem alpha_sum (L : Finset Long) (F : ℕ → ℝ) :
    (∑ t ∈ L, F (longProduct t)) = ∑ m ∈ products L, alpha L m*F m := by
  have h := sum_fiberwise_of_maps_to (s := L) (t := products L) (g := longProduct)
    (fun t ht => mem_image_of_mem _ ht) (fun t => F (longProduct t))
  rw [← h]
  apply sum_congr rfl
  intro m _
  calc
    _ = ∑ _t ∈ L.filter (fun t => longProduct t=m), F m := by
      apply sum_congr rfl
      intro t ht
      rw [(mem_filter.mp ht).2]
    _ = _ := by simp only [sum_const,nsmul_eq_mul,alpha]

/-- A fixed divisor order sufficient for the existing general C2 producer.
This does not use U8's two-prime coefficient or drop fibre multiplicity. -/
theorem alpha_order_eight (L : Finset Long)
    (hL : ∀ t ∈ L, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2) (m : ℕ) :
    |alpha L m| ≤ (fouvryTau 8 m : ℝ) := by
  rw [abs_of_nonneg (alpha_nonneg L m)]
  have hc : (L.filter (fun t => longProduct t=m)).card ≤
      (m.divisors ×ˢ m.divisors ×ˢ m.divisors).card := by
    apply card_le_card_of_injOn (fun t : Long => (t.1,t.2.1,t.2.2.1))
    · intro t ht
      obtain ⟨ht,he⟩ := mem_filter.mp ht
      obtain ⟨hb,hc,hd,hn⟩ := hL t ht
      have hm : m ≠ 0 := by rw [← he]; unfold longProduct; positivity
      have hbD : t.1 ∣ m := by
        rw [← he]
        exact (dvd_mul_right t.1 t.2.1).trans
          ((dvd_mul_right (t.1*t.2.1) t.2.2.1).trans (dvd_mul_right _ t.2.2.2))
      have hcD : t.2.1 ∣ m := by
        rw [← he]
        exact (dvd_mul_left t.2.1 t.1).trans
          ((dvd_mul_right (t.1*t.2.1) t.2.2.1).trans (dvd_mul_right _ t.2.2.2))
      have hdD : t.2.2.1 ∣ m := by
        rw [← he]
        exact (dvd_mul_left t.2.2.1 (t.1*t.2.1)).trans (dvd_mul_right _ t.2.2.2)
      exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hbD,hm⟩,
        mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hcD,hm⟩,Nat.mem_divisors.mpr ⟨hdD,hm⟩⟩⟩
    · rintro ⟨b,c,d,n⟩ hx ⟨b',c',d',n'⟩ hy h
      obtain ⟨hx,hxprod⟩ := mem_filter.mp hx
      obtain ⟨_,hyprod⟩ := mem_filter.mp hy
      have hb : b=b' := congrArg Prod.fst h
      have hc : c=c' := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
      have hd : d=d' := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
      subst b'; subst c'; subst d'
      have hp : 0 < b*c*d := by
        obtain ⟨hb,hc,hd,_⟩ := hL _ hx
        positivity
      have hn : n=n' := Nat.eq_of_mul_eq_mul_left hp (hxprod.trans hyprod.symm)
      subst n'
      rfl
  have hpow : m.divisors.card^3 ≤ fouvryTau 8 m := by
    by_cases hm : m=0
    · subst m; simp
    · simpa only [fouvryTau_two,show 2^3=8 by norm_num] using fouvryTau_pow_le 2 3 hm
  have hc' : (L.filter (fun t => longProduct t=m)).card ≤ m.divisors.card^3 := by
    simpa only [card_product,pow_succ,pow_zero,mul_one,one_mul,Nat.mul_assoc] using hc
  unfold alpha
  exact_mod_cast hc'.trans hpow

/-- An actual physical subfamily in an arbitrary first-prime rectangle. -/
def box (N : ℕ) (e : Bool) (L : Finset Long) (V : Finset ℕ) : Finset Physical :=
  (LastPrimeFour.original N e).filter fun x => longPart x ∈ L ∧ shortPart x ∈ V

def small (N : ℕ) (e : Bool) : Finset Physical :=
  (LastPrimeFour.original N e).filter fun x => (shortPart x : ℝ) ≤ (N : ℝ)^(1/10 : ℝ)
def large (N : ℕ) (e : Bool) : Finset Physical :=
  (LastPrimeFour.original N e).filter fun x => ¬(shortPart x : ℝ) ≤ (N : ℝ)^(1/10 : ℝ)

theorem original_card_split (N : ℕ) (e : Bool) :
    (small N e).card+(large N e).card = (LastPrimeFour.original N e).card :=
  card_filter_add_card_filter_not _

theorem box_maps {N : ℕ} {e : Bool} {L : Finset Long} {V : Finset ℕ} :
    Set.MapsTo firstSwitch (box N e L V) (L ×ˢ V) := by
  intro x hx
  exact (mem_filter.mp hx).2

end Wu08FirstPrimeFour
