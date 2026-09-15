import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleWeightedSource
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitActualFamily

namespace Wu2008DoubleSieve.LowerTripleGrouped
open Finset
open scoped Classical

abbrev Label := ℕ × ℕ × ℕ × ℕ
abbrev Source := Σ _ : ℕ, Σ _ : ℕ × ℕ × ℕ, ℕ

def cofactor (x : Label) : ℕ := x.1 * x.2.1 * x.2.2.1 * x.2.2.2
noncomputable def lower (lo : ℕ → ℝ) (x : Label) : ℝ := max x.2.2.1 (lo x.1 - 1)
noncomputable def upper (N : ℕ) (hi : ℕ → ℝ) (x : Label) : ℝ :=
  min (hi x.1) ((N : ℝ) / cofactor x)

noncomputable def labels {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a f lo hi : ℕ → ℝ) (pre : ℕ → ℕ → ℕ → Prop) : Finset Label :=
  ((boxConvolutionSupport W).sigma fun d =>
    (primeWindow N (a d) (f d)).product
      ((primeWindow N (a d) (f d)).product (range (N+1)))).image
        (fun x => (x.1, x.2)) |>.filter fun x =>
    x.2.1 < x.2.2.1 ∧ pre x.1 x.2.1 x.2.2.1 ∧ 0 < x.2.2.2 ∧
    Sifted (x.1*x.2.1*N) (cofactor x) x.2.2.1 ∧ lower lo x ≤ upper N hi x

variable {i N : ℕ} {W : Fin i → Finset ℕ} {a f lo hi : ℕ → ℝ}
  {pre : ℕ → ℕ → ℕ → Prop}

theorem mem_labels (x : Label) : x ∈ labels N W a f lo hi pre ↔
    x.1 ∈ boxConvolutionSupport W ∧ x.2.1 ∈ primeWindow N (a x.1) (f x.1) ∧
    x.2.2.1 ∈ primeWindow N (a x.1) (f x.1) ∧ x.2.2.2 < N+1 ∧
    x.2.1 < x.2.2.1 ∧ pre x.1 x.2.1 x.2.2.1 ∧ 0 < x.2.2.2 ∧
    Sifted (x.1*x.2.1*N) (cofactor x) x.2.2.1 ∧ lower lo x ≤ upper N hi x := by
  rcases x with ⟨d,p,q,n⟩
  simp [labels, mem_sigma, mem_product, and_assoc]

theorem cofactor_pos (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    {x : Label} (hx : x ∈ labels N W a f lo hi pre) : 0 < cofactor x := by
  obtain ⟨hxd,hp,hq,_,_,_,hn,_⟩ := (mem_labels x).mp hx
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hd _ hxd)
    (mem_primeWindow.mp hp).1.pos) (mem_primeWindow.mp hq).1.pos) hn

theorem physical_cap (x : Label) (hx : 0 < cofactor x) :
    (cofactor x : ℝ) * upper N hi x ≤ N := by
  have hxR : (0 : ℝ) < cofactor x := by exact_mod_cast hx
  exact (mul_comm _ _).trans_le ((le_div_iff₀ hxR).mp (min_le_right _ _))

noncomputable def family (N : ℕ) (W : Fin i → Finset ℕ)
    (a f lo hi : ℕ → ℝ) (pre : ℕ → ℕ → ℕ → Prop)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) : LabelledPhysical.Family Label N where
  labels := labels N W a f lo hi pre
  weight := fun x => (convolutionCoeff W x.1 : ℝ)
  cofactor := cofactor
  lower := lower lo
  upper := upper N hi
  weight_nonneg := fun _ _ => Nat.cast_nonneg _
  geometry := by
    intro x hx
    obtain ⟨_,_,hq,_,_,_,_,_,hf⟩ := (mem_labels x).mp hx
    have hpos := cofactor_pos hd hx
    exact ⟨hpos, (show (2 : ℝ) ≤ x.2.2.1 by exact_mod_cast
      (mem_primeWindow.mp hq).1.two_le).trans (le_max_left _ _), hf, physical_cap x hpos⟩

/-- All original source coordinates, including the output prime, are retained before encoding. -/
noncomputable def sources (N : ℕ) (W : Fin i → Finset ℕ)
    (a f lo hi : ℕ → ℝ) (pre : ℕ → ℕ → ℕ → Prop) : Finset Source :=
  (boxConvolutionSupport W).sigma fun d =>
    ((orderedTriples (primeWindow N (a d) (f d))).filter fun t =>
      pre d t.1 t.2.1 ∧ lo d ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < hi d).sigma fun t =>
        sourceSieveCarrier N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1

def encode (N : ℕ) (x : Source) : Σ _ : Label, ℕ :=
  ⟨(x.1,x.2.1.1,x.2.1.2.1,(N-x.2.2)/(x.1*x.2.1.1*x.2.1.2.1*x.2.1.2.2)),x.2.1.2.2⟩

theorem source_data {d p q r ell : ℕ}
    (hx : (⟨d,(p,q,r),ell⟩ : Source) ∈ sources N W a f lo hi pre) :
    d ∈ boxConvolutionSupport W ∧ p ∈ primeWindow N (a d) (f d) ∧
    q ∈ primeWindow N (a d) (f d) ∧ r ∈ primeWindow N (a d) (f d) ∧
    p < q ∧ q < r ∧ pre d p q ∧ lo d ≤ (r : ℝ) ∧ (r : ℝ) < hi d ∧
    ell ≤ N ∧ ell.Prime ∧ d*p*q*r ∣ N-ell ∧ Sifted (d*p*N) (N-ell) q := by
  simpa only [sources, mem_sigma, mem_filter, orderedTriples, mem_product,
    sourceSieveCarrier, mem_range, Nat.lt_succ_iff, and_assoc] using hx

theorem encode_injOn : Set.InjOn (encode N) (sources N W a f lo hi pre) := by
  rintro ⟨d,⟨p,q,r⟩,ell⟩ hx ⟨d',⟨p',q',r'⟩,ell'⟩ hy he
  have hd : d = d' := congrArg (fun x : Σ _ : Label, ℕ => x.1.1) he
  have hp : p = p' := congrArg (fun x : Σ _ : Label, ℕ => x.1.2.1) he
  have hq : q = q' := congrArg (fun x : Σ _ : Label, ℕ => x.1.2.2.1) he
  have hr : r = r' := congrArg (fun x : Σ _ : Label, ℕ => x.2) he
  subst d'; subst p'; subst q'; subst r'
  have hn : (N-ell)/(d*p*q*r) = (N-ell')/(d*p*q*r) :=
    congrArg (fun x : Σ _ : Label, ℕ => x.1.2.2.2) he
  obtain ⟨_,_,_,_,_,_,_,_,_,hle,_,hdv,_⟩ := source_data hx
  obtain ⟨_,_,_,_,_,_,_,_,_,hle',_,hdv',_⟩ := source_data hy
  have hv := Nat.mul_div_cancel' hdv
  have hv' := Nat.mul_div_cancel' hdv'
  rw [hn] at hv
  have heq : ell = ell' := by omega
  subst ell'
  rfl

/-- The quotient starts at one, not two; no unit source is discarded. -/
theorem source_quotient {d p q r ell : ℕ} (hN : 4 ≤ N) (he : Even N)
    (hd : 0 < d) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hle : ell ≤ N) (hell : ell.Prime) (hdv : d*p*q*r ∣ N-ell) :
    0 < (N-ell)/(d*p*q*r) ∧ (N-ell)/(d*p*q*r) ≤ N ∧
    cofactor (d,p,q,(N-ell)/(d*p*q*r)) * r = N-ell := by
  have hlt : ell < N := by
    have hne : ell ≠ N := by
      intro hh
      subst ell
      have := hell.even_iff.mp he
      omega
    omega
  have hpos : 0 < d*p*q*r := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd hp.pos) hq.pos) hr.pos
  refine ⟨Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdv) hpos,
    (Nat.div_le_self _ _).trans (Nat.sub_le _ _), ?_⟩
  simpa only [cofactor, mul_assoc, mul_comm, mul_left_comm] using Nat.mul_div_cancel' hdv

/-- Actual source tests are transported to a genuinely varying physical r-fibre. -/
theorem inclusion (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) :
    (sources N W a f lo hi pre).image (encode N) ⊆
      (family N W a f lo hi pre hd).labels.sigma (fun x =>
        ((family N W a f lo hi pre hd).primes x).filter
          (fun r => (N-cofactor x*r).Prime)) := by
  intro y hy
  obtain ⟨⟨d,⟨p,q,r⟩,ell⟩,hx,rfl⟩ := mem_image.mp hy
  obtain ⟨hxd,hp,hq,hr,hpq,hqr,hpre,hlo,hhi,hle,hell,hdv,hs⟩ := source_data hx
  let n := (N-ell)/(d*p*q*r)
  have hpP := (mem_primeWindow.mp hp).1
  have hqP := (mem_primeWindow.mp hq).1
  have hrP := (mem_primeWindow.mp hr).1
  obtain ⟨hn,hnN,hprod⟩ := source_quotient hN he (hd _ hxd) hpP hqP hrP hle hell hdv
  have hpos : 0 < cofactor (d,p,q,n) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hd _ hxd) hpP.pos) hqP.pos) hn
  have hcap : cofactor (d,p,q,n)*r ≤ N := hprod.trans_le (Nat.sub_le _ _)
  have hmask : Sifted (d*p*N) (cofactor (d,p,q,n)) q := by
    rw [← hprod] at hs
    exact (sifted_mul_iff _ _ _ _).mp hs |>.1
  have hl : lower lo (d,p,q,n) < r := by
    apply max_lt_iff.mpr
    exact ⟨by exact_mod_cast hqr, by dsimp at hlo ⊢; linarith⟩
  have hu : (r : ℝ) ≤ upper N hi (d,p,q,n) := by
    have hpR : (0 : ℝ) < cofactor (d,p,q,n) := by exact_mod_cast hpos
    exact le_min hhi.le ((le_div_iff₀ hpR).mpr (by
      rw [mul_comm]; exact_mod_cast hcap))
  apply mem_sigma.mpr
  refine ⟨(mem_labels _).mpr ⟨hxd,hp,hq,Nat.lt_succ_of_le hnN,hpq,hpre,hn,hmask,hl.le.trans hu⟩, ?_⟩
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨mem_range.mpr ?_,hrP,hl,hu⟩, ?_⟩
  · exact Nat.lt_succ_of_le ((Nat.le_mul_of_pos_left r hpos).trans hcap)
  · change (N-cofactor (d,p,q,n)*r).Prime
    rw [hprod, Nat.sub_sub_self hle]
    exact hell

/-- An arbitrary nonnegative test on label and physical prime is never merged by E. -/
theorem test_transport (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) (test : (Σ _ : Label, ℕ) → ℝ)
    (ht : ∀ y, 0 ≤ test y) :
    (∑ x ∈ sources N W a f lo hi pre, test (encode N x)) ≤
      ∑ x ∈ (family N W a f lo hi pre hd).labels,
        ∑ r ∈ ((family N W a f lo hi pre hd).primes x).filter
          (fun r => (N-cofactor x*r).Prime), test ⟨x,r⟩ := by
  rw [← sum_image encode_injOn, ← sum_sigma]
  exact sum_le_sum_of_subset_of_nonneg (inclusion hd hN he) (fun y _ _ => ht y)

noncomputable def sourceMass (N : ℕ) (W : Fin i → Finset ℕ)
    (a f lo hi : ℕ → ℝ) (pre : ℕ → ℕ → ℕ → Prop) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ t ∈ (orderedTriples (primeWindow N (a d) (f d))).filter
      (fun t => pre d t.1 t.2.1 ∧ lo d ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < hi d),
        (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ)

theorem source_upper (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) :
    sourceMass N W a f lo hi pre ≤ (family N W a f lo hi pre hd).primeMass := by
  have h := test_transport (a := a) (f := f) (lo := lo) (hi := hi) (pre := pre) hd hN he (fun y => (convolutionCoeff W y.1.1 : ℝ))
    (fun _ => Nat.cast_nonneg _)
  simpa only [sources, sum_sigma, encode, sum_const, nsmul_eq_mul, sourceMass,
    sourceSieveCount, Int.cast_natCast, mul_sum, LabelledPhysical.Family.primeMass,
    family, card_sigma, Nat.cast_sum, mul_sum, mul_comm] using h

theorem cofactor_divisors (x : Label) : x.1 ∣ cofactor x ∧ x.2.1 ∣ cofactor x ∧
    x.2.2.1 ∣ cofactor x := by
  unfold cofactor
  exact ⟨dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _,
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _,
    dvd_mul_of_dvd_left (dvd_mul_left _ _) _⟩

/-- At fixed E, n is uniquely recovered from d,p,q, independently of r. -/
theorem recover_n {x : Label} (hx : 0 < cofactor x) :
    cofactor x / (x.1*x.2.1*x.2.2.1) = x.2.2.2 := by
  have hb : 0 < x.1*x.2.1*x.2.2.1 := by
    change 0 < (x.1*x.2.1*x.2.2.1)*x.2.2.2 at hx
    exact Nat.pos_of_mul_pos_right hx
  exact Nat.mul_div_cancel_left _ hb

theorem fixedE_projection_injective {E : ℕ} (hE : 0 < E) :
    Set.InjOn (fun x : Label => (x.1,x.2.1,x.2.2.1)) {x | cofactor x = E} := by
  rintro ⟨d,p,q,n⟩ hx ⟨d',p',q',n'⟩ hy he
  have he' : d = d' ∧ p = p' ∧ q = q' := by simpa only [Prod.mk.injEq] using he
  rcases he' with ⟨hd,hp,hq⟩
  subst d'; subst p'; subst q'
  change cofactor (d,p,q,n) = E at hx
  change cofactor (d,p,q,n') = E at hy
  have hnx := recover_n (x := (d,p,q,n)) (by rw [hx]; exact hE)
  have hny := recover_n (x := (d,p,q,n')) (by rw [hy]; exact hE)
  rw [hx] at hnx
  rw [hy] at hny
  have : n = n' := hnx.symm.trans hny
  subst n'
  rfl

/-- Inverse on the original source, including the original output ell. -/
def decode (N : ℕ) (y : Σ _ : Label, ℕ) : Source :=
  ⟨y.1.1,(y.1.2.1,y.1.2.2.1,y.2),N-cofactor y.1*y.2⟩

theorem decode_encode {x : Source} (hx : x ∈ sources N W a f lo hi pre) :
    decode N (encode N x) = x := by
  rcases x with ⟨d,⟨p,q,r⟩,ell⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,hle,_,hdv,_⟩ := source_data hx
  have hprod : cofactor (d,p,q,(N-ell)/(d*p*q*r))*r = N-ell := by
    simpa only [cofactor, mul_assoc, mul_comm, mul_left_comm] using Nat.mul_div_cancel' hdv
  simp only [decode, encode, hprod, Nat.sub_sub_self hle]

/-- Exact arbitrary original tests on the image, before the one-sided physical enlargement. -/
theorem source_test_dictionary (test : Source → ℝ) :
    (∑ x ∈ sources N W a f lo hi pre, test x) =
      ∑ y ∈ (sources N W a f lo hi pre).image (encode N), test (decode N y) := by
  rw [sum_image encode_injOn]
  exact sum_congr rfl (fun x hx => congrArg test (decode_encode hx).symm)

/-- Unit quotient instances enter the same wide family directly. -/
theorem unit_retained (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) {d p q r ell : ℕ}
    (hx : (⟨d,(p,q,r),ell⟩ : Source) ∈ sources N W a f lo hi pre)
    (hn : (N-ell)/(d*p*q*r) = 1) :
    (d,p,q,1) ∈ (family N W a f lo hi pre hd).labels ∧
      r ∈ ((family N W a f lo hi pre hd).primes (d,p,q,1)).filter
        (fun r => (N-cofactor (d,p,q,1)*r).Prime) := by
  have h := inclusion hd hN he (mem_image_of_mem (encode N) hx)
  simpa only [encode, hn, mem_sigma] using h

end Wu2008DoubleSieve.LowerTripleGrouped
