import Wu08FirstPrimeFourGeometry
import MathlibNt.SieveTheory.LiLiuFouvryG9ReducedWeights
import MathlibNt.SieveTheory.LiLiuFouvryG9WFLevel

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace Wu08FirstPrimeFour

def beta (N a : ℕ) : ℝ := if a.Coprime N then primeSWBeta a else 0
def output (N m a : ℕ) : ℕ := ((N : ℤ)-(m : ℤ)*a).natAbs

theorem beta_nonneg (N a : ℕ) : 0 ≤ beta N a := by
  unfold beta primeSWBeta
  split_ifs <;> norm_num

def primeRectangle (N : ℕ) (L : Finset Long) (V : Finset ℕ) : ℝ :=
  ∑ m ∈ products L, ∑ a ∈ V, alpha L m*beta N a*
    (if (output N m a).Prime then 1 else 0)
def lowRectangle (N : ℕ) (L : Finset Long) (V : Finset ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ products L, ∑ a ∈ V, alpha L m*beta N a*
    (if (output N m a : ℝ) < z then 1 else 0)
def siftedRectangle (N : ℕ) (L : Finset Long) (V P : Finset ℕ) : ℝ :=
  weightedSequenceSifted (products L ×ˢ V)
    (fun p => output N p.1 p.2) (fun p => alpha L p.1*beta N p.2) P

theorem primeRectangle_labels (N : ℕ) (L : Finset Long) (V : Finset ℕ) :
    primeRectangle N L V = ∑ p ∈ L ×ˢ V,
      beta N p.2*(if (output N (longProduct p.1) p.2).Prime then 1 else 0) := by
  unfold primeRectangle
  rw [sum_product]
  dsimp only
  rw [alpha_sum L (fun m => ∑ a ∈ V, beta N a*(if (output N m a).Prime then 1 else 0))]
  apply sum_congr rfl
  intro m _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

/-- Actual finite count upper: only the rectangular cover discards gates.
The map is injective on full labels, not on outputs or long products. -/
theorem box_le_primeRectangle (N : ℕ) (e : Bool) (L : Finset Long) (V : Finset ℕ) :
    ((box N e L V).card : ℝ) ≤ primeRectangle N L V := by
  let W : Long × ℕ → ℝ := fun p =>
    beta N p.2*(if (output N (longProduct p.1) p.2).Prime then 1 else 0)
  have hw : ∀ p, 0 ≤ W p := by
    intro p
    dsimp only [W]
    exact mul_nonneg (beta_nonneg _ _) (by split_ifs <;> norm_num)
  have hone : ∀ x ∈ box N e L V, W (firstSwitch x) = 1 := by
    rintro ⟨⟨a,b,c,d⟩,n⟩ hx
    have hmem := (mem_filter.mp hx).1
    obtain ⟨ha,haN,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hs,hp⟩ :=
      LastPrimeFour.original_data hmem
    have hid : longProduct (b,c,d,n)*a = LastPrimeFour.cofactor (a,b,c,n)*d := by
      simp only [longProduct,LastPrimeFour.cofactor]
      ring
    have hout : output N (longProduct (b,c,d,n)) a =
        N-LastPrimeFour.cofactor (a,b,c,n)*d := by
      unfold output
      rw [g9IntegerFibre_original N _ _ (hid.symm ▸ hs.le),hid]
    change beta N a*(if (output N (longProduct (b,c,d,n)) a).Prime then 1 else 0)=1
    rw [hout,if_pos hp]
    simp [beta,primeSWBeta,haN,ha]
  have hsub : (box N e L V).image firstSwitch ⊆ L ×ˢ V := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    exact mem_product.mpr (box_maps hx)
  calc
    _ = ∑ x ∈ box N e L V, W (firstSwitch x) := by
      calc
        _ = ∑ _x ∈ box N e L V, (1 : ℝ) := by simp
        _ = _ := sum_congr rfl (fun x hx => (hone x hx).symm)
    _ = ∑ p ∈ (box N e L V).image firstSwitch, W p :=
      (sum_image (fun _ _ _ _ h => firstSwitch_injective h)).symm
    _ ≤ ∑ p ∈ L ×ˢ V, W p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hw p)
    _ = _ := (primeRectangle_labels N L V).symm

/-- Exact prime alternative; low prime outputs are retained, including at z. -/
theorem prime_indicator_le_sifted_low (P : Finset ℕ) (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hcut : ∀ p ∈ P, (p : ℝ) < z) (r : ℕ) :
    (if r.Prime then (1 : ℝ) else 0) ≤
      (if r.Coprime (P.prod id) then 1 else 0) + (if (r : ℝ) < z then 1 else 0) := by
  by_cases hp : r.Prime
  · by_cases hr : (r : ℝ) < z
    · simp only [if_pos hp,if_pos hr]
      split_ifs <;> norm_num
    · have hc : r.Coprime (P.prod id) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro p hpP
        apply Nat.Coprime.symm
        apply (hP p hpP).coprime_iff_not_dvd.mpr
        intro hpr
        have he : p=r := (Nat.dvd_prime hp).mp hpr |>.resolve_left (hP p hpP).ne_one
        subst p
        exact hr (hcut r hpP)
      simp only [if_pos hp,if_neg hr,if_pos hc,add_zero,le_refl]
  · simp only [if_neg hp]
    split_ifs <;> norm_num

theorem primeRectangle_le_sifted_low (N : ℕ) (L : Finset Long) (V P : Finset ℕ)
    (z : ℝ) (hP : ∀ p ∈ P, p.Prime) (hcut : ∀ p ∈ P, (p : ℝ) < z) :
    primeRectangle N L V ≤ siftedRectangle N L V P+lowRectangle N L V z := by
  unfold primeRectangle siftedRectangle lowRectangle weightedSequenceSifted
  rw [sum_product,← sum_add_distrib]
  apply sum_le_sum
  intro m _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro a _
  have h := mul_le_mul_of_nonneg_left (prime_indicator_le_sifted_low P z hP hcut (output N m a))
    (mul_nonneg (alpha_nonneg L m) (beta_nonneg N a))
  simpa only [mul_add] using h

/-- Finite first-prime sieve with the true full-cofactor coprime center. -/
theorem rectangle_weighted_upper (N : ℕ) (L : Finset Long) (V P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D η z : ℝ}
    (hD : 2 ≤ D) (hη : 0 < η) (hηu : η < 1/8) (hcut : ∀ p ∈ P, (p : ℝ) < z) :
    siftedRectangle N L V P ≤
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d*g9IntegerFibreCenter (products L) V (alpha L) (beta N) d) +
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d*bilinearDiscrepancy (products L) V (alpha L) (beta N) N d) := by
  have h := externalFamily_weighted_sequence_sieve_centered P hP hD hη hηu hcut
    (products L ×ˢ V) (fun p => output N p.1 p.2) (fun p => alpha L p.1*beta N p.2)
    (fun p _ => mul_nonneg (alpha_nonneg L p.1) (beta_nonneg N p.2))
    (g9IntegerFibreCenter (products L) V (alpha L) (beta N))
  have heq : ∀ d, weightedDivCount (products L ×ˢ V) (fun p => output N p.1 p.2)
      (fun p => alpha L p.1*beta N p.2) d-
      g9IntegerFibreCenter (products L) V (alpha L) (beta N) d =
      bilinearDiscrepancy (products L) V (alpha L) (beta N) N d :=
    fun d => g9IntegerFibre_centered_eq _ _ _ _ _ d
  simp only [heq] at h
  exact h

/-- The published C2 engine really accepts the new four-label long coefficient.
The threshold precedes the interval, long labels, and SAME signed weight. -/
theorem rectangle_C2 (j A : ℕ) {Cscale ε : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ z : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*z.scale=x → ε ≤ ν → ν ≤ 1/10+ε/10 → z.scale=x^ν →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x → ∀ L : Finset Long,
      (∀ t ∈ L, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2) →
      (∀ t ∈ L, M ≤ (longProduct t : ℝ) ∧ (longProduct t : ℝ) ≤ 2*M) →
      ∀ c : ℕ → ℝ, SignedWellFactorable j (x^((5-5*ν)/9-ε)) c →
      |signedError (products L) (primeSWInterval z.lower z.upper)
        (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) (alpha L) (beta N) c N| ≤ x/log x^A := by
  filter_upwards [primeC2_goldbach_rectangle_kscale 8 j A hCscale hε] with x hx
  intro z M ν hM hMT hεν hν hT N hN hNx L hL hscale c hc
  exact hx z M ν hM hMT hεν hν hT N hN hNx (products L)
    (fun m hm => by obtain ⟨t,ht,rfl⟩ := mem_image.mp hm; exact hscale t ht)
    (alpha L) c (fun m _ => alpha_order_eight L hL m) hc

/-- No asymptotic error is discarded here: this already bounds an actual box. -/
theorem box_weighted_upper (N : ℕ) (e : Bool) (L : Finset Long) (V P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D η z : ℝ}
    (hD : 2 ≤ D) (hη : 0 < η) (hηu : η < 1/8) (hcut : ∀ p ∈ P, (p : ℝ) < z) :
    ((box N e L V).card : ℝ) ≤
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d*g9IntegerFibreCenter (products L) V (alpha L) (beta N) d) +
      (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D η z t d*bilinearDiscrepancy (products L) V (alpha L) (beta N) N d) +
      lowRectangle N L V z :=
  (box_le_primeRectangle N e L V).trans
    ((primeRectangle_le_sifted_low N L V P z hP hcut).trans
      (add_le_add (rectangle_weighted_upper N L V P hP hD hη hηu hcut) le_rfl))

#print axioms box_weighted_upper
#print axioms rectangle_C2
end Wu08FirstPrimeFour
