import MathlibNt.Wu2008DoubleSieve.LastPrimeFourErrorPayment

/-! Small outputs remember all four prime slots. The arbitrary rough integer
is recovered from the positive product; no primality of that integer is used. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset Real
open scoped Classical

abbrev OriginalLabel := TruncatedFourPhysical.Label

def fourOutput (N : ℕ) (x : OriginalLabel) : ℕ := N - fourModulusProduct x.1*x.2
def fourComplement (x : OriginalLabel) : ℕ := fourModulusProduct x.1*x.2
def fourSlots (x : OriginalLabel) : Fin 4 → ℕ := ![x.1.1,x.1.2.1,x.1.2.2.1,x.1.2.2.2]
noncomputable def fourSmallLabels (N : ℕ) (e : Bool) (Z : ℝ) : Finset OriginalLabel :=
  (original N e).filter fun x => (fourOutput N x : ℝ) < Z
noncomputable def fourSmallBudget (Z : ℝ) : ℝ :=
  (1 / alpha)^4 * (⌊max Z 0⌋₊ + 1 : ℕ)

theorem fourOriginal_complement {N : ℕ} {e : Bool} {x : OriginalLabel}
    (hx : x ∈ original N e) :
    0 < fourComplement x ∧ fourComplement x < N ∧
      N - fourOutput N x = fourComplement x := by
  rcases x with ⟨⟨a,b,c,d⟩,n⟩
  obtain ⟨ha,_,_,hb,_,hc,_,_,_,_,hn,_,hd,_,_,_,_,hs,_⟩ := original_data hx
  have hid : fourModulusProduct (a,b,c,d)*n = cofactor (a,b,c,n)*d := by
    simp only [fourModulusProduct, cofactor]; ring
  have hp : 0 < fourComplement ⟨(a,b,c,d),n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos) hd.pos) (show 0 < n by omega)
  have hlt : fourComplement ⟨(a,b,c,d),n⟩ < N := by
    change fourModulusProduct (a,b,c,d)*n < N
    rw [hid]; exact hs
  exact ⟨hp,hlt,Nat.sub_sub_self hlt.le⟩

theorem fourOriginal_slots {N : ℕ} {e : Bool} {x : OriginalLabel}
    (hx : x ∈ original N e) : ∀ j : Fin 4,
    (fourSlots x j).Prime ∧ fourSlots x j ∣ fourComplement x ∧
      (N : ℝ)^alpha ≤ fourSlots x j := by
  rcases x with ⟨⟨a,b,c,d⟩,n⟩
  obtain ⟨ha,_,hza,hb,_,hc,_,hab,hbc,_,_,_,hd,_,hcd,_⟩ := original_data hx
  have hzb : (N : ℝ)^alpha ≤ b := hza.trans (by exact_mod_cast hab.le)
  have hzc : (N : ℝ)^alpha ≤ c := hzb.trans (by exact_mod_cast hbc.le)
  have hzd : (N : ℝ)^alpha ≤ d := hzc.trans (by exact_mod_cast hcd.le)
  have hda : a ∣ fourComplement ⟨(a,b,c,d),n⟩ :=
    (dvd_mul_right a b).trans ((dvd_mul_right _ c).trans
      ((dvd_mul_right _ d).trans (dvd_mul_right _ n)))
  have hdb : b ∣ fourComplement ⟨(a,b,c,d),n⟩ :=
    (dvd_mul_left b a).trans ((dvd_mul_right _ c).trans
      ((dvd_mul_right _ d).trans (dvd_mul_right _ n)))
  have hdc : c ∣ fourComplement ⟨(a,b,c,d),n⟩ :=
    (dvd_mul_left c (a*b)).trans ((dvd_mul_right _ d).trans (dvd_mul_right _ n))
  have hdd : d ∣ fourComplement ⟨(a,b,c,d),n⟩ :=
    (dvd_mul_left d (a*b*c)).trans (dvd_mul_right _ n)
  simp only [fourSlots, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true]
  exact ⟨⟨ha,hda,hza⟩,⟨hb,hdb,hzb⟩,⟨hc,hdc,hzc⟩,hd,hdd,hzd⟩

/-- The nonunit integer is recovered by exact division, not by a primality assumption. -/
theorem fourResidual_recovery {N : ℕ} {e : Bool} {x : OriginalLabel}
    (hx : x ∈ original N e) :
    x.2 = (N - fourOutput N x) / fourModulusProduct x.1 := by
  rw [(fourOriginal_complement hx).2.2]
  have hD : 0 < fourModulusProduct x.1 :=
    Nat.pos_of_mul_pos_right (fourOriginal_complement hx).1
  exact (Nat.mul_div_right x.2 hD).symm

/-- Actual output and the four selected prime slots reconstruct all five labels. -/
theorem fourOutput_slots_injective {N : ℕ} {e : Bool} :
    Set.InjOn (fun x : OriginalLabel => (fourOutput N x, fourSlots x)) (original N e) := by
  rintro ⟨⟨a,b,c,d⟩,n⟩ hx ⟨⟨a',b',c',d'⟩,n'⟩ hy h
  have hs := congrArg Prod.snd h
  have ha : a = a' := congrFun hs 0
  have hb : b = b' := congrFun hs 1
  have hc : c = c' := congrFun hs 2
  have hd : d = d' := congrFun hs 3
  subst a'; subst b'; subst c'; subst d'
  have hout := congrArg Prod.fst h
  have hn : n = n' := (fourResidual_recovery hx).trans
    ((congrArg (fun r => (N-r)/fourModulusProduct (a,b,c,d)) hout).trans
      (fourResidual_recovery hy).symm)
  subst n'; rfl

theorem fourComplement_slots_injective {N : ℕ} {e : Bool} :
    Set.InjOn (fun x : OriginalLabel => (fourComplement x, fourSlots x)) (original N e) := by
  intro x hx y hy h
  have hc : fourComplement x = fourComplement y := congrArg Prod.fst h
  have hs : fourSlots x = fourSlots y := congrArg Prod.snd h
  have ho : fourOutput N x = fourOutput N y := congrArg (fun m => N-m) hc
  exact fourOutput_slots_injective hx hy (Prod.ext ho hs)

theorem fourSmallLabels_card_le {N : ℕ} (hN : 1 < N) (e : Bool) (Z : ℝ) :
    ((fourSmallLabels N e Z).card : ℝ) ≤ fourSmallBudget Z := by
  let E := (range (⌊max Z 0⌋₊+1)).image (fun r => N-r)
  have h := omega3_labels_card_le_outputs (fourSmallLabels N e Z) fourComplement fourSlots E
    (fourComplement_slots_injective.mono (filter_subset _ _))
    (by
      intro x hx
      obtain ⟨hx,hZ⟩ := mem_filter.mp hx
      exact mem_image.mpr ⟨fourOutput N x, mem_range.mpr (Nat.lt_succ_of_le
        (Nat.le_floor (hZ.le.trans (le_max_left _ _)))), (fourOriginal_complement hx).2.2⟩)
    hN (by norm_num [alpha, truncatedSixthLowerAlpha] : 0 < alpha)
    (fun x hx => ⟨(fourOriginal_complement (mem_filter.mp hx).1).1,
      (fourOriginal_complement (mem_filter.mp hx).1).2.1.le⟩)
    (fun x hx => fourOriginal_slots (mem_filter.mp hx).1)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast (card_image_le.trans_eq (card_range _) : E.card ≤ ⌊max Z 0⌋₊+1)

theorem fourOriginal_large_le_sifted (N : ℕ) (e : Bool) (Z : ℝ) :
    (((original N e).filter (fun x => ¬(fourOutput N x : ℝ) < Z)).card : ℝ) ≤
      fourSifted N e Z := by
  let G := (labels N e).sigma (fun t =>
    (omega3ProfilePrimes N (lower N e t) (upper N e t)).filter
      (fun d => Sifted N (N-cofactor t*d) Z))
  have hm : Set.MapsTo switch
      ((original N e).filter (fun x => ¬(fourOutput N x : ℝ) < Z)) G := by
    rintro ⟨⟨a,b,c,d⟩,n⟩ hx
    obtain ⟨hx,hZ⟩ := mem_filter.mp hx
    obtain ⟨ht,hd⟩ := mem_sigma.mp (original_maps hx)
    obtain ⟨hd,hprime⟩ := mem_filter.mp hd
    have hid : fourOutput N ⟨(a,b,c,d),n⟩ = N-cofactor (a,b,c,n)*d := by
      unfold fourOutput fourModulusProduct cofactor
      congr 1; ring
    rw [hid] at hZ
    exact mem_sigma.mpr ⟨ht,mem_filter.mpr ⟨hd,ninth_prime_sifted hprime (le_of_not_gt hZ)⟩⟩
  have hc := card_le_card_of_injOn switch hm switch_injective.injOn
  have heq : (G.card : ℝ) = fourSifted N e Z := by
    simp only [G, card_sigma, Nat.cast_sum, fourSifted]
  exact (show (_ : ℝ) ≤ (G.card : ℝ) by exact_mod_cast hc).trans_eq heq

theorem fourPhysical_upper_finite {N D : ℕ} (hN : 1 < N) (e : Bool)
    (he : Even N) (Z : ℝ) (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    ((original N e).card : ℝ) ≤
      fourMass N e * ordinaryRosserMainSum true N 1 D Z +
        signedR1 N e D Z + fourR2 N e D Z + fourSmallBudget Z := by
  have hsplit := card_filter_add_card_filter_not (s := original N e)
    (fun x => (fourOutput N x : ℝ) < Z)
  have hsplitR : ((fourSmallLabels N e Z).card : ℝ) +
      (((original N e).filter (fun x => ¬(fourOutput N x : ℝ) < Z)).card : ℝ) =
      (original N e).card := by exact_mod_cast hsplit
  have hs := fourSmallLabels_card_le hN e Z
  have hl := fourOriginal_large_le_sifted N e Z
  have hu := four_sifted_upper_finite (e := e) he Z hD hZ
  linarith

theorem fourSmallBudget_source_bound {N : ℕ} (hN : 512 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    fourSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
      (2 * (1 / alpha)^4) * (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hZ : sqrt ((N : ℝ) ^ (1 / 2 - δ)) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_mul (Nat.cast_nonneg N)]
    exact rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    simpa only [rpow_zero] using
      rpow_le_rpow_of_exponent_le hN1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have hfloor := Nat.floor_le (sqrt_nonneg ((N : ℝ) ^ (1 / 2 - δ)))
  unfold fourSmallBudget
  rw [max_eq_left (sqrt_nonneg _), Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ((1 / alpha)^4) * (2 * (N : ℝ) ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

theorem fourSmall_error_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ δ : ℝ, 0 < δ →
      fourSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤ ε * N / log N ^ 2 := by
  have hk : 0 < alpha := by norm_num [alpha, truncatedSixthLowerAlpha]
  obtain ⟨T, hT, hp⟩ := ninth_power_log_error_budget 0
    (show 0 < 2 * (1 / alpha)^4 by positivity) (show (0 : ℝ) < 3 / 4 by norm_num) hε
  refine ⟨T, hT, ?_⟩
  intro N hN δ hδ
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (2 * (1 / alpha)^4) * (N : ℝ) ^ (1 / 4 : ℝ) :=
      fourSmallBudget_source_bound (hT.trans hN) hδ
    _ = (2 * (1 / alpha)^4) * N * log N ^ (0 : ℕ) / (N : ℝ) ^ (3 / 4 : ℝ) := by
      rw [show (1 / 4 : ℝ) = 1 - 3 / 4 by norm_num, rpow_sub hNR, rpow_one, pow_zero]
      ring
    _ ≤ _ := hp N hN
end Wu2008DoubleSieve.LastPrimeFour
