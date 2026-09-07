import MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundaryBudget

noncomputable section
open Classical Finset Filter LiLiuPrereqBuchstab
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.PrimeReciprocalLogScale

namespace G12RoughBoundary

/-- The closed integer interval pays its endpoint by 1/r. -/
theorem integer_band_reciprocal {a : ℝ} (ha : 1 ≤ a) {r : ℕ} (hr : 0 < r) :
    (∑ q ∈ Icc r ⌊a*(r : ℝ)⌋₊, 1/(q : ℝ)) ≤ (a-1)+1/(r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have har : (r : ℝ) ≤ a*r := le_mul_of_one_le_left hrR.le ha
  have hf : r ≤ ⌊a*(r : ℝ)⌋₊ := Nat.le_floor har
  have hc : ((Icc r ⌊a*(r : ℝ)⌋₊).card : ℝ) ≤ a*r+1-r := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega : r ≤ ⌊a*(r : ℝ)⌋₊+1), Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (har.trans' hrR.le)]
  calc
    _ ≤ ∑ _q ∈ Icc r ⌊a*(r : ℝ)⌋₊, 1/(r : ℝ) := by
      apply sum_le_sum
      intro q hq
      exact one_div_le_one_div_of_le hrR (by exact_mod_cast (mem_Icc.mp hq).1)
    _ = ((Icc r ⌊a*(r : ℝ)⌋₊).card : ℝ) / r := by simp [div_eq_mul_inv]
    _ ≤ (a*r+1-r)/r := div_le_div_of_nonneg_right hc hrR.le
    _ = _ := by field_simp; ring

def primes (N : ℕ) : Finset ℕ := goldbachG11PrimeInterval N (4/53) (3/11)
def harmonic (N : ℕ) : ℝ := ∑ p ∈ primes N, 1/(p : ℝ)
def harmonicBound : ℝ := |Real.log ((3/11 : ℝ)/(4/53))|+1

theorem harmonicBound_pos : 0 < harmonicBound := by unfold harmonicBound; positivity

theorem harmonic_nonneg (N : ℕ) : 0 ≤ harmonic N := sum_nonneg (fun _ _ => by positivity)

theorem harmonic_eventually : ∃ K : ℕ, ∀ N : ℕ, K ≤ N → harmonic N ≤ harmonicBound := by
  have ht := tendsto_primeReciprocalLogInterval (a := (4/53 : ℝ)) (b := (3/11 : ℝ))
    (by norm_num) (by norm_num)
  have hlt : Real.log ((3/11 : ℝ)/(4/53)) < harmonicBound := by
    unfold harmonicBound
    linarith [le_abs_self (Real.log ((3/11 : ℝ)/(4/53)))]
  obtain ⟨K,hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hlt))
  exact ⟨K,fun N hN => (hK N hN).le⟩

def labels (N : ℕ) : Finset GoldbachG11Label :=
  goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))

def nearLabels (N : ℕ) (a : ℝ) : Finset GoldbachG11Label :=
  (labels N).filter fun v => (v.2.2.2 : ℝ) ≤ a*v.2.2.1

def nearMass (N : ℕ) (a : ℝ) : ℝ :=
  ∑ v ∈ nearLabels N a, (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ)

def nearReciprocal (N : ℕ) (a : ℝ) : ℝ :=
  ∑ v ∈ nearLabels N a, 1/(goldbachG11LabelProd v : ℝ)

/-- All three unexpanded prime coordinates stay in the original exponent range. -/
theorem labels_primes {N : ℕ} (hN : 1 ≤ N) {v : GoldbachG11Label} (hv : v ∈ labels N) :
    v.1 ∈ primes N ∧ v.2.1 ∈ primes N ∧ v.2.2.1 ∈ primes N := by
  rcases v with ⟨t,s,r,q⟩
  obtain ⟨hr,hq,hs,ht,_,hz,hrq,hqs,hsb,hbt,htc⟩ := mem_goldbachG12Labels_iff.mp hv
  have hz' := (goldbachG11_prime_lower_cutoff_iff N r hr).mp hz
  have hrs : (r : ℝ) ≤ s := by exact_mod_cast hrq.trans hqs
  have hbc : (N : ℝ)^(4/33 : ℝ) ≤ (N : ℝ)^(3/11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  simp only [primes,mem_goldbachG11PrimeInterval]
  exact ⟨⟨ht,((hz'.trans_le hrs).trans_le hsb).trans_le hbt,htc⟩,
    ⟨hs,hz'.trans_le hrs,hsb.trans hbc⟩,hr,hz',hrs.trans (hsb.trans hbc)⟩

/-- Expand q to integers, never any of r,s,t. All repeated labels remain. -/
theorem nearReciprocal_le {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 1 ≤ a) :
    nearReciprocal N a ≤ harmonic N ^ 3 * ((a-1)+1/((N : ℝ)^(4/53 : ℝ))) := by
  let B : Finset GoldbachG11Label := (primes N).sigma fun _t =>
    (primes N).sigma fun _s => (primes N).sigma fun r => Icc r ⌊a*(r : ℝ)⌋₊
  have hsub : nearLabels N a ⊆ B := by
    intro v hv
    obtain ⟨hv,hnear⟩ := mem_filter.mp hv
    obtain ⟨ht,hs,hr⟩ := labels_primes hN hv
    have hrq := (mem_goldbachG12Labels_iff.mp hv).2.2.2.2.2.2.1
    exact mem_sigma.mpr ⟨ht,mem_sigma.mpr ⟨hs,mem_sigma.mpr
      ⟨hr,mem_Icc.mpr ⟨hrq,Nat.le_floor hnear⟩⟩⟩⟩
  have hz : (0 : ℝ) < (N : ℝ)^(4/53 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  calc
    _ ≤ ∑ v ∈ B, 1/(goldbachG11LabelProd v : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ t ∈ primes N, ∑ s ∈ primes N, ∑ r ∈ primes N,
        ((1/(r : ℝ))*(1/(s : ℝ))*(1/(t : ℝ))) *
          (∑ q ∈ Icc r ⌊a*(r : ℝ)⌋₊, 1/(q : ℝ)) := by
      simp only [B,sum_sigma,mul_sum,goldbachG11LabelProd,Nat.cast_mul,one_div,mul_inv]
      apply sum_congr rfl; intro t _
      apply sum_congr rfl; intro s _
      apply sum_congr rfl; intro r _
      apply sum_congr rfl; intro q _
      ring
    _ ≤ ∑ t ∈ primes N, ∑ s ∈ primes N, ∑ r ∈ primes N,
        ((1/(r : ℝ))*(1/(s : ℝ))*(1/(t : ℝ))) *
          ((a-1)+1/((N : ℝ)^(4/53 : ℝ))) := by
      apply sum_le_sum; intro t _
      apply sum_le_sum; intro s _
      apply sum_le_sum; intro r hr
      have hd := mem_goldbachG11PrimeInterval.mp hr
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (integer_band_reciprocal ha hd.1.pos).trans
        (add_le_add_right (one_div_le_one_div_of_le hz hd.2.1.le) _)
    _ = _ := by
      simp only [← sum_mul,← mul_sum,harmonic]
      ring

/-- True uniform Buchstab, with a deliberately coarse fixed constant 2. -/
theorem cofactor_eventually : ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N →
    ∀ v ∈ labels N, (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ) ≤
      2*((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ) := by
  obtain ⟨K,hK,hb⟩ := goldbachG12_rough_upper_buchstab 1 (by norm_num)
  refine ⟨K,hK,?_⟩
  intro N hN v hv
  have hN2 : 2 ≤ N := by omega
  rcases v with ⟨t,s,r,q⟩
  have hm : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [labels,goldbachG12Labels,mem_sigma] using hv
  have hu := goldbachG12_canonical_logQuotient_bounds hN2 hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  have hw := LiLiuGoldbachG12BuchstabMajorant.buchstab_le_564383 hu.1
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos
    (by exact_mod_cast (mem_goldbachClosedPrimes_iff.mp hm.2.2.2).1.one_lt)
  have hp := hb N hN _ hv
  unfold goldbachG11BuchstabMass at hp
  have hy : 0 ≤ (N : ℝ)/goldbachG11LabelProd ⟨t,s,r,q⟩ := by positivity
  have hh := mul_le_mul_of_nonneg_left hw (div_nonneg hy hlq.le)
  dsimp only [goldbachG11LabelProd] at hp hh hy ⊢
  have hn := div_nonneg hy hlq.le
  simp only [div_eq_mul_inv] at hp hh hn ⊢
  nlinarith only [hp,hh,hn]

/-- The log is the cofactor log, not a second output-prime saving. -/
theorem normalized_cofactor_le {N : ℕ} (hN : 4 ≤ N) {v : GoldbachG11Label}
    (hv : v ∈ labels N)
    (hb : (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ) ≤
      2*((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ)) :
    Real.log (N : ℝ)/(N : ℝ) *
      (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ) ≤
        (53/2 : ℝ) * (1/(goldbachG11LabelProd v : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hd : (0 : ℝ) < goldbachG11LabelProd v := by exact_mod_cast goldbachG12LabelProd_pos hv
  obtain ⟨_,hq,_,_,_,hz,hrq,_,_,_,_⟩ := mem_goldbachG12Labels_iff.mp hv
  have hqlog : 0 < Real.log (v.2.2.2 : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hzq : (N : ℝ)^(4/53 : ℝ) ≤ v.2.2.2 := hz.trans (by exact_mod_cast hrq)
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hzq
  rw [Real.log_rpow hNp] at hl
  calc
    _ ≤ Real.log (N : ℝ)/(N : ℝ) *
        (2*((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg hlog hNp.le)
    _ = (2*Real.log (N : ℝ)/Real.log (v.2.2.2 : ℝ)) * (1/(goldbachG11LabelProd v : ℝ)) := by
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_iff₀ hqlog).mpr
      linarith

end G12RoughBoundary
