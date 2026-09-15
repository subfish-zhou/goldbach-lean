import MathlibNt.Wu2008DoubleSieve.HighSixTotalMass

namespace Wu2008DoubleSieve.HighSix
open Finset Set Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

noncomputable def primeWeight (δ t : ℝ) : ℝ := 1/((1/2-δ)-t)
noncomputable def primeIntegral (δ : ℝ) : ℝ :=
  ∫ t in left..right, 1/(t*((1/2-δ)-t))
noncomputable def closedPrimes (N : ℕ) := primesIcc ((N : ℝ)^left) ((N : ℝ)^right)
noncomputable def reciprocalMain (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ P N, primeWeight δ (log p/log N)/(p : ℝ)

/-- The actual original window lies in the initial constant-A branch. -/
theorem primeWeight_eq_single {δ t : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc left right) :
    SingleUpperQuadrature.weight δ t = primeWeight δ t := by
  have ht' : t ∈ Icc (1/15 : ℝ) (1/3) := by
    constructor <;> norm_num [left,right] at ht ⊢ <;> linarith [ht.1,ht.2]
  have ha := SingleUpperQuadrature.argument_mem hδ hδhi ht'
  have ha3 : ((1/2-δ)-t)/truncatedSixthLowerAlpha ≤ 3 := by
    apply (div_le_iff₀ (by norm_num [truncatedSixthLowerAlpha])).mpr
    norm_num [truncatedSixthLowerAlpha,left] at ht ⊢
    linarith [ht.1]
  have hA : wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha) = 1 := by
    generalize hu : ((1/2-δ)-t)/truncatedSixthLowerAlpha = u at *
    unfold wuUpperCoefficient
    rw [MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_eq_of_le_three ha3]
    field_simp [(show u ≠ 0 by linarith [ha.1]),
      (exp_pos eulerMascheroniConstant).ne']
  simp only [SingleUpperQuadrature.weight,primeWeight,hA]

theorem closed_coordinate {N p : ℕ} (hN : 2 ≤ N) (hp : p ∈ closedPrimes N) :
    log (p : ℝ)/log N ∈ Icc left right := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  obtain ⟨hpp,hlo,hhi⟩ := (mem_primesIcc (rpow_nonneg hN0.le right)).mp hp
  constructor
  · apply (le_div_iff₀ hl).mpr
    rw [← log_rpow hN0]
    exact log_le_log (by positivity) hlo
  · apply (div_le_iff₀ hl).mpr
    rw [← log_rpow hN0]
    exact log_le_log (by exact_mod_cast hpp.pos) hhi

theorem primeWeight_bounds {δ t : ℝ} (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc left right) : 0 ≤ primeWeight δ t ∧ primeWeight δ t ≤ 10 := by
  have hd : (1/10 : ℝ) ≤ (1/2-δ)-t := by
    norm_num [right] at ht
    linarith [ht.2]
  have hp : 0 < (1/2-δ)-t := by linarith
  exact ⟨by unfold primeWeight; positivity,
    (div_le_iff₀ hp).mpr (by linarith)⟩

/-- A two-sided quadrature on the full closed carrier, using the existing
true prime producer and the exact constant-A branch, not an upper-minus-upper. -/
theorem closed_prime_integral {δ ε : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      |(∑ p ∈ closedPrimes N, primeWeight δ (log p/log N)/(p : ℝ)) - primeIntegral δ| ≤ ε := by
  obtain ⟨T,hT4,hT⟩ := SingleUpperQuadrature.weighted_prime_quadrature hε
  refine ⟨T,hT4,?_⟩
  intro N hN
  have h := hT N hN δ left right hδ hδhi (by norm_num [left])
    (by norm_num [left,right]) (by norm_num [right])
  have he : (∫ t in left..right, SingleUpperQuadrature.weight δ t/t) = primeIntegral δ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num [left,right])] at ht
    dsimp only
    rw [primeWeight_eq_single hδ hδhi ht]
    simp only [primeWeight,div_eq_mul_inv,mul_inv_rev,one_mul]
  rw [he] at h
  have hs : (∑ p ∈ closedPrimes N, SingleUpperQuadrature.weight δ (log p/log N)/(p : ℝ)) =
      ∑ p ∈ closedPrimes N, primeWeight δ (log p/log N)/(p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [primeWeight_eq_single hδ hδhi (closed_coordinate (by omega) hp)]
  exact (hs ▸ h).le

/-- The lost atoms are exactly prime divisors of N or the upper endpoint.
The lower endpoint is retained. The endpoint fiber has cardinality at most one. -/
theorem missing_card {N : ℕ} (hN : 2 ≤ N) :
    (((closedPrimes N \ P N).card : ℕ) : ℝ) ≤ 1/left+1 := by
  have hN0 : 0 < N := by omega
  let E := (closedPrimes N).filter (fun p : ℕ => (p : ℝ) = (N : ℝ)^right)
  have he : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    exact_mod_cast (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
  have hs : closedPrimes N \ P N ⊆ largePrimeDivisors N ((N : ℝ)^left) ∪ E := by
    intro p hp
    obtain ⟨hc,hn⟩ := mem_sdiff.mp hp
    obtain ⟨hpp,hlo,hhi⟩ := (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) right)).mp hc
    by_cases hd : p ∣ N
    · exact mem_union_left _ (mem_largePrimeDivisors.mpr ⟨hpp,hd,hN0.ne',hlo⟩)
    · apply Finset.mem_union_right
      apply mem_filter.mpr
      refine ⟨hc,le_antisymm hhi ?_⟩
      by_contra hh
      have hpN : p ∈ P N := mem_primeWindow.mpr
        ⟨hpp,hpp.coprime_iff_not_dvd.mpr hd,hlo,lt_of_not_ge hh⟩
      exact hn hpN
  have hc := (Finset.card_le_card hs).trans (card_union_le _ _)
  have hcR : ((closedPrimes N \ P N).card : ℝ) ≤
      (largePrimeDivisors N ((N : ℝ)^left)).card + 1 := by exact_mod_cast (by omega :
        (closedPrimes N \ P N).card ≤ (largePrimeDivisors N ((N : ℝ)^left)).card+1)
  have hd := largePrimeDivisors_card_le_inv (κ := left) (by omega) hN0 le_rfl (by norm_num [left])
  linarith

/-- The exact coprime half-open mask is paid by its actual missing atoms. -/
theorem reciprocal_mask_error {N : ℕ} {δ : ℝ} (hN : 2 ≤ N) (hδhi : δ ≤ 1/100) :
    |(∑ p ∈ closedPrimes N, primeWeight δ (log p/log N)/(p : ℝ)) - reciprocalMain N δ| ≤
      (1/left+1)*10/(N : ℝ)^left := by
  have hpow : 0 < (N : ℝ)^left := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hsub : P N ⊆ closedPrimes N := fun _ hp => outer_closed hp
  rw [reciprocalMain, ← sum_sdiff hsub, add_sub_cancel_right]
  calc
    _ ≤ ∑ p ∈ closedPrimes N \ P N, |primeWeight δ (log p/log N)/(p : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ closedPrimes N \ P N, 10/(N : ℝ)^left := by
      apply sum_le_sum
      intro p hp
      have hc := (mem_sdiff.mp hp).1
      have hp' := (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) right)).mp hc
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
      have hw := primeWeight_bounds hδhi (closed_coordinate hN hc)
      rw [abs_div,abs_of_nonneg hw.1,abs_of_pos hp0]
      exact (div_le_div_of_nonneg_right hw.2 hp0.le).trans
        (div_le_div_of_nonneg_left (by norm_num) hpow hp'.2.1)
    _ = ((closedPrimes N \ P N).card : ℝ)*(10/(N : ℝ)^left) := by simp
    _ ≤ (1/left+1)*(10/(N : ℝ)^left) :=
      mul_le_mul_of_nonneg_right (missing_card hN) (by positivity)
    _ = _ := by ring

/-- Two-sided true-prime quadrature on the original coprime half-open window. -/
theorem reciprocal_integral {δ ε : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      |reciprocalMain N δ-primeIntegral δ| ≤ ε := by
  obtain ⟨T1,hT14,hT1⟩ := closed_prime_integral hδ hδhi (half_pos hε)
  have hgrow : Tendsto (fun N : ℕ => (N : ℝ)^left) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [left])).comp tendsto_natCast_atTop_atTop
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp
    (hgrow.eventually (eventually_ge_atTop ((1/left+1)*10/(ε/2))))
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hp : 0 < (N : ℝ)^left := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hb : (1/left+1)*10/(N : ℝ)^left ≤ ε/2 := by
    apply (div_le_iff₀ hp).mpr
    have hh := (div_le_iff₀ (half_pos hε)).mp (hT2 N (by omega))
    linarith
  have hm := (reciprocal_mask_error hN2 hδhi).trans hb
  rw [abs_sub_comm] at hm
  exact (abs_sub_le _ _ _).trans ((add_le_add hm (hT1 N (by omega))).trans (by linarith))
end Wu2008DoubleSieve.HighSix
