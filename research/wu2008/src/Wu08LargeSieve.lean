import Wu08PrefixPayment
import MathlibNt.Wu2008DoubleSieve.LastPrimeFourPhysicalSieveEndpoint
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRestriction

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.Large
open LastPrimeFour

def family (N : ℕ) (e : Bool) : LabelledPhysical.Family Index N :=
  (LastPrimeFour.family N e).restrictLabels fun t => (N : ℝ)^(1/10 : ℝ) < t.1

theorem family_fibre {N : ℕ} (hN : 1 < N) (e : Bool) (m : ℕ) :
    ((family N e).layerFibre m).card ≤ layerBound := by
  apply (card_le_card (s := (family N e).layerFibre m)
    (t := (LastPrimeFour.family N e).layerFibre m) ?_).trans (fibre_card_le hN e m)
  intro t ht
  obtain ⟨ht,hm⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨(mem_filter.mp ht).1,hm⟩

theorem R1_paid {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool, ∀ Z : ℝ,
      (family N e).R1 (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ ε*N/log N^2 := by
  obtain ⟨C,hC,T1,hT1,hd⟩ := LabelledPhysical.Family.R1_log_saving_of_card.{0}
    3 truncatedSixthLowerAlpha 1 layerBound (by norm_num)
    (by norm_num [truncatedSixthLowerAlpha]) (by norm_num) hδ
  obtain ⟨T2,hT2,hpay⟩ := ninth_log_cube_error_budget hC hε
  refine ⟨max T1 T2,hT2.trans (le_max_right _ _),?_⟩
  intro N hN e Z
  have hn : 1 < N := by omega
  have hh := hd N ((le_max_left _ _).trans hN) Index (family N e)
    (family_fibre hn e)
    (fun t ht => label_balanced hn (mem_filter.mp ht).1)
    (fun _ _ => le_rfl) Z
  rw [show (3 : ℝ)=((3 : ℕ) : ℝ) by norm_num,rpow_natCast] at hh
  exact hh.trans (hpay N ((le_max_right _ _).trans hN))

theorem R2_le (N : ℕ) (e : Bool) (D : ℕ) (Z : ℝ) :
    (family N e).R2 D Z ≤ fourR2 N e D Z := by
  rw [fourR2_eq]
  exact (LastPrimeFour.family N e).restrictLabels_R2_le _ D Z

/-- The a=N^(1/10) integer atom stays on the small side. No endpoint is discarded. -/
theorem high_output_maps (N : ℕ) (e : Bool) (Z : ℝ) :
    Set.MapsTo LastPrimeFour.switch
      ((large N e).filter fun x => ¬(fourOutput N x : ℝ)<Z)
      ((family N e).labels.sigma fun t => ((family N e).primes t).filter
        fun d => Sifted N (N-(family N e).cofactor t*d) Z) := by
  rintro ⟨⟨a,b,c,d⟩,n⟩ hx
  obtain ⟨hx,hZ⟩ := mem_filter.mp hx
  obtain ⟨hx,ha⟩ := mem_filter.mp hx
  obtain ⟨ht,hd⟩ := mem_sigma.mp (original_maps hx)
  obtain ⟨hd,hprime⟩ := mem_filter.mp hd
  have hid : fourOutput N ⟨(a,b,c,d),n⟩ = N-cofactor (a,b,c,n)*d := by
    unfold fourOutput fourModulusProduct cofactor
    congr 1
    ring
  rw [hid] at hZ
  exact mem_sigma.mpr ⟨mem_filter.mpr ⟨ht,lt_of_not_ge ha⟩,
    mem_filter.mpr ⟨hd,ninth_prime_sifted hprime (le_of_not_gt hZ)⟩⟩

theorem finite_upper {N D : ℕ} (hN : 1 < N) (e : Bool) (he : Even N)
    (Z : ℝ) (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    ((large N e).card : ℝ) ≤ (family N e).mass * ordinaryRosserMainSum true N 1 D Z +
      (family N e).R1 D Z + fourR2 N e D Z + fourSmallBudget Z := by
  have hhigh := card_le_card_of_injOn LastPrimeFour.switch (high_output_maps N e Z)
    switch_injective.injOn
  have hhighR : ((((large N e).filter fun x => ¬(fourOutput N x : ℝ)<Z).card : ℕ) : ℝ) ≤
      (family N e).sifted Z := by
    rw [card_sigma] at hhigh
    change _ ≤ ∑ t ∈ (family N e).labels,
      (1 : ℝ)*(((family N e).primes t).filter fun d =>
        Sifted N (N-(family N e).cofactor t*d) Z).card
    simp only [one_mul]
    exact_mod_cast hhigh
  have hlo : (((large N e).filter fun x => (fourOutput N x : ℝ)<Z).card : ℝ) ≤ fourSmallBudget Z := by
    apply le_trans _ (fourSmallLabels_card_le hN e Z)
    exact_mod_cast card_le_card (filter_subset_filter _ (filter_subset _ _))
  have hsplit : ((((large N e).filter fun x => (fourOutput N x : ℝ)<Z).card : ℕ) : ℝ)+
      (((large N e).filter fun x => ¬(fourOutput N x : ℝ)<Z).card : ℝ) = (large N e).card := by
    exact_mod_cast card_filter_add_card_filter_not (s := large N e) (fun x => (fourOutput N x : ℝ)<Z)
  have hu := (family N e).upper_finite he D Z hD hZ
  have hr := R2_le N e D Z
  linarith only [hhighR,hlo,hsplit,hu,hr]

theorem all_errors_paid {δ ε : ℝ} (hδ : 0 < δ) (hδu : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool,
      (family N e).R1 (⌊(N : ℝ)^(1/2-δ)⌋₊+1) (sqrt ((N : ℝ)^(1/2-δ))) +
      fourR2 N e (⌊(N : ℝ)^(1/2-δ)⌋₊+1) (sqrt ((N : ℝ)^(1/2-δ))) +
      fourSmallBudget (sqrt ((N : ℝ)^(1/2-δ))) ≤ ε*N/log N^2 := by
  obtain ⟨T1,hT1,h1⟩ := R1_paid hδ (show 0 < ε/3 by positivity)
  obtain ⟨T2,_,h2⟩ := fourR2_error_paid (show 0 < ε/3 by positivity)
  obtain ⟨T3,_,h3⟩ := fourSmall_error_paid (show 0 < ε/3 by positivity)
  refine ⟨max T1 (max T2 T3),hT1.trans (le_max_left _ _),?_⟩
  intro N hN e
  have hp1 := h1 N ((le_max_left _ _).trans hN) e (sqrt ((N : ℝ)^(1/2-δ)))
  have hp2 := h2 N ((le_max_left T2 T3).trans ((le_max_right _ _).trans hN)) e δ hδ hδu
  have hp3 := h3 N ((le_max_right T2 T3).trans ((le_max_right _ _).trans hN)) δ hδ
  calc
    _ ≤ ε/3*N/log N^2 + ε/3*N/log N^2 + ε/3*N/log N^2 :=
      add_le_add (add_le_add hp1 hp2) hp3
    _ = _ := by ring

/-- Restricted literal source at fixed delta, before taking any density limit. -/
theorem source_error_paid {δ ρ ε : ℝ} (hδ : 0 < δ) (hδu : δ < 1/2)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ e : Bool,
      ((large N e).card : ℝ) ≤
        (fourDensityCoefficient δ ρ*wuSingularSeries N/log N)*(family N e).mass + ε*N/log N^2 := by
  obtain ⟨T1,_,h1⟩ := omega3_source_rosser_density hδ hδu hρ
  obtain ⟨T2,hT2,h2⟩ := all_errors_paid hδ hδu hε
  refine ⟨max T1 T2,hT2.trans (le_max_right _ _),?_⟩
  intro N hN he e
  have hN2 := (le_max_right T1 T2).trans hN
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδu
  have hu := finite_upper (by omega) e he (sqrt ((N : ℝ)^(1/2-δ)))
    hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hm : 0 ≤ (family N e).mass := sum_nonneg (fun _ _ => by
    change (0 : ℝ) ≤ 1*(_ : ℕ)
    positivity)
  have hd := mul_le_mul_of_nonneg_left (h1 N ((le_max_left _ _).trans hN) he) hm
  change (family N e).mass * _ ≤ (family N e).mass *
    (fourDensityCoefficient δ ρ*wuSingularSeries N/log N) at hd
  have hp := h2 N hN2 e
  nlinarith only [hu,hd,hp]

/-- Correct coefficient eight on the actual large-prime mass, not the old whole
alpha-domain mass. Density parameters are selected before the common threshold. -/
theorem coefficient_eight {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ e : Bool,
      ((large N e).card : ℝ) ≤ ((8+ε)*wuSingularSeries N/log N)*(family N e).mass +
        ε*(wuSingularSeries N*N/log N^2) := by
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨d,hd,hdu,hcoef⟩ := four_density_parameters hε
  obtain ⟨T,hT,hu⟩ := source_error_paid hd hdu hd (mul_pos hε hC1)
  refine ⟨T,hT,?_⟩
  intro N hN he e
  have hNp : 0 < N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N hNp
  have hm : 0 ≤ (family N e).mass := sum_nonneg (fun _ _ => by
    change (0 : ℝ) ≤ 1*(_ : ℕ)
    positivity)
  have hmain := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hC.le) hlog.le) hm
  have hClow := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ)) hNp (one_dvd N)
  have herr : (ε*wuSingularSeries 1)*N/log N^2 ≤ ε*(wuSingularSeries N*N/log N^2) := by
    calc
      _ ≤ (ε*wuSingularSeries N)*N/log N^2 := by gcongr
      _ = _ := by ring
  exact (hu N hN he e).trans (add_le_add hmain herr)

#print axioms coefficient_eight
end Wu08FirstPrimeFour.Large
