import MathlibNt.Wu2008DoubleSieve.SingleUpperHCoarseChoice

namespace Wu2008DoubleSieve.SingleUpperHFineCoarse
open Finset Set Real LiLiuPrereqBuchstab
open SingleUpperHSource SingleUpperHPacking SingleUpperHCoarseEnvelope
open SingleUpperHCoarseLimit SingleUpperLowQuadrature
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- All nodes of the n+1-cell coarse partition, including its last endpoint. -/
noncomputable def fullGrid (δ : ℝ) (n : ℕ) : Finset ℝ :=
  (range (n+2)).image (coarseNode δ n)

theorem fullGrid_anchor (δ : ℝ) (n : ℕ) :
    truncatedSixthLowerAlpha/2 ∈ fullGrid δ n := by
  exact mem_image.mpr ⟨0,mem_range.mpr (by omega),node_zero δ n⟩

theorem fullGrid_legal {δ : ℝ} (hδhi : δ ≤ 1/100) (n : ℕ) :
    ∀ q ∈ fullGrid δ n, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2 := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
  exact node_mem hδhi (by have := mem_range.mp hi; omega)

/-- Exact finite reboxing domination. Fine cells remain half-open and disjoint;
closed coarse endpoint repetitions only enlarge the nonnegative upper sum. -/
theorem fine_sum_le {δ η Δ a : ℝ} {n m N : ℕ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 ≤ η)
    (hN : 2 ≤ N) (hΔ : 1 < Δ)
    (ha : truncatedSixthLowerAlpha/2 ≤ a)
    (had : truncatedSixthLowerAlpha-coarseMesh δ n ≤ a)
    (hend : gamma5GainPoint N Δ a m ≤ (1/2-δ)/2)
    (hstep : gamma5GainStep N Δ ≤ coarseMesh δ n) :
    (∑ j ∈ range m, ∑ p ∈ primeWindow N
      ((N : ℝ)^gamma5GainPoint N Δ a j)
      ((N : ℝ)^gamma5GainPoint N Δ a (j+1)),
      (effective δ (argument δ (sample (fullGrid δ n) (gamma5GainPoint N Δ a j)))+η) *
        (1/((p : ℝ)*((1/2-δ)-log p/log N)))) ≤ coarsePrimeMass δ η n N := by
  let P := fun i => primesIcc ((N : ℝ)^(clippedNode δ n i))
    ((N : ℝ)^(clippedNode δ n (i+1)))
  let c := fun i => effective δ (argument δ (coarseNode δ n (i-1)))+η
  let w := fun p : ℕ => 1/((p : ℝ)*((1/2-δ)-log p/log N))
  let g := fun p => ∑ i ∈ range (n+1), if p ∈ P i then c i*w p else 0
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hm := (gamma5Gain_point_strictMono hNr hΔ a).monotone
  have haj (j : ℕ) : a ≤ gamma5GainPoint N Δ a j := by
    simpa only [gamma5GainPoint,Nat.cast_zero,zero_mul,add_zero] using hm (Nat.zero_le j)
  have hc (i : ℕ) (hi : i ∈ range (n+1)) : 0 ≤ c i :=
    add_nonneg (effective_slab_nonneg hδ hδhi (node_mem hδhi
      (by have := mem_range.mp hi; omega))) hη
  have hpw (i : ℕ) (hi : i ∈ range (n+1)) (p : ℕ) (hp : p ∈ P i) : 0 ≤ w p := by
    have ht := closed_coordinate hN hp
    have htop : clippedNode δ n (i+1) ≤ (1/2-δ)/2 := by
      apply max_le _ (node_mem hδhi (by have := mem_range.mp hi; omega)).2
      exact had.trans ((haj m).trans hend)
    have hpp := (mem_primesIcc (rpow_nonneg hN0.le _)).mp hp
    dsimp [w]
    apply div_nonneg (by norm_num)
    exact mul_nonneg (Nat.cast_nonneg p) (by linarith [ht.2])
  have hterm (i : ℕ) (hi : i ∈ range (n+1)) (p : ℕ) :
      0 ≤ (if p ∈ P i then c i*w p else 0) := by
    split_ifs with hp
    · exact mul_nonneg (hc i hi) (hpw i hi p hp)
    · exact le_rfl
  have hpoint (j : ℕ) (hj : j ∈ range m) (p : ℕ)
      (hp : p ∈ primeWindow N ((N : ℝ)^gamma5GainPoint N Δ a j)
        ((N : ℝ)^gamma5GainPoint N Δ a (j+1))) :
      (effective δ (argument δ (sample (fullGrid δ n) (gamma5GainPoint N Δ a j)))+η)*w p ≤ g p := by
    have hjm : j+1 ≤ m := by have := mem_range.mp hj; omega
    have ht := closed_coordinate hN (window_subset_closed hp)
    have htlo := ha.trans ((haj j).trans ht.1)
    have hthi := ht.2.trans ((hm hjm).trans hend)
    obtain ⟨i,hi,hlo,hhi⟩ := point_cover (mesh_pos hδhi n) (by omega : 0 < n+1)
      htlo (by change log (p : ℝ)/log N ≤ coarseNode δ n (n+1); simpa only [node_end] using hthi)
    have hlag := lagged_sample_le hδ hδhi (mesh_pos hδhi n)
      (by change coarseNode δ n (n+1) ≤ (1/2-δ)/2; rw [node_end])
      (mem_range.mp hi) (ha.trans (haj j)) ht.1
      (show log (p : ℝ)/log N-gamma5GainPoint N Δ a j ≤ coarseMesh δ n by
        have he : gamma5GainPoint N Δ a (j+1) = gamma5GainPoint N Δ a j + gamma5GainStep N Δ := by
          simp only [gamma5GainPoint,Nat.cast_add,Nat.cast_one]; ring
        linarith [ht.2]) hlo hhi
    have hpi : p ∈ P i := by
      apply (mem_primesIcc (rpow_nonneg hN0.le _)).mpr
      refine ⟨(mem_primeWindow.mp hp).1,?_,?_⟩
      · have htclip : clippedNode δ n i ≤ log (p : ℝ)/log N :=
          max_le (had.trans ((haj j).trans ht.1)) hlo
        have hlog := (le_div_iff₀ (log_pos hNr)).mp htclip
        rw [← log_rpow hN0] at hlog
        exact (log_le_log_iff (rpow_pos_of_pos hN0 _) (by exact_mod_cast (mem_primeWindow.mp hp).1.pos)).mp hlog
      · have htclip : log (p : ℝ)/log N ≤ clippedNode δ n (i+1) :=
          hhi.trans (le_max_right _ _)
        have hlog := (div_le_iff₀ (log_pos hNr)).mp htclip
        rw [← log_rpow hN0] at hlog
        exact (log_le_log_iff (by exact_mod_cast (mem_primeWindow.mp hp).1.pos) (rpow_pos_of_pos hN0 _)).mp hlog
    have hh : (effective δ (argument δ (sample (fullGrid δ n) (gamma5GainPoint N Δ a j)))+η)*w p ≤ c i*w p :=
      mul_le_mul_of_nonneg_right (by
        change effective δ (argument δ (sample (fullGrid δ n) (gamma5GainPoint N Δ a j))) ≤
          effective δ (argument δ (coarseNode δ n (i-1))) at hlag
        exact add_le_add hlag (le_refl η)) (hpw i hi p hpi)
    apply hh.trans
    have hs := single_le_sum (fun k hk => hterm k hk p) hi
    simpa only [if_pos hpi] using hs
  calc
    _ ≤ ∑ j ∈ range m, ∑ p ∈ primeWindow N
        ((N : ℝ)^gamma5GainPoint N Δ a j)
        ((N : ℝ)^gamma5GainPoint N Δ a (j+1)), g p :=
      sum_le_sum (fun j hj => sum_le_sum (fun p hp => hpoint j hj p hp))
    _ = ∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a m), g p :=
      (SingleUpperLowPacking.grid_sum hN hΔ a m g).symm
    _ ≤ coarsePrimeMass δ η n N := by
      dsimp only [g]
      rw [sum_comm]
      unfold coarsePrimeMass
      apply sum_le_sum
      intro i hi
      rw [mul_sum]
      change (∑ p ∈ _, if p ∈ P i then c i*w p else 0) ≤ ∑ p ∈ P i, c i*w p
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (mem_filter.mp hp).2
      · intro p hp _
        exact mul_nonneg (hc i hi) (hpw i hi p hp)

end Wu2008DoubleSieve.SingleUpperHFineCoarse
