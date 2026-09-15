import HighO3Geometry

namespace HighO3
open Finset Real Wu2008DoubleSieve HighBoxRecovery HighTheta Filter LiLiuPrereqBuchstab
open scoped Classical Topology
noncomputable section

theorem prime_interval {N d : ℕ} {δ η s t : ℝ} (hN : 2 ≤ N) (hd : 0 < d)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    {p : ℕ × ℕ × ℕ} (hp : p ∈ omega3XPrimes N δ s t d) :
    p.1 ∈ primesIcc ((N : ℝ)^η) N ∧ p.2.1 ∈ primesIcc ((N : ℝ)^η) N ∧
      p.2.2 ∈ primesIcc ((N : ℝ)^η) N := by
  obtain ⟨hp2,hp1,hp3N,hp3,h23,_⟩ := mem_omega3XPrimes.mp hp
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have hg := support_bounds hN hd hδ hδhi hη hsize hs hst ht
  have h12 : p.1 < p.2.1 := by exact_mod_cast h1.2.2.2
  have hlo1 := hg.2.2.2.2.1.trans h1.2.2.1
  have hlo2 := hg.2.2.2.2.1.trans h2.2.2.1
  exact ⟨(mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨h1.1,hlo1,by exact_mod_cast (h12.le.trans h23.le).trans hp3N⟩,
    (mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨h2.1,hlo2,by exact_mod_cast h23.le.trans hp3N⟩,
    (mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨hp3,hlo2.trans (by exact_mod_cast h23.le),by exact_mod_cast hp3N⟩⟩

theorem atom_geometry {N d : ℕ} {δ η s t : ℝ} (hN : 2 ≤ N) (hd : 0 < d)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    {p : ℕ × ℕ × ℕ} (hp : p ∈ omega3XPrimes N δ s t d) :
    let x := omega3XScale N d p.1 p.2.1 p.2.2
    let y := (p.2.1 : ℝ)
    0 < x ∧ 2 ≤ y ∧ y ≤ x ∧ (N : ℝ)^η ≤ y ∧ (N : ℝ)^η ≤ x ∧ x ≤ N ∧
      1+4*δ/(1/2-δ) < log x/log y ∧ log x/log y ≤ 1/η := by
  obtain ⟨hp2,hp1,_,hp3,h23,h3s⟩ := mem_omega3XPrimes.mp hp
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have hg := support_bounds hN hd hδ hδhi hη hsize hs hst ht
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h10 : (0 : ℝ) < p.1 := by exact_mod_cast h1.1.pos
  have h21 : (1 : ℝ) < p.2.1 := by exact_mod_cast h2.1.one_lt
  have h20 : (0 : ℝ) < p.2.1 := by linarith
  have h30 : (0 : ℝ) < p.2.2 := by exact_mod_cast hp3.pos
  have hx : 0 < omega3XScale N d p.1 p.2.1 p.2.2 := by unfold omega3XScale; positivity
  have hgap := omega3X_log_gap hN1 hd1 h10 h21 h1.2.2.2
    (by exact_mod_cast h23) (h3s.trans hg.2.2.2.2.2) hδ hδhi
  change 1+4*δ/(1/2-δ) < log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1 at hgap
  have hlog2 : 0 < log (p.2.1 : ℝ) := log_pos h21
  have hg0 : 0 < 4*δ/(1/2-δ) := by positivity
  have hxy : (p.2.1 : ℝ) < omega3XScale N d p.1 p.2.1 p.2.2 := by
    have hu : 1 < log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1 := by linarith
    have hl : log (p.2.1 : ℝ) < log (omega3XScale N d p.1 p.2.1 p.2.2) := by
      simpa only [one_mul] using (lt_div_iff₀ hlog2).mp hu
    exact (log_lt_log_iff h20 hx).mp hl
  have hyg := hg.2.2.2.2.1.trans h2.2.2.1
  have hden : 1 ≤ (d : ℝ)*p.1*p.2.1*p.2.2 := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd h1.1.pos) h2.1.pos) hp3.pos
  have hxN : omega3XScale N d p.1 p.2.1 p.2.2 ≤ N := div_le_self hN0.le hden
  have hlo := log_le_log (rpow_pos_of_pos hN0 _) hyg
  rw [log_rpow hN0] at hlo
  have hhi := log_le_log hx hxN
  have hu : log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1 ≤ 1/η := by
    apply (div_le_iff₀ hlog2).mpr
    calc
      _ ≤ log (N : ℝ) := hhi
      _ ≤ log (p.2.1 : ℝ)/η := (le_div_iff₀ hη).mpr (by nlinarith)
      _ = _ := by ring
  exact ⟨hx,by exact_mod_cast h2.1.two_le,hxy.le,hyg,hyg.trans hxy.le,hxN,hgap,hu⟩

/-- Fixed reciprocal-prime budget; no sampling of the prime atoms. -/
theorem scale_mass {N d : ℕ} {δ η s t : ℝ} (hN : 2 ≤ N) (hd : 0 < d)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (hstart : primeErrorStart ≤ (N : ℝ)^η) :
    (∑ p ∈ omega3XPrimes N δ s t d,omega3XScale N d p.1 p.2.1 p.2.2/log p.2.1) ≤
      ((5/η)^3/η)*((N : ℝ)/d/log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsum := omega3X_prime_triple_reciprocal_le hN hη hstart (omega3XPrimes N δ s t d)
    (fun p hp => prime_interval hN hd hδ hδhi hη hsize hs hst ht hp)
  calc
    _ ≤ ∑ p ∈ omega3XPrimes N δ s t d,
        ((N : ℝ)/d/(η*log N))*(1/((p.1 : ℝ)*p.2.1*p.2.2)) := by
      apply sum_le_sum
      intro p hp
      have hP := prime_interval hN hd hδ hδhi hη hsize hs hst ht hp
      have hlo := ((mem_primesIcc hN0.le).mp hP.2.1).2.1
      have hl := log_le_log (rpow_pos_of_pos hN0 _) hlo
      rw [log_rpow hN0] at hl
      calc
        _ ≤ omega3XScale N d p.1 p.2.1 p.2.2/(η*log N) :=
          div_le_div_of_nonneg_left (by unfold omega3XScale; positivity) (mul_pos hη hlogN) hl
        _ = _ := by unfold omega3XScale; ring
    _ = ((N : ℝ)/d/(η*log N))*∑ p ∈ omega3XPrimes N δ s t d,1/((p.1 : ℝ)*p.2.1*p.2.2) := (mul_sum ..).symm
    _ ≤ ((N : ℝ)/d/(η*log N))*(5/η)^3 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end
end HighO3
