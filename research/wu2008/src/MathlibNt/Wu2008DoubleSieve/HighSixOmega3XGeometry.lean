import MathlibNt.Wu2008DoubleSieve.HighSixOmega3Remainders
import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabSource

namespace Wu2008DoubleSieve.HighSix.Omega3Upper
open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

/-- Compact geometry on the actual ordered triples, without a source box. -/
theorem X_triple_geometry {N d p1 p2 p3 : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hd : d ∈ P N)
    (hp : (p1,p2,p3) ∈ omega3XPrimes N δ s S d) :
    0 < omega3XScale N d p1 p2 p3 ∧ (2 : ℝ) ≤ p2 ∧
    (p2 : ℝ) < omega3XScale N d p1 p2 p3 ∧
    (N : ℝ)^(1/25 : ℝ) ≤ p2 ∧
    (N : ℝ)^(1/25 : ℝ) ≤ omega3XScale N d p1 p2 p3 ∧
    omega3XScale N d p1 p2 p3 ≤ N ∧
    1+4*δ/(1/2-δ) < log (omega3XScale N d p1 p2 p3)/log p2 ∧
    log (omega3XScale N d p1 p2 p3)/log p2 ≤ 25 := by
  obtain ⟨hp2,hp1,_,hp3,h23,h3s⟩ := mem_omega3XPrimes.mp hp
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have hdpos := (mem_primeWindow.mp hd).1.pos
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have h10 : (0 : ℝ) < p1 := by exact_mod_cast h1.1.pos
  have h21 : (1 : ℝ) < p2 := by exact_mod_cast h2.1.one_lt
  have h20 : (0 : ℝ) < p2 := by positivity
  have hd0 : (0 : ℝ) < d := by linarith
  have h30 : (0 : ℝ) < p3 := by exact_mod_cast hp3.pos
  have hc : 0 < 1/2-δ := by linarith
  have hx : 0 < omega3XScale N d p1 p2 p3 := by unfold omega3XScale; positivity
  have hcut : wuLocalCutoff N δ d s ≤ (R N δ d)^(1/2 : ℝ) :=
    rpow_le_rpow_of_exponent_le (ratio_bounds hN hδ hδhi hd).1.le (by norm_num [s])
  have hgap := omega3X_log_gap hN1 hd1 h10 h21 h1.2.2.2
    (by exact_mod_cast h23) (h3s.trans hcut) hδ (show δ < 1/2 by linarith)
  change 1+4*δ/(1/2-δ) < log (omega3XScale N d p1 p2 p3)/log p2 at hgap
  have hlog2 : 0 < log (p2 : ℝ) := log_pos h21
  have hg0 : 0 < 4*δ/(1/2-δ) := by positivity
  have hxy : (p2 : ℝ) < omega3XScale N d p1 p2 p3 := by
    have hu : 1 < log (omega3XScale N d p1 p2 p3)/log p2 := by linarith
    have hl : log (p2 : ℝ) < log (omega3XScale N d p1 p2 p3) := by
      simpa only [one_mul] using (lt_div_iff₀ hlog2).mp hu
    exact (log_lt_log_iff h20 hx).mp hl
  have hyg := (inner_lower_cutoff hN hδ hδhi hd).trans h2.2.2.1
  have hden : 1 ≤ (d : ℝ)*p1*p2*p3 := by
    have hn : 1 ≤ d*p1*p2*p3 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos h1.1.pos) h2.1.pos) hp3.pos
    exact_mod_cast hn
  have hxN : omega3XScale N d p1 p2 p3 ≤ N := div_le_self hN0.le hden
  have hlowlog := log_le_log (rpow_pos_of_pos hN0 _) hyg
  rw [log_rpow hN0] at hlowlog
  have hhighlog := log_le_log hx hxN
  refine ⟨hx,by exact_mod_cast h2.1.two_le,hxy,hyg,hyg.trans hxy.le,hxN,hgap,?_⟩
  apply (div_le_iff₀ hlog2).mpr
  linarith

/-- Actual x and y grow uniformly before the ordered prime labels. -/
theorem X_buchstab_uniform {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ d ∈ P N,
      ∀ p ∈ omega3XPrimes N δ s S d,
        let x := omega3XScale N d p.1 p.2.1 p.2.2
        let y := (p.2.1 : ℝ)
        let B := x*buchstab (log x/log y)/log y
        primeErrorStart ≤ y ∧ 0 < B ∧ |(roughCount x y : ℝ)-B| ≤ ε*(x/log y) := by
  let u0 : ℝ := 1+2*δ/(1/2-δ)
  have hc : 0 < 1/2-δ := by linarith
  have hu0 : 1 < u0 := by
    have hp : 0 < 2*δ/(1/2-δ) := by positivity
    dsimp [u0]
    linarith
  obtain ⟨X,_,hX⟩ := roughCount_uniform_buchstab_fixed 26 (by norm_num) hu0 hε
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show (0 : ℝ) < 1/25 by norm_num)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max X primeErrorStart)))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN d hd p hp
  obtain ⟨_,hy,hyx,hyg,hxg,_,hgap,hcap⟩ := X_triple_geometry (by omega) hδ hδhi hd hp
  have hu : log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1 ∈ Set.Icc u0 (26 : ℝ) := by
    constructor
    · dsimp [u0]
      have : 0 ≤ 2*δ/(1/2-δ) := by positivity
      have he : 4*δ/(1/2-δ) = 2*(2*δ/(1/2-δ)) := by ring
      rw [he] at hgap
      linarith
    · linarith
  have hgrowth := hT N (by omega)
  have hxX := ((le_max_left X primeErrorStart).trans hgrowth).trans hxg
  have hyStart := ((le_max_right X primeErrorStart).trans hgrowth).trans hyg
  have hy1 : (1 : ℝ) < p.2.1 := by linarith
  obtain ⟨_,_,_,hcoord,hnorm⟩ := omega3X_buchstab_coordinates hy1 hyx.le
  obtain ⟨hpos,hrel⟩ := hX _ hxX _ hu
  rw [← hcoord,hnorm] at hrel
  rw [hnorm] at hpos
  refine ⟨hyStart,hpos,?_⟩
  let B := omega3XScale N d p.1 p.2.1 p.2.2*
    buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1)/log p.2.1
  have heq : (roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)/B-1 =
      ((roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)-B)/B := by
    have hB : B ≠ 0 := hpos.ne'
    field_simp
  change |(roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)/B-1| < ε at hrel
  rw [heq,abs_div,abs_of_pos hpos] at hrel
  exact ((div_lt_iff₀ hpos).mp hrel).le.trans
    (mul_le_mul_of_nonneg_left (omega3X_buchstab_main_term_bounds hy1 hyx.le).2 hε.le)

/-- All three ordered coordinates lie in the same growing prime interval. -/
theorem X_prime_interval {N d : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hd : d ∈ P N)
    {p : ℕ × ℕ × ℕ} (hp : p ∈ omega3XPrimes N δ s S d) :
    p.1 ∈ primesIcc ((N : ℝ)^(1/25 : ℝ)) N ∧
    p.2.1 ∈ primesIcc ((N : ℝ)^(1/25 : ℝ)) N ∧
    p.2.2 ∈ primesIcc ((N : ℝ)^(1/25 : ℝ)) N := by
  rcases p with ⟨p1,p2,p3⟩
  obtain ⟨hp2,hp1,hp3N,hp3,h23,_⟩ := mem_omega3XPrimes.mp hp
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have h12 : p1 < p2 := by exact_mod_cast h1.2.2.2
  have hlow := inner_lower_cutoff hN hδ hδhi hd
  refine ⟨(mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨h1.1,hlow.trans h1.2.2.1,?_⟩,
    (mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨h2.1,hlow.trans h2.2.2.1,?_⟩,
    (mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨hp3,?_,?_⟩⟩
  · exact_mod_cast (h12.le.trans h23.le).trans hp3N
  · exact_mod_cast h23.le.trans hp3N
  · exact (hlow.trans h2.2.2.1).trans (by exact_mod_cast h23.le)
  · exact_mod_cast hp3N

end Wu2008DoubleSieve.HighSix.Omega3Upper
