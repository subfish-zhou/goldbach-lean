import MathlibNt.SieveTheory.LiLiuGoldbachG11EffectiveProductSupport
import MathlibNt.SieveTheory.LiuPanPrincipalPNT

open scoped BigOperators Topology
open Finset Filter
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.PanPrincipal

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG11PiLiHi (N m : ℕ) : ℝ :=
  min (m.minFac : ℝ) ((N : ℝ) / m)

noncomputable def goldbachG11PiLiLo (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  min (goldbachG11PiLiHi N m) (max ((N : ℝ) ^ (4 / 53 : ℝ)) (ε * N / m))


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig