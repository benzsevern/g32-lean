import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
import Mathlib.Analysis.Analytic.Polynomial

/-! # Regular functions in the standard affine coordinates

Localizing a polynomial section gives analytic evaluation on its domain.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Filter Topology
open AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.TubularEuler

theorem affine_regular_top_analytic (n : ℕ)
    (s : Γ(complexAffineSpace (Fin n), ⊤)) (a : Fin n → ℂ) :
    AnalyticAt ℂ (fun v => Point.evaluate ⊤ s ((affineSpaceEquiv (Fin n)).symm v)) a := by
  simp_rw [evaluate_affineSpaceEquiv_symm_top]
  exact AnalyticOnNhd.eval_mvPolynomial (affineGlobalPolynomial s) a (Set.mem_univ a)

theorem affine_regular_local_analytic (n : ℕ)
    (U : (complexAffineSpace (Fin n)).Opens) (s : Γ(complexAffineSpace (Fin n), U))
    (a : Fin n → ℂ) (ha : (affineSpaceEquiv (Fin n)).symm a ∈ Point.overOpen U) :
    AnalyticAt ℂ (fun v => Point.evaluate U s ((affineSpaceEquiv (Fin n)).symm v)) a := by
  let X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)
  have hXa : IsAffineOpen (⊤ : X.left.Opens) := by
    change IsAffineOpen (⊤ : (complexAffineSpace (Fin n)).Opens)
    exact isAffineOpen_top _
  obtain ⟨r, hrU, hra⟩ := hXa.exists_basicOpen_le
    (⟨((affineSpaceEquiv (Fin n)).symm a).underlying, ha⟩ : U) (by trivial)
  have hrne : Point.evaluate ⊤ r ((affineSpaceEquiv (Fin n)).symm a) ≠ 0 :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r _ (by trivial)).mp hra
  have hn := (affine_regular_top_analytic n r a).continuousAt.eventually_ne hrne
  have hbasic : ∀ᶠ v in 𝓝 a,
      (affineSpaceEquiv (Fin n)).symm v ∈ Point.overOpen (X.left.basicOpen r) := by
    filter_upwards [hn] with v hv
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r _ (by trivial)).mpr hv
  let sr := (X.left.presheaf.map (homOfLE hrU).op).hom s
  obtain ⟨k, p, hp⟩ := Point.exists_evaluate_basicOpen_eq_div (X := X) hXa r sr
  have hrat : AnalyticAt ℂ (fun v =>
      Point.evaluate ⊤ p ((affineSpaceEquiv (Fin n)).symm v) /
        Point.evaluate ⊤ r ((affineSpaceEquiv (Fin n)).symm v) ^ k) a :=
    (affine_regular_top_analytic n p a).div
      ((affine_regular_top_analytic n r a).pow k) (pow_ne_zero k hrne)
  apply hrat.congr
  filter_upwards [hbasic] with v hv
  rw [Point.evaluate_res hrU s _ hv]
  exact (hp _ hv).symm

end HodgeLean.Foundations.TubularEuler
