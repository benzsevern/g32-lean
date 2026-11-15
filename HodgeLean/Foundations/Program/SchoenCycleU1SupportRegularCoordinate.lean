import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import HodgeLean.Foundations.Program.SchoenCycleU1NativeAffineDifferentials
import HodgeLean.Foundations.Program.SchoenCycleU1LinearAvoidance

/-! # One regular coordinate separating and unramified on a finite support -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
namespace HodgeLean.Foundations.Program

/-- One actual affine regular function separates the prescribed finite support
and has nonzero native coordinate derivative at every support point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, affine tangent vectors;
ACGH, Geometry of Algebraic Curves I, Chapter I, local divisor coordinates. -/
theorem s2e_u1_affine_support_regular_coordinate
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    (U : Z.left.Opens) (hU : IsAffineOpen U)
    (S : Finset (ComplexPoint Z)) (hS : ∀ p ∈ S, p.underlying ∈ U) :
    ∃ s : Γ(Z.left, U),
      Set.InjOn (fun p : ComplexPoint Z => Point.evaluate U s p) S ∧
      ∀ p ∈ S, deriv (fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)) 0 ≠ 0 := by
  classical
  letI := s2e_step1_sectionAlgebra Z U
  let e (i : S) : Γ(Z.left, U) →ₐ[ℂ] ℂ := s2e_step1_pointEvaluation Z U i.val
    (s2e_step1_point_preimage Z i.val U (hS i.val i.property))
  let d (i : S) : Γ(Z.left, U) →ₗ[ℂ] ℂ := (TrivSqZeroExt.sndHom ℂ ℂ).comp
    (s2e_u1_sectionJetAlong Z U (s2e_u1_nativeCurve Z i.val)
      (s2e_u1_nativeCurve_regular_sections Z i.val U (hS i.val i.property)).1
      (s2e_u1_nativeCurve_regular_sections Z i.val U (hS i.val i.property)).2).toLinearMap
  have hd (i : S) (s : Γ(Z.left, U)) : d i s =
      deriv (fun t => Point.evaluate U s (s2e_u1_nativeCurve Z i.val t)) 0 :=
    s2e_u1_nativeSectionJet_snd Z i.val U (hS i.val i.property) s
  let I := {ij : S × S // ij.1 ≠ ij.2} ⊕ S
  let L : I → Γ(Z.left, U) →ₗ[ℂ] ℂ := Sum.elim
    (fun ij => (e ij.val.1).toLinearMap - (e ij.val.2).toLinearMap) d
  have hL (i : I) : ∃ s, L i s ≠ 0 := by
    rcases i with ij | p
    · have hne : e ij.val.1 ≠ e ij.val.2 := by
        intro h
        apply ij.property
        apply Subtype.ext
        exact s2e_step1_point_ext_on_affine Z U hU _ _ _ _ h
      by_contra hn
      have hz : ∀ s, L (Sum.inl ij) s = 0 := by
        simpa only [not_exists, not_not] using hn
      apply hne
      apply AlgHom.ext
      intro s
      exact sub_eq_zero.mp (hz s)
    · obtain ⟨s, hs⟩ := s2e_u1_affine_section_native_derivative_ne_zero
        Z p.val U hU (hS p.val p.property)
      refine ⟨s, ?_⟩
      change d p s ≠ 0
      rwa [hd]
  obtain ⟨s, hs⟩ := s2e_u1_exists_nonzero_linear_functionals L hL
  refine ⟨s, ?_, ?_⟩
  · intro x hx y hy he
    by_contra hxy
    let ij : {ij : S × S // ij.1 ≠ ij.2} :=
      ⟨(⟨x, hx⟩, ⟨y, hy⟩), fun h => hxy (congrArg Subtype.val h)⟩
    apply hs (Sum.inl ij)
    change e ⟨x, hx⟩ s - e ⟨y, hy⟩ s = 0
    dsimp only [e]
    rw [s2e_u1_pointEvaluation_eq_evaluate Z U x (hS x hx),
      s2e_u1_pointEvaluation_eq_evaluate Z U y (hS y hy)]
    exact sub_eq_zero.mpr he
  · intro p hp
    have h := hs (Sum.inr (⟨p, hp⟩ : S))
    change d ⟨p, hp⟩ s ≠ 0 at h
    rwa [hd] at h

/-- A regular section with nonzero native derivative gives an actual analytic
coordinate change with an analytic local inverse.
Source: Mathlib, `AnalyticAt.analyticAt_localInverse`; Hartshorne,
Algebraic Geometry, II.8, local coordinates on a smooth curve. -/
theorem s2e_u1_regular_coordinate_native_inverse
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z)
    (U : Z.left.Opens) (hp : p.underlying ∈ U) (s : Γ(Z.left, U))
    (hs : deriv (fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)) 0 ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r (Point.evaluate U s p) ∧
      r (Point.evaluate U s p) = 0 ∧
      (∀ᶠ t : ℂ in nhds 0,
        r (Point.evaluate U s (s2e_u1_nativeCurve Z p t)) = t) ∧
      (∀ᶠ w : ℂ in nhds (Point.evaluate U s p),
        Point.evaluate U s (s2e_u1_nativeCurve Z p (r w)) = w) := by
  let f : ℂ → ℂ := fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)
  have hf : AnalyticAt ℂ f 0 := (s2e_u1_nativeCurve_regular_sections Z p U hp).2 s
  let r := hf.hasStrictDerivAt.localInverse f (deriv f 0) 0 hs
  have hl : ∀ᶠ t : ℂ in nhds 0, r (f t) = t :=
    HasStrictDerivAt.eventually_left_inverse hf.hasStrictDerivAt hs
  have hr : ∀ᶠ w : ℂ in nhds (f 0), f (r w) = w :=
    HasStrictDerivAt.eventually_right_inverse hf.hasStrictDerivAt hs
  refine ⟨r, ?_, ?_, hl, ?_⟩
  · simpa only [f, s2e_u1_nativeCurve_zero] using hf.analyticAt_localInverse hs
  · simpa only [f, s2e_u1_nativeCurve_zero] using hl.self_of_nhds
  · simpa only [f, s2e_u1_nativeCurve_zero] using hr

end HodgeLean.Foundations.Program
