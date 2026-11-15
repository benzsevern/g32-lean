import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RetainedModelFibre
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffinePointSupport

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A generator of a retained branch ideal vanishes at the actual lifted affine base point. -/
theorem retained_affine_generator_zero
    (B : Over (Spec ↧ℂ)) (U : B.left.affineOpens) (I : B.left.IdealSheafData)
    (x : ComplexPoint B) (hx : x.left (IsLocalRing.closedPoint ℂ) ∈ I.support)
    (u : Γ(B.left, U)) (hu : I.ideal U = Ideal.span {u}) :
    letI := s2e_step1_sectionAlgebra B U.1
    ∀ xR : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap Γ(B.left, U))),
      Point.map (s2e_u1_fromSpecOver B U.1 U.2) xR = x →
      ComplexPoint.affineSpecEquiv Γ(B.left, U) xR u = 0 := by
  letI := s2e_step1_sectionAlgebra B U.1
  intro xR hxR
  have hpoint := congrArg (fun y : ComplexPoint B => y.left (IsLocalRing.closedPoint ℂ)) hxR
  change U.2.fromSpec (xR.left (IsLocalRing.closedPoint ℂ)) =
    x.left (IsLocalRing.closedPoint ℂ) at hpoint
  have hz := (Scheme.IdealSheafData.mem_support_iff.mp hx) U
  rw [hu, B.left.zeroLocus_span] at hz
  have hpre : xR.left (IsLocalRing.closedPoint ℂ) ∈
      U.2.fromSpec ⁻¹' B.left.zeroLocus ({u} : Set Γ(B.left, U)) := by
    change U.2.fromSpec (xR.left (IsLocalRing.closedPoint ℂ)) ∈
      B.left.zeroLocus ({u} : Set Γ(B.left, U))
    rw [hpoint]
    exact hz
  rw [U.2.fromSpec_preimage_zeroLocus] at hpre
  have hmem : u ∈ (xR.left (IsLocalRing.closedPoint ℂ)).asIdeal := hpre (Set.mem_singleton u)
  have he := affine_point_mem_prime_iff (ComplexPoint.affineSpecEquiv Γ(B.left, U) xR) u
  rw [Equiv.symm_apply_apply] at he
  exact he.mp hmem

end AlgebraicGeometry.RamifiedNormalization.StageFour
