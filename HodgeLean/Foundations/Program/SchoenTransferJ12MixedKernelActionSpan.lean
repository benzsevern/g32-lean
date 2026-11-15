import HodgeLean.Foundations.Program.SchoenTransferJ12PullbackKernelSpan
import HodgeLean.Foundations.Program.SchoenTransferJ12MixedKernelPullback
import HodgeLean.Foundations.Program.SchoenTransferJ12PointTopCoordinate
import HodgeLean.Foundations.Program.SchoenTransferE1Proofs
import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Foundations.SegreProjective

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Actual mixed divisor product kernels preserve source cycles through the specified abelian power.
Source: the product of the actual source maps, normalized graph transfer and abelian kernel algebraicity. -/
theorem s4_selected_mixed_divisor_kernel_action_span
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : TopologicalSpace.dim A.left = a) (hY : TopologicalSpace.dim Y.left = d)
    (n p q : ℕ) (h : n + p = d + q) (hlarge : d ≤ n * a + p)
    (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (f : Fin n → (Y ⟶ A))
    (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1)
    (b : HQ Y (2 * p)) (hb : b ∈ cfd_cycleSpan Y p) :
    s4_selected_corr_action A Y d IY n (2 * p) (2 * q) (by omega)
      (s4_selected_mixed_divisor_kernel A Y n f pol) b ∈ cfd_cycleSpan A q := by
  let B := g3_power A n
  let D := n * a
  have hB : TopologicalSpace.dim B.left = D := by
    letI : SmoothOfRelativeDimension a A.hom := by
      have h := SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
      rwa [hA] at h
    letI : SmoothOfRelativeDimension D B.hom := spec_g3_smoothOfRelativeDimension_power A a n
    exact SmoothOfRelativeDimension.dim_eq (f := B.hom) D
  letI := connectedSpace_complexPoint B
  let e : ComplexPoint B := Classical.choice inferInstance
  obtain ⟨hec, IB, he⟩ := s4_selected_point_top_coordinate B D hB e
  let g : Y ⟶ B := s2_lift n f
  let s := D + p - d
  have hlarge' : d ≤ D + p := hlarge
  have hshift : D + p = d + s := by dsimp only [s]; omega
  have hkernel : n + s = D + q := by omega
  have hp := s4_selected_pullback_kernel_action_span A B Y D d hB hY IB IY e hec he g
    n p q s hshift hkernel (s4_selected_mixed_divisor_kernel A B n (g3_proj A n) pol)
    (s4_selected_mixed_divisor_kernel_mem A B n (g3_proj A n) pol hpol) b hb
  rw [s4_selected_mixed_divisor_kernel_pullback A B Y g n (g3_proj A n) pol] at hp
  have hl : (fun i => g ≫ g3_proj A n i) = f := by
    funext i
    exact s4_e1_lift_proj n f i
  rw [hl] at hp
  exact hp

#print axioms s4_selected_mixed_divisor_kernel_action_span
end HodgeLean.Foundations.Program
