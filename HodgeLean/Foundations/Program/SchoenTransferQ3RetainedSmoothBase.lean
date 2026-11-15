import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedTangentialMaps
import HodgeLean.Foundations.Program.SchoenTransferQ3SmoothRefinement

/-! One shared dense smooth base for the actual ambient tangential maps. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- The actual ambient tangential morphism and its actual composite with q
are smooth over one common dense base open. -/
theorem s4_q3_retained_shared_smooth_tangential_base
    {C D X W : Over (Spec ↧ℂ)} (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    [IsIntegral X.left] [Smooth X.hom] [IsIntegral W.left] [Smooth W.hom]
    (f : C ⟶ D) [Etale f.left] (i : C ⟶ X) (j : D ⟶ W)
    [IsClosedImmersion j.left] (q : X ⟶ W) [IsFinite q.left]
    (hsquare : i ≫ q = f ≫ j) (p : C.left) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (_ : j.left (f.left p) ∈ U)
      (g : Fin r → Γ(W.left, U)) (V : D.left.Opens) (_ : f.left p ∈ V)
      (hVU : V ≤ j.left ⁻¹ᵁ U)
      (hCi : f.left ⁻¹ᵁ V ≤ i.left ⁻¹ᵁ (q.left ⁻¹ᵁ U)),
      let h := s4_q3_tangentialCoordinateMorphism W U r g
      Etale (j.left.resLE U V hVU ≫ h) ∧
      Etale (i.left.resLE (q.left ⁻¹ᵁ U) (f.left ⁻¹ᵁ V) hCi ≫ (q.left ∣_ U) ≫ h) ∧
      IsDominant h ∧ IsDominant ((q.left ∣_ U) ≫ h) ∧
      ∃ A : (ComplexPoint.complexAffineSpace (Fin r)).Opens,
        Dense (A : Set (ComplexPoint.complexAffineSpace (Fin r))) ∧
        Smooth (h ∣_ A) ∧ Smooth (((q.left ∣_ U) ≫ h) ∣_ A) := by
  obtain ⟨U, hU, hpU, g, V, hpV, hVU, hCi, ht, hs, hdW, hdX, A, B, hA, hB, hsW, hsX⟩ :=
    s4_q3_retained_generic_tangential_maps r f i j q hsquare p
  refine ⟨U, hU, hpU, g, V, hpV, hVU, hCi, ht, hs, hdW, hdX, A ⊓ B,
    hA.inter_of_isOpen_right hB B.isOpen, ?_, ?_⟩
  · exact s4_q3_smooth_restriction_mono _ A (A ⊓ B) inf_le_left hsW
  · exact s4_q3_smooth_restriction_mono _ B (A ⊓ B) inf_le_right hsX

end HodgeLean.Foundations.Program
