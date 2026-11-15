import HodgeLean.Foundations.Program.SchoenTransferQ3SupportCoordinateSquare

/-! One actual ambient tangential map with etale restrictions on both supports. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual support square supplies a single ambient coordinate map
whose target and source support restrictions are both etale. -/
theorem s4_q3_shared_support_coordinate_morphisms
    {C D X W : Over (Spec ↧ℂ)} (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    (f : C ⟶ D) [Etale f.left] (i : C ⟶ X) (j : D ⟶ W)
    [IsClosedImmersion j.left] (q : X ⟶ W) (hsquare : i ≫ q = f ≫ j) (p : C.left) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (_ : j.left (f.left p) ∈ U)
      (g : Fin r → Γ(W.left, U)) (V : D.left.Opens) (_ : f.left p ∈ V)
      (hVU : V ≤ j.left ⁻¹ᵁ U)
      (hCi : f.left ⁻¹ᵁ V ≤ i.left ⁻¹ᵁ (q.left ⁻¹ᵁ U)),
      Etale (j.left.resLE U V hVU ≫ s4_q3_tangentialCoordinateMorphism W U r g) ∧
      Etale (i.left.resLE (q.left ⁻¹ᵁ U) (f.left ⁻¹ᵁ V) hCi ≫
        (q.left ∣_ U) ≫ s4_q3_tangentialCoordinateMorphism W U r g) := by
  obtain ⟨U, hU, hpU, g, V, hpV, hVU, htarget⟩ :=
    s4_q3_support_coordinate_square_etale r j (f.left p)
  have hleft : i.left ≫ q.left = f.left ≫ j.left := congrArg Over.Hom.left hsquare
  have hCi : f.left ⁻¹ᵁ V ≤ i.left ⁻¹ᵁ (q.left ⁻¹ᵁ U) := by
    intro y hy
    change (i.left ≫ q.left) y ∈ U
    rw [hleft]
    exact hVU hy
  refine ⟨U, hU, hpU, g, V, hpV, hVU, hCi, htarget, ?_⟩
  have hcomm : i.left.resLE (q.left ⁻¹ᵁ U) (f.left ⁻¹ᵁ V) hCi ≫ (q.left ∣_ U) =
      (f.left ∣_ V) ≫ j.left.resLE U V hVU := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
      morphismRestrict_ι_assoc]
    rw [hleft]
  rw [← Category.assoc, hcomm, Category.assoc]
  letI := htarget
  infer_instance

end HodgeLean.Foundations.Program
