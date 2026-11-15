import HodgeLean.Foundations.Program.G32Native.RetainedConormalRestriction

/-! # Independence of affine presentation for the retained conormal differential -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

/-- The actual differential on the retained conormal fibre is independent
of the affine open used to present the immersion ideal.
Source: Hartshorne, Algebraic Geometry, II, Proposition 8.12,
naturality of the conormal sequence and its fibre specialization. -/
theorem retainedAffineConormalDifferential_independent_affine_aux
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A B : X.left.Opens) (hA : IsAffineOpen A) (hB : IsAffineOpen B)
    (x : ComplexPoint Y)
    (hxA : x ∈ Point.overOpen (j.left ⁻¹ᵁ A))
    (hxB : x ∈ Point.overOpen (j.left ⁻¹ᵁ B))
    (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    retainedAffineConormalDifferential X Y j d A hA x hxA z hz =
      retainedAffineConormalDifferential X Y j d B hB x hxB z hz := by
  obtain ⟨C, hC, hxC, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (x := (Point.map j x).underlying) (U := A ⊓ B) ⟨hxA, hxB⟩
  have hCA : C ≤ A := fun y hy => (hsub hy).1
  have hCB : C ≤ B := fun y hy => (hsub hy).2
  have hxC' : x ∈ Point.overOpen (j.left ⁻¹ᵁ C) := hxC
  exact (retainedAffineConormalDifferential_restriction X Y j d A C hA hC hCA x hxA hxC' z hz).trans
    (retainedAffineConormalDifferential_restriction X Y j d B C hB hC hCB x hxB hxC' z hz).symm

#print axioms retainedAffineConormalDifferential_independent_affine_aux
end HodgeLean.Foundations.TubularEuler
