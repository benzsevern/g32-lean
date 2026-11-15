import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicGenericDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericAffineEtaleOpen
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist

/-! # Intrinsic proper degrees with an actual smooth target -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- A proper generically finite map to an actual smooth projective target carries the specified intrinsic class to its actual residue-degree multiple, with its finite etale neighborhood and testing point constructed from the map.
Source: Fulton, Intersection Theory, section 1.4; SGA 1, Expose I and Expose XII.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_proper_degree_smooth_target
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [IsProjective X.hom] [IsProjective Y.hom] (f : X ⟶ Y) [IsProper f.left]
    (d : ℕ) [SmoothOfRelativeDimension d Y.hom]
    (hdimX : topologicalKrullDim X.left = (d : ℕ))
    (hdimY : topologicalKrullDim Y.left = (d : ℕ))
    (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (hdegree : 0 < a1p_degree f.left (genericPoint X.left)) :
    homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap f))
      (properCycle_intrinsic_class X d hdimX) =
    (a1p_degree f.left (genericPoint X.left) : ℚ) • properCycle_intrinsic_class Y d hdimY := by
  obtain ⟨U, hU, hgU, hfinite, hetale⟩ :=
    properCycle_generically_finite_etale_affine_open f hg hdegree
  letI : Nonempty U := ⟨⟨genericPoint Y.left, hgU⟩⟩
  letI : Nonempty (f.left ⁻¹ᵁ U) := ⟨⟨genericPoint X.left, by
    change f.left (genericPoint X.left) ∈ U
    rwa [hg]⟩⟩
  letI : IsFinite (f.left ∣_ U) := hfinite
  letI : Etale (f.left ∣_ U) := hetale
  letI : Nonempty (openScheme Y U).left := inferInstanceAs (Nonempty U.toScheme)
  letI : LocallyOfFiniteType (openScheme Y U).hom := by
    change LocallyOfFiniteType (U.ι ≫ Y.hom)
    infer_instance
  obtain ⟨y⟩ := s2t_nonempty_complexPoints (openScheme Y U)
  exact properCycle_intrinsic_generic_open_degree_smooth_target X Y f d hdimX hdimY hg U hU y

end HodgeLean.Foundations.QuotientDuality
