import HodgeLean.Foundations.Program.G32Native.OriginalRegularConormalSpanning
import HodgeLean.Foundations.Program.G32Native.ModuleFibreCovectorExt
import HodgeLean.Foundations.Program.G32Native.OriginalRegularConormalRestriction
import HodgeLean.Foundations.Program.G32Native.RetainedAffineEquationRestriction
import HodgeLean.Foundations.Program.G32Native.RetainedRestrictedEquationValues

/-! # Restriction of the retained conormal differential -/
noncomputable section
set_option maxHeartbeats 50000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

/-- The retained conormal differential is unchanged on a smaller affine open.
Source: restriction of original conormal values, original equation covectors,
and `originalRegularConormalValue_surjective`. -/
theorem retainedAffineConormalDifferential_restriction_of_equation_family
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A B : X.left.Opens) (hA : IsAffineOpen A) (hB : IsAffineOpen B) (hBA : B ≤ A)
    (v : RingHom.ker (j.left.app A).hom → RingHom.ker (j.left.app B).hom)
    (hv : ∀ u, (v u).val = X.left.presheaf.map (homOfLE hBA).op u.val)
    (x : ComplexPoint Y) (hxA : x ∈ Point.overOpen (j.left ⁻¹ᵁ A))
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ B))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    retainedAffineConormalDifferential X Y j d A hA x hxA z hz =
      retainedAffineConormalDifferential X Y j d B hB x hx z hz := by
  refine moduleFibreCovector_ext_value Y (Conormal.sheaf j.left) x d _ _ (fun a => ?_)
  obtain ⟨u, hu⟩ := originalRegularConormalValue_surjective X Y j A hA x hxA a
  have ha := moduleFibreCovectorValue_congr_input Y (Conormal.sheaf j.left) x d
    (retainedAffineConormalDifferential X Y j d A hA x hxA z hz) a
    (originalRegularConormalValue j.left A hA u x hxA) hu.symm
  have hp := moduleFibreCovectorValue_of_equation Y (Conormal.sheaf j.left) x d
    (retainedAffineConormalDifferential X Y j d A hA x hxA z hz)
    (retainedAffineConormalDifferential X Y j d B hB x hx z hz)
    (originalRegularConormalValue j.left A hA u x hxA)
    (originalRegularConormalValue j.left B hB (v u) x hx)
    (retained_restricted_equation_values X Y j d A B hA hB hBA u (v u) (hv u) x hxA hx z hz)
  have hn := originalRegularConormalValue_restriction_aux j.left A B hA hB hBA u (v u) (hv u) x hxA hx
  have hb := moduleFibreCovectorValue_congr_input Y (Conormal.sheaf j.left) x d
    (retainedAffineConormalDifferential X Y j d B hB x hx z hz)
    (originalRegularConormalValue j.left B hB (v u) x hx) a (hn.symm.trans hu)
  exact ha.trans (hp.trans hb)

/-- Restricting to a smaller affine open preserves the retained conormal
map, using the actual presheaf restriction family.
Source: `retainedAffineConormalDifferential_restriction_of_equation_family`
and `originalIdealEquationRestrict_val`. -/
theorem retainedAffineConormalDifferential_restriction
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A B : X.left.Opens) (hA : IsAffineOpen A) (hB : IsAffineOpen B) (hBA : B ≤ A)
    (x : ComplexPoint Y) (hxA : x ∈ Point.overOpen (j.left ⁻¹ᵁ A))
    (hxB : x ∈ Point.overOpen (j.left ⁻¹ᵁ B))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    retainedAffineConormalDifferential X Y j d A hA x hxA z hz =
      retainedAffineConormalDifferential X Y j d B hB x hxB z hz := by
  exact retainedAffineConormalDifferential_restriction_of_equation_family X Y j d A B hA hB hBA
    (fun u => originalIdealEquationRestrict j.left hBA u)
    (fun u => originalIdealEquationRestrict_val j.left hBA u) x hxA hxB z hz

#print axioms retainedAffineConormalDifferential_restriction
#print axioms retainedAffineConormalDifferential_restriction_of_equation_family
end HodgeLean.Foundations.TubularEuler
