import HodgeLean.Foundations.Program.G32Native.TypeIIIPaperDefs

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.TypeIIIPaper

/-- An intertwining equivalence transports the sum of all operator images. -/
theorem orbit_map_intertwine {K E H I : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup H] [Module K H] (e : E ≃ₗ[K] H) (U : Submodule K E)
    (F : I → Module.End K E) (G : I → Module.End K H)
    (h : ∀ i, (G i).comp e.toLinearMap = e.toLinearMap.comp (F i)) :
    (⨆ i, U.map (F i)).map e.toLinearMap = ⨆ i, (U.map e.toLinearMap).map (G i) := by
  rw [Submodule.map_iSup]
  congr 1
  funext i
  rw [← Submodule.map_comp, ← Submodule.map_comp, h i]

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- A cast of an indexed cohomology subspace is its image under the cohomology cast equivalence. -/
theorem degree_cast_submodule_map {i j : ℕ} (h : i = j)
    (U : Submodule ℚ (HQ A (2*i))) :
    cast (congrArg (fun n => Submodule ℚ (HQ A (2*n))) h) U =
      U.map (HQ.castEquiv A (congrArg (2*·) h)).toLinearMap := by
  subst j
  change U = U.map LinearMap.id
  exact (Submodule.map_id U).symm

/-- Cohomology cast equivalences compose along equality of degrees. -/
theorem cohomology_cast_trans {i j k : ℕ} (h : i = j) (g : j = k) :
    (HQ.castEquiv A h).trans (HQ.castEquiv A g) = HQ.castEquiv A (h.trans g) := by
  subst j
  subst k
  rfl

/-- Rational exterior pullback intertwines the cup-wedge equivalence in any equal degree presentation. -/
theorem rationalPullback_cast_cup (d : AbelianEnd0 A) {m n : ℕ} (h : m = n) :
    (rationalPullback A d n).comp
      (((torusCohomology_cupProductOf A).cupWedgeEquiv m).trans
        (HQ.castEquiv A h)).toLinearMap =
      (((torusCohomology_cupProductOf A).cupWedgeEquiv m).trans
        (HQ.castEquiv A h)).toLinearMap.comp
          (exteriorPower.map m (abelianEnd0Action A d).unop) := by
  subst n
  change (rationalPullback A d m).comp
      ((torusCohomology_cupProductOf A).cupWedgeEquiv m).toLinearMap =
    ((torusCohomology_cupProductOf A).cupWedgeEquiv m).toLinearMap.comp _
  apply LinearMap.ext
  intro x
  change (torusCohomology_cupProductOf A).cupWedgeEquiv m
    (exteriorPower.map m (abelianEnd0Action A d).unop
      (((torusCohomology_cupProductOf A).cupWedgeEquiv m).symm
        ((torusCohomology_cupProductOf A).cupWedgeEquiv m x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

#print axioms orbit_map_intertwine
#print axioms rationalPullback_cast_cup
end HodgeLean.Foundations.Program.TypeIIIPaper
