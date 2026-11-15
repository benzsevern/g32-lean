import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericPoint
import Mathlib.AlgebraicGeometry.Stalk

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual dominant field-source map constructs its original generic
field embedding and retains the exact scheme factorization. -/
theorem s2e_c1_field_source_generic_embedding
    (L : Type) [Field L] (X : Scheme) [IsIntegral X]
    (η : Spec (CommRingCat.of L) ⟶ X) [IsDominant η] :
    ∃ φ : X.functionField →+* L, Function.Injective φ ∧
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) = η := by
  have hg : η (IsLocalRing.closedPoint L) = genericPoint X :=
    (congrArg η (Subsingleton.elim _ (genericPoint (Spec (CommRingCat.of L))))).trans
      (s2e_c1_dominant_generic_point η)
  let u : X.functionField ⟶ CommRingCat.of L :=
    eqToHom (congrArg X.presheaf.stalk hg.symm) ≫ Scheme.stalkClosedPointTo η
  refine ⟨u.hom, u.hom.injective, ?_⟩
  have htransport (x y : X) (h : x = y) :
      Spec.map (eqToHom (congrArg X.presheaf.stalk h.symm)) ≫ X.fromSpecStalk y =
        X.fromSpecStalk x := by
    subst y
    simp
  change Spec.map u ≫ X.fromSpecStalk (genericPoint X) = η
  dsimp only [u]
  rw [Spec.map_comp, Category.assoc, htransport]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk η
  exact hg

end HodgeLean.Foundations.Program
