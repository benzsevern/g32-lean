import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Canonical union and intersection maps for a retained component -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

variable {C : Scheme} {P V : Over C} (i : P ⟶ V)
  [IsClosedImmersion i.left] (J : V.left.IdealSheafData)

/-- The union with a specified residual ideal, retaining the original component map. -/
def residualUnion : Over C :=
  Over.mk ((i.left.ker ⊓ J).subschemeι ≫ V.hom)

/-- The intersection with the same residual ideal. -/
def residualIntersection : Over C :=
  Over.mk ((i.left.ker ⊔ J).subschemeι ≫ V.hom)

/-- The residual subscheme over the original base. -/
def residualComponent : Over C := Over.mk (J.subschemeι ≫ V.hom)

def residualUnionι : residualUnion i J ⟶ V :=
  Over.homMk (i.left.ker ⊓ J).subschemeι

def residualComponentι : residualComponent (V := V) J ⟶ V :=
  Over.homMk J.subschemeι

def residualUnionFirst : P ⟶ residualUnion i J :=
  Over.homMk
    (IsClosedImmersion.lift (i.left.ker ⊓ J).subschemeι i.left
      (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact inf_le_left))
    (by
      change _ ≫ ((i.left.ker ⊓ J).subschemeι ≫ V.hom) = P.hom
      rw [← Category.assoc, IsClosedImmersion.lift_fac, Over.w i])

@[simp, reassoc]
theorem residualUnionFirst_fac :
    residualUnionFirst i J ≫ residualUnionι i J = i := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

def residualIntersectionFirst : residualIntersection i J ⟶ P :=
  Over.homMk
    (IsClosedImmersion.lift i.left (i.left.ker ⊔ J).subschemeι
      (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left))
    (by
      change _ ≫ P.hom = (i.left.ker ⊔ J).subschemeι ≫ V.hom
      rw [← Over.w i, ← Category.assoc, IsClosedImmersion.lift_fac])

def residualIntersectionSecond :
    residualIntersection i J ⟶ residualComponent (V := V) J :=
  Over.homMk (Scheme.IdealSheafData.inclusion
    (show J ≤ i.left.ker ⊔ J from le_sup_right))
    (by
      change _ ≫ (J.subschemeι ≫ V.hom) = _
      rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
      rfl)

@[simp]
theorem residualIntersectionFirst_fac :
    (residualIntersectionFirst i J ≫ i).left = (i.left.ker ⊔ J).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

theorem residualIntersection_square :
    residualIntersectionFirst i J ≫ i =
      residualIntersectionSecond i J ≫ residualComponentι (V := V) J := by
  apply Over.OverMorphism.ext
  exact (residualIntersectionFirst_fac i J).trans
    (Scheme.IdealSheafData.inclusion_subschemeι
      (show J ≤ i.left.ker ⊔ J from le_sup_right)).symm

theorem residualUnion_kernel :
    (residualUnionι i J).left.ker = i.left.ker ⊓
      (residualComponentι (V := V) J).left.ker := by
  exact (i.left.ker ⊓ J).ker_subschemeι.trans
    (congrArg (fun K => i.left.ker ⊓ K) J.ker_subschemeι.symm)

theorem residualIntersection_kernel :
    (residualIntersectionFirst i J ≫ i).left.ker = i.left.ker ⊔
      (residualComponentι (V := V) J).left.ker := by
  rw [residualIntersectionFirst_fac]
  change (i.left.ker ⊔ J).subschemeι.ker = i.left.ker ⊔ J.subschemeι.ker
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]

end HodgeLean.Foundations.Program.G32Native
