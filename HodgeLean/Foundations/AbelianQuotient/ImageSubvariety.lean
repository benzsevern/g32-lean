import HodgeLean.Foundations.AbelianQuotient.ImageGroup

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The actual scheme image, retained as an abelian subvariety of the codomain. -/
def imageSubvariety {A B : Variety} (f : Hom A B) : Subvariety B := by
  let G := Classical.choose (canonical_image_abelian f)
  letI := G
  have h := Classical.choose_spec (canonical_image_abelian f)
  exact
    { B :=
        { X := imageModel f
          group := G
          commutative := h.1
          integral := h.2.1
          smooth := h.2.2.1
          projective := h.2.2.2.1 }
      inclusion := ⟨imageInclusion f, h.2.2.2.2.2.1⟩
      embedding := by
        change IsClosedImmersion f.hom.left.imageι
        infer_instance }

end HodgeLean.Foundations.AbelianQuotient
