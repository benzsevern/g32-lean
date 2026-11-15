import HodgeLean.Foundations.BundleThom.Defs
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Cokernels and the zero-source arrow adjunction

The actual cokernel functor carries colimit constructions on chain arrows to relative chain colimits.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
open scoped ZeroObject
namespace HodgeLean.Foundations.BundleThom

variable (C : Type*) [Category* C] [HasZeroObject C] [HasZeroMorphisms C] [HasCokernels C]

/-- The actual arrow from the zero object, functorially in its target.
Source: Mac Lane, Categories for the Working Mathematician, V.2, universal cokernel property. -/
def i1_zeroSourceArrow : C ⥤ Arrow C where
  obj X := Arrow.mk (0 : (0 : C) ⟶ X)
  map f := Arrow.homMk (𝟙 (0 : C)) f (by simp)

/-- The universal cokernel hom-set equivalence, retaining the actual source arrow.
Source: Mac Lane, Categories for the Working Mathematician, V.2, universal cokernel property. -/
def i1_cokernelZeroSourceHomEquiv (a : Arrow C) (X : C) :
    ((coker (C := C)).obj a ⟶ X) ≃ (a ⟶ (i1_zeroSourceArrow C).obj X) where
  toFun f := Arrow.homMk 0 (cokernel.π a.hom ≫ f) (by
    rw [zero_comp, ← Category.assoc, cokernel.condition, zero_comp])
  invFun g := cokernel.desc a.hom g.right (by simpa [i1_zeroSourceArrow] using g.w.symm)
  left_inv f := by
    apply (cancel_epi (cokernel.π a.hom)).mp
    change cokernel.π a.hom ≫ cokernel.desc a.hom (cokernel.π a.hom ≫ f) _ = _
    exact cokernel.π_desc _ _ _
  right_inv g := by
    apply Arrow.hom_ext
    · change (0 : a.left ⟶ (0 : C)) = g.left
      exact Subsingleton.elim _ _
    · exact cokernel.π_desc _ _ _

/-- The actual cokernel functor is left adjoint to the zero-source arrow functor.
Source: Mac Lane, Categories for the Working Mathematician, V.2, colimits and cokernels. -/
def i1_cokernelZeroSourceAdjunction : coker (C := C) ⊣ i1_zeroSourceArrow C :=
  Adjunction.mkOfHomEquiv {
    homEquiv := i1_cokernelZeroSourceHomEquiv C
    homEquiv_naturality_left_symm := by
      intro a' a X f g
      apply (cancel_epi (cokernel.π a'.hom)).mp
      simp [i1_cokernelZeroSourceHomEquiv, coker, Category.assoc, cokernel.π_desc, cokernel.π_desc_assoc]
    homEquiv_naturality_right := by
      intro a X Y f g
      apply Arrow.hom_ext
      · change (0 : a.left ⟶ (0 : C)) = 0 ≫ 𝟙 (0 : C)
        exact Subsingleton.elim _ _
      · change cokernel.π a.hom ≫ (f ≫ g) = (cokernel.π a.hom ≫ f) ≫ g
        exact (Category.assoc _ _ _).symm }

end HodgeLean.Foundations.BundleThom
