import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Smooth

/-! # Passing from the actual target section algebra to the actual target stalk -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Formal smoothness over the original affine target sections gives formal
smoothness of the actual scheme stalk map.
Source: EGA IV, 17.11.1; Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_formallySmooth_target_stalk
    {X Y : Scheme} (f : X ⟶ Y) (x : X)
    (V : Y.affineOpens) (W : X.Opens) (hx : x ∈ W)
    (hy : f x ∈ V.1) (hWV : W ≤ f ⁻¹ᵁ V.1)
    (h : (f.appLE V.1 W hWV ≫ X.presheaf.germ W x hx).hom.FormallySmooth) :
    (f.stalkMap x).hom.FormallySmooth := by
  let S := Γ(Y, V.1)
  let M := Y.presheaf.stalk (f x)
  let L := X.presheaf.stalk x
  letI : Algebra S M := (Y.presheaf.germ V.1 (f x) hy).hom.toAlgebra
  letI : Algebra M L := (f.stalkMap x).hom.toAlgebra
  letI : Algebra S L := (f.appLE V.1 W hWV ≫ X.presheaf.germ W x hx).hom.toAlgebra
  have hh : Y.presheaf.germ V.1 (f x) hy ≫ f.stalkMap x =
      f.appLE V.1 W hWV ≫ X.presheaf.germ W x hx := by
    rw [f.germ_stalkMap]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  letI : IsScalarTower S M L := IsScalarTower.of_algebraMap_eq (fun s =>
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hh) s).symm)
  let P := (V.2.primeIdealOf ⟨f x, hy⟩).asIdeal
  letI : IsLocalization.AtPrime M P := V.2.isLocalization_stalk ⟨f x, hy⟩
  letI : Algebra.FormallyUnramified S M := Algebra.FormallyUnramified.of_isLocalization P.primeCompl
  letI : Algebra.FormallySmooth S L := RingHom.formallySmooth_algebraMap.mp h
  exact RingHom.formallySmooth_algebraMap.mpr
    (Algebra.FormallySmooth.of_restrictScalars S M L)

#print axioms residual_formallySmooth_target_stalk
end HodgeLean.Foundations.Program.G32Native
