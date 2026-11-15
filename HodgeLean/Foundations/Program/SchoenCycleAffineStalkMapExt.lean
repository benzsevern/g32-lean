import Mathlib.AlgebraicGeometry.Stalk

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two maps from an actual affine scheme stalk agree when they retain the same original affine function values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_affine_stalk_map_ext
    (A : CommRingCat) (p : PrimeSpectrum A) (T : Type*) [CommRing T]
    (f g : (Spec A).presheaf.stalk p →+* T)
    (h : ∀ a : A, f (StructureSheaf.toStalk A p a) = g (StructureSheaf.toStalk A p a)) :
    f = g := by
  letI : Algebra A ((Spec A).presheaf.stalk p) := StructureSheaf.stalkAlgebra A p
  letI : IsLocalization.AtPrime ((Spec A).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A p
  apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
  exact RingHom.ext h

#print axioms s2e_affine_stalk_map_ext
end HodgeLean.Foundations.Program
