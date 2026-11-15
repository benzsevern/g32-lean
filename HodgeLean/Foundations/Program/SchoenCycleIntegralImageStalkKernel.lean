import HodgeLean.Foundations.Program.SchoenCycleLocalizedKernel
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Actual scheme-image ideals in stalks with integral source -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- For a finite morphism with integral source, the actual image ideal in a target stalk is the kernel of the map to any source stalk above it.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_integral_image_ideal_stalk_kernel
    {X Y : Scheme} [IsIntegral X] (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) (x : X) (hx : f x ∈ U.1) :
    Ideal.map (Y.presheaf.germ U.1 (f x) hx).hom (f.ker.ideal U) =
      RingHom.ker (f.stalkMap x).hom := by
  letI : Algebra Γ(Y, U.1) (Y.presheaf.stalk (f x)) :=
    (Y.presheaf.germ U.1 (f x) hx).hom.toAlgebra
  let p := U.2.primeIdealOf ⟨f x, hx⟩
  letI := U.2.isLocalization_stalk ⟨f x, hx⟩
  rw [f.ker_apply U]
  apply s2e_localized_kernel_of_injective_target p.asIdeal.primeCompl
    (f.app U.1).hom (X.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom
    (germ_injective_of_isIntegral X x hx) (f.stalkMap x).hom
  ext s
  exact f.germ_stalkMap_apply U.1 x hx s

end HodgeLean.Foundations.Program
