import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneIdealIso

/-! # The distinguished coordinate of the original relation remains exactly homogeneous coordinate zero -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ideal inclusion returns its specified normalized local equation. -/
theorem conormal_ideal_inclusion_coefficient {X : Scheme} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U) :
    conormalIdealMapCoefficient I
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) U a ha = a := by
  change (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val.app
    (Opposite.op U.1) (idealSection I U a ha) = a
  rw [← idealAffineSectionsEquiv_val, idealSection_coordinate]

/-- The concrete polynomial of one specified homogeneous coordinate. -/
def conormalCoordinatePolynomial (K : Type) [CommRing K] (k : ℕ) (j : Fin (k + 1)) :
    homogeneousSubmodule (Fin (k + 1)) K 1 :=
  ⟨X j, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X K j)⟩

/-- The concrete coordinate polynomial gives the original coordinate ratio, with no scalar factor. -/
theorem conormal_coordinate_polynomial_ratio (K : Type) [CommRing K] (k : ℕ)
    (i j : Fin (k + 1)) :
    ProjSpace.homogeneousRatioSection K k 1 (conormalCoordinatePolynomial K k j) i =
      ProjSpace.coordinateRatioSection K k i j := rfl

/-- The inverse ideal comparison carries the original pulled inclusion to the actual native inclusion. -/
theorem conormalHyperplanePolynomialIdealIso_inv_inclusion (k : ℕ) :
    (conormalHyperplanePolynomialIdealIso k).inv ≫
      (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (s2e_hyperplaneIdeal k).subschemeι.toRingCatSheafHom)) ≫
      (pullbackUnit (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).hom =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (conormalNativeHyperplaneIdeal ℂ k).subschemeι.toRingCatSheafHom) := by
  have h := congrArg (fun a => (conormalHyperplanePolynomialIdealIso k).inv ≫ a)
    (conormalHyperplanePolynomialIdealIso_inclusion k)
  rw [Iso.inv_hom_id_assoc] at h
  exact h.symm

/-- The first native relation coordinate is the exact polynomial X₀ in every original chart. -/
theorem conormal_native_hyperplane_inclusion_numerator (k : ℕ) (i : Fin (k + 1)) :
    conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k)
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (conormalNativeHyperplaneIdeal ℂ k).subschemeι.toRingCatSheafHom))
      (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
      (conormal_native_hyperplane_coordinate_mem ℂ k i) =
      ProjSpace.homogeneousRatioSection ℂ k 1 (conormalCoordinatePolynomial ℂ k 0) i := by
  rw [conormal_ideal_inclusion_coefficient, conormal_coordinate_polynomial_ratio]

end HodgeLean.Foundations.Program.G32Native
