import HodgeLean.Foundations.Program.G32Native.PairedConormalRelationCoordinateCocycle

/-! # Actual global sections retain the original homogeneous coefficient expansion -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The original affine-cover restrictions detect an actual global section. -/
theorem pairedCechRestriction_injective {R : Type} [CommRing R]
    {X : Scheme} (π : X ⟶ Spec (.of R)) (M : X.Modules)
    (K : X.OrderedAffineCover) :
    Function.Injective (pairedCechRestriction (toOModulePresheaf π M) K) := by
  intro s t h
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M
    (fun s : K.Idx 0 => K.inter s) ⊤ (fun _ => le_top)
      (by rw [paired_cech_vertex_cover K])).1
  intro i
  exact congrFun h i

/-- The global twisting section obtained from the supplied ideal map is
the actual linear combination of the original coordinate sections. -/
theorem paired_nativeIdealMap_global_coordinates (k : ℕ) (hk : 0 < k)
    (φ : Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι ⟶
      SheafOfModules.unit
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf) :
    (show (ProjSpace.twistingSectionPresheaf ℂ k 1).obj ⊤ from
      paired_nativeIdealMapTwistingPowerSection k φ) =
      ∑ j : Fin (k + 1), paired_nativeIdealMapCoefficientVector k hk φ j •
        (show (ProjSpace.twistingSectionPresheaf ℂ k 1).obj ⊤ from
          tensorPowSection (ProjSpace.twistingCoordinateSection ℂ k j) 1) := by
  apply pairedCechRestriction_injective
    ((𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ))) ≫ ProjSpace.π ℂ k)
    ((ProjSpace.twistingSheaf ℂ k).tensorPow 1)
    (ProjSpace.stdCoverPullback
      (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ))))
  funext i
  have h := congrFun (paired_nativeIdealMap_coordinate_cocycle k hk φ) i
  simpa only [pairedCechRestriction, map_sum, LinearMap.map_smul, Finset.sum_apply,
    Pi.smul_apply] using h

end HodgeLean.Foundations.Program.G32Native
