import HodgeLean.Foundations.TubularEuler.TubeDefs
import HodgeLean.Foundations.TubularEuler.CompactInjectivityHelpers

/-! # Literal restrictions of the supplied normal map

The support equation and openness use the original local inverses.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle Topology
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)

private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

variable (n : LocalNormalMap ι k v j hj)
variable (R : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
variable (hsub : (R : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆ n.domain)

def restrictNormalMap : C(R, ComplexPoint (Over.mk (v ≫ W.hom))) :=
  n.map.comp ⟨fun z => ⟨z.val, hsub z.property⟩,
    continuous_subtype_val.subtype_mk (fun z : R => hsub z.property)⟩

def restrictNormalAmbient : C(R, ComplexPoint W) :=
  (Point.continuousMap (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)).comp
    (restrictNormalMap ι k v j hj n R hsub)

theorem restrictNormalAmbient_support
    (hcover : ∀ z ∈ R, ∃ x, z ∈ (n.localInverse x).source) (z : R) :
    restrictNormalAmbient ι k v j hj n R hsub z ∈
      a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ z.val.2 = 0 := by
  obtain ⟨x, hx⟩ := hcover z.val z.property
  change Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
    (n.map ⟨z.val, hsub z.property⟩) ∈ _ ↔ _
  rw [← n.local_map x z.val hx]
  exact n.local_support x z.val hx

theorem restrictNormalAmbient_isOpenMap
    (hcover : ∀ z ∈ R, ∃ x, z ∈ (n.localInverse x).source) :
    IsOpenMap (restrictNormalAmbient ι k v j hj n R hsub) := by
  let e (x : ComplexPoint Q) := (n.localInverse x).restrOpen R R.isOpen
  have heR : ∀ x, (e x).source ⊆ R := fun _ _ h => h.2
  apply isOpenMap_of_partial_homeomorph_cover R
    (restrictNormalAmbient ι k v j hj n R hsub) e heR
  · intro x z hz
    exact n.local_map x z hz.1
  · intro z
    obtain ⟨x, hx⟩ := hcover z.val z.property
    exact ⟨x, hx, z.property⟩

theorem restrictNormalMap_isOpenMap
    (hcover : ∀ z ∈ R, ∃ x, z ∈ (n.localInverse x).source) :
    IsOpenMap (restrictNormalMap ι k v j hj n R hsub) := by
  let g := Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
  have hg : Function.Injective g := ComplexPoint.map_injective_of_mono _
  have hopen := restrictNormalAmbient_isOpenMap ι k v j hj n R hsub hcover
  intro S hS
  have heq : restrictNormalMap ι k v j hj n R hsub '' S =
      g ⁻¹' (restrictNormalAmbient ι k v j hj n R hsub '' S) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨z, hz, hg hzy⟩
  rw [heq]
  exact (hopen S hS).preimage
    (Point.continuousMap (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)).continuous

#print axioms restrictNormalMap_isOpenMap
#print axioms restrictNormalAmbient_isOpenMap
#print axioms restrictNormalMap
#print axioms restrictNormalAmbient
#print axioms restrictNormalAmbient_support

end HodgeLean.Foundations.TubularEuler
