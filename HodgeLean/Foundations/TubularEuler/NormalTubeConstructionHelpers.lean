import HodgeLean.Foundations.TubularEuler.NormalMapRestrictionHelpers
import HodgeLean.Foundations.TubularEuler.NormalMapShrinkingHelpers

/-! # Geometric tubes from injective radial restrictions

The homeomorphism and ambient partial homeomorphism retain the supplied map.
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

include ι in
theorem normalBase_nonempty : Nonempty (ComplexPoint Q) := by
  letI : LocallyOfFiniteType Q.hom := by
    rw [← Over.w ι]
    infer_instance
  letI : JacobsonSpace Q.left := LocallyOfFiniteType.jacobsonSpace Q.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Q.left).Nonempty) isOpen_univ.isLocallyClosed
  exact ⟨Over.homMk (pointOfClosedPoint Q.hom x hx)
    (pointOfClosedPoint_comp Q.hom x hx)⟩

def normalTubeOfRestriction (n : LocalNormalMap ι k v j hj)
    (R : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
    (hsub : (R : Set (TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⊆ n.domain)
    (hzero : ∀ x, zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ R)
    (hrad : ∀ z : R, ∀ a : ℝ, a ∈ Set.Icc 0 1 →
      (⟨z.val.proj, (a : ℂ) • z.val.2⟩ : TotalSpace (Fin k → ℂ) (i1_normalFibre j)) ∈ R)
    (hcover : ∀ z ∈ R, ∃ x, z ∈ (n.localInverse x).source)
    (hinj : Function.Injective (restrictNormalAmbient ι k v j hj n R hsub)) :
    NormalTube ι k v j hj := by
  classical
  let fV := restrictNormalMap ι k v j hj n R hsub
  let fA := restrictNormalAmbient ι k v j hj n R hsub
  have hVinj : Function.Injective fV := by
    intro z w h
    exact hinj (congrArg (Point.map
      (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)) h)
  have hV : IsOpenEmbedding fV := IsOpenEmbedding.of_continuous_injective_isOpenMap
    fV.continuous hVinj (restrictNormalMap_isOpenMap ι k v j hj n R hsub hcover)
  have hA : IsOpenEmbedding fA := IsOpenEmbedding.of_continuous_injective_isOpenMap
    fA.continuous hinj (restrictNormalAmbient_isOpenMap ι k v j hj n R hsub hcover)
  let x := Classical.choice (normalBase_nonempty ι)
  letI : Nonempty R := ⟨⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, hzero x⟩⟩
  let T : Opens (ComplexPoint (Over.mk (v ≫ W.hom))) := ⟨Set.range fV, hV.isOpen_range⟩
  let S := R.openPartialHomeomorphSubtypeCoe inferInstance
  let A := S.symm.trans (hA.toOpenPartialHomeomorph fA)
  refine { source := R
           target := T
           map := hV.isEmbedding.toHomeomorph
           contains_zero := hzero
           radial := hrad
           map_zero := ?_
           support := ?_
           ambient := A
           ambient_source := ?_
           ambient_map := ?_ }
  · intro y hy
    exact n.map_zero y _
  · intro z
    exact restrictNormalAmbient_support ι k v j hj n R hsub hcover z
  · simp only [A, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      S, Opens.openPartialHomeomorphSubtypeCoe_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
  · intro z
    have hS : S.symm z.val = z := S.left_inv (Set.mem_univ z)
    change fA (S.symm z.val) = _
    rw [hS]
    rfl

#print axioms normalTubeOfRestriction
#print axioms normalBase_nonempty

end HodgeLean.Foundations.TubularEuler
