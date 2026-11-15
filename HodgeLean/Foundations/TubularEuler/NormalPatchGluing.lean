import HodgeLean.Foundations.TubularEuler.NormalMapCoordinateAssemblyHelpers
import HodgeLean.Foundations.TubularEuler.CompatibleContinuousMapHelpers

/-! # Assembly from compatible primitive normal germs

Each original coordinate patch survives enlargement to the union domain.
No local inverse or transverse derivative is supplied by the assembly.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Bundle
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom
variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) := i1_normalTotalTopology j k
local notation "NT" => TotalSpace (Fin k → ℂ) (i1_normalFibre j)
local notation "Z" => ComplexPoint (Over.mk (v ≫ W.hom))
local notation "zN" => zeroSection (Fin k → ℂ) (i1_normalFibre j)

/-- Enlarging a domain with an agreeing map retains its primitive normal coordinates.
Source: Lee, Introduction to Smooth Manifolds, second edition, proof of Theorem 6.24,
restriction of normal exponential coordinates.
HC no distance; AV milestone no distance. -/
def NormalCoordinatePatch.enlarge
    {U O : Opens NT} {m : C(U, Z)} {f : C(O, Z)} {x : ComplexPoint Q}
    (p : NormalCoordinatePatch ι k v j U m x) (hsub : (U : Set NT) ⊆ O)
    (heq : ∀ z : U, f ⟨z.val, hsub z.property⟩ = m z) :
    NormalCoordinatePatch ι k v j O f x where
  baseChart := p.baseChart
  frame := p.frame
  ambientChart := p.ambientChart
  base_hol := p.base_hol
  frame_linear := p.frame_linear
  ambient_hol := p.ambient_hol
  base_mem := p.base_mem
  frame_mem := p.frame_mem
  support := p.support
  modelSource := p.modelSource
  modelMap := p.modelMap
  model_mem := p.model_mem
  model_analytic := p.model_analytic
  model_fix := p.model_fix
  model_transverse := p.model_transverse
  model_target := p.model_target
  frame_target := p.frame_target
  map_domain q hq := hsub (p.map_domain q hq)
  map_agreement q hq := by
    exact (p.map_agreement q hq).trans
      (congrArg (Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W))
        (heq ⟨_, p.map_domain q hq⟩)).symm

/-- Compatible local normal coordinate maps give the retained local normal map.
The inverse function theorem is applied by `localNormalMapOfCoordinatePatches`.
Source: Lee, Introduction to Smooth Manifolds, second edition, proof of Theorem 6.24;
Mathlib, `ContinuousMap.liftCover`.
HC no distance; AV milestone no distance. -/
theorem local_normal_map_of_compatible_patches
    (U : ComplexPoint Q → Opens NT) (m : ∀ x, C(U x, Z))
    (hzero : ∀ x, zN x ∈ U x)
    (hmzero : ∀ i x hx, m i ⟨zN x, hx⟩ = Point.map (i1_smoothLift ι v j hj) x)
    (patch : ∀ x, NormalCoordinatePatch ι k v j (U x) (m x) x)
    (hcompat : ∀ i l z hi hl, m i ⟨z, hi⟩ = m l ⟨z, hl⟩) :
    Nonempty (LocalNormalMap ι k v j hj) := by
  classical
  let f (i : ComplexPoint Q) (z : NT) : Z :=
    if hz : z ∈ U i then m i ⟨z, hz⟩ else Point.map (i1_smoothLift ι v j hj) i
  have hf (i : ComplexPoint Q) : ContinuousOn (f i) (U i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z : U i => f i z.val)
    have he : (fun z : U i => f i z.val) = m i := by
      funext z
      simp only [f, dite_eq_left z.property]
    rw [he]
    exact (m i).continuous
  obtain ⟨g, hg⟩ := compatible_continuousOn_maps_union U f hf (by
    intro i l z hi hl
    simpa only [f, dite_eq_left hi, dite_eq_left hl] using hcompat i l z hi hl)
  let O : Opens NT := ⟨⋃ i, (U i : Set NT), isOpen_iUnion (fun i => (U i).isOpen)⟩
  have hsub (i : ComplexPoint Q) : (U i : Set NT) ⊆ O :=
    fun z hz => Set.mem_iUnion.mpr ⟨i, hz⟩
  have heq (i : ComplexPoint Q) (z : U i) : g ⟨z.val, hsub i z.property⟩ = m i z := by
    simpa only [f, dite_eq_left z.property] using hg i z.val z.property
  exact ⟨localNormalMapOfCoordinatePatches ι k v j hj O g
    (fun x => hsub x (hzero x))
    (fun x hx => (heq x ⟨zN x, hzero x⟩).trans (hmzero x x (hzero x)))
    (fun x => NormalCoordinatePatch.enlarge ι k v j (patch x) (hsub x) (heq x))⟩

#print axioms NormalCoordinatePatch.enlarge
#print axioms local_normal_map_of_compatible_patches

end HodgeLean.Foundations.TubularEuler
