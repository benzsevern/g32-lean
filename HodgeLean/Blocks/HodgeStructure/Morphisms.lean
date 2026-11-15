import HodgeLean.Blocks.HodgeStructure.Basic

/-! # Morphisms of pure rational Hodge structures -/

noncomputable section
namespace HodgeBlocks

variable {n : ℤ} {V W U : Type*}
  [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]
  [AddCommGroup U] [Module ℚ U] [Module.Finite ℚ U]

/-- A rational linear map preserving every Hodge piece after scalar extension.
`LinearMap.baseChange` (`Mathlib/LinearAlgebra/TensorProduct/Tower.lean`) is its canonical
complex-linear extension. -/
structure QHodgeStructure.Hom (M : QHodgeStructure n V) (N : QHodgeStructure n W) where
  toLinearMap : V →ₗ[ℚ] W
  maps_pieces : ∀ pq, (M.H pq).map (toLinearMap.baseChange ℂ) ≤ N.H pq

namespace QHodgeStructure.Hom

/-- Identity Hodge morphism. -/
def id (M : QHodgeStructure n V) : M.Hom M where
  toLinearMap := LinearMap.id
  maps_pieces := fun pq => by rw [LinearMap.baseChange_id, Submodule.map_id]

/-- Composition of Hodge morphisms.  `LinearMap.baseChange_comp` makes scalar extension
functorial, and `Submodule.map_comp` identifies the iterated image. -/
def comp {M : QHodgeStructure n V} {N : QHodgeStructure n W} {P : QHodgeStructure n U}
    (g : N.Hom P) (f : M.Hom N) : M.Hom P where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  maps_pieces := fun pq => by
    rw [LinearMap.baseChange_comp, Submodule.map_comp]
    exact (Submodule.map_mono (f.maps_pieces pq)).trans (g.maps_pieces pq)

@[simp] theorem id_toLinearMap (M : QHodgeStructure n V) :
    (id M).toLinearMap = LinearMap.id := rfl

@[simp] theorem comp_toLinearMap {M : QHodgeStructure n V} {N : QHodgeStructure n W}
    {P : QHodgeStructure n U} (g : N.Hom P) (f : M.Hom N) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

end QHodgeStructure.Hom
end HodgeBlocks
