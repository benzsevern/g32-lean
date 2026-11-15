import HodgeLean.Adapters.NormalConeB4aGysinLocalDimension

noncomputable section
namespace HodgeLean.Adapters
open TopologicalSpace

/-- Every dense open set in a Noetherian space contains the generic points of
all its irreducible components. -/
theorem a3b4a_gysin_generic_points_mem_dense_open
    {T : Type*} [TopologicalSpace T] [NoetherianSpace T]
    (V : Set T) (hV : IsOpen V) (hdense : Dense V) :
    ∀ ξ ∈ genericPoints T, ξ ∈ V := by
  intro ξ hξ
  obtain ⟨O, hO, hOne, hOV⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure ({ξ} : Set T)) hξ
  obtain ⟨y, hyV, hyO⟩ := hdense.exists_mem_open hO hOne
  exact (specializes_iff_mem_closure.mpr (hOV hyO)).mem_open hV hyV

end HodgeLean.Adapters
