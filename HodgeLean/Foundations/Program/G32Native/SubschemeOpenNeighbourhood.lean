import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Ambient neighbourhoods inducing prescribed opens of a closed subscheme. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every open of a closed subscheme is the trace of an ambient open. -/
theorem g32l4_ambient_open_for_subscheme_open {X : Scheme}
    (I : X.IdealSheafData) (V : I.subscheme.Opens) :
    ∃ U : X.Opens, I.subschemeι ⁻¹ᵁ U = V := by
  obtain ⟨O, hO, hpre⟩ := I.subschemeι.isEmbedding.isInducing.isOpen_iff.mp V.isOpen
  refine ⟨⟨O, hO⟩, ?_⟩
  apply TopologicalSpace.Opens.ext
  exact hpre

end HodgeLean.Foundations.Program
