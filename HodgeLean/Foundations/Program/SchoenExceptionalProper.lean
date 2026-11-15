module

public import HodgeLean.Foundations.Program.SchoenExceptionalDefs

@[expose] public noncomputable section
open CategoryTheory Topology
namespace HodgeLean.Foundations.Program

theorem s3_fibre_compact {X Y : TopCat} (p : X ⟶ Y) (hp : IsProperMap p) (y : Y) :
    IsCompact {x : X | p x = y} := by
  exact hp.isCompact_preimage isCompact_singleton

theorem s3_fibre_neighborhood {X Y : TopCat} (p : X ⟶ Y) (hp : IsProperMap p)
    (y : Y) (U : Set X) (hU : IsOpen U) (hUy : {x : X | p x = y} ⊆ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ p ⁻¹' V ⊆ U := by
  refine ⟨(p '' Uᶜ)ᶜ, (hp.isClosedMap _ hU.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hUy hxy)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩

theorem s3_fibre_compactSpace {X Y : TopCat} (p : X ⟶ Y) (hp : IsProperMap p) (y : Y) :
    CompactSpace {x : X // p x = y} :=
  isCompact_iff_compactSpace.mp (s3_fibre_compact p hp y)

end HodgeLean.Foundations.Program
