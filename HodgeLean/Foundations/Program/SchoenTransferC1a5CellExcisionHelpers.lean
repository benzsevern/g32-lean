import HodgeLean.Foundations.Program.SchoenTransferC1a5CoproductExcisionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5EmptyExcisionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeHelpers

/-! Singular excision in the literal relative skeletal cell presentation.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Realized characteristic-cell attachment gives the literal singular relative quasi-isomorphism.
Source: Hatcher §2.1, Theorem 2.20; Mathlib relativeCellComplexOfMono.isPushout. -/
lemma c1a5_singular_cell_excision {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    let l := SSet.relativeCellComplexOfMono.l i n
    let r := SSet.relativeCellComplexOfMono.r i n
    let t := SSet.relativeCellComplexOfMono.t i n
    let b := SSet.relativeCellComplexOfMono.b i n
    let w := (SSet.relativeCellComplexOfMono.w i n).symm
    QuasiIso (c1a5RelativeMap c1a5SingularChains l r t b w) := by
  dsimp only
  have sq := (SSet.relativeCellComplexOfMono.isPushout i n).map SSet.toTop
  cases n with
  | zero =>
    have h0 : IsInitial (SSet.boundary.{0} 0 : SSet) := by
      rw [SSet.boundary_zero]
      exact SSet.Subcomplex.isInitialBot
    have ht := h0.isInitialObj SSet.toTop (SSet.boundary.{0} 0 : SSet)
    have : IsEmpty (SSet.toTop.obj (SSet.boundary.{0} 0 : SSet)) :=
      Function.isEmpty (ht.to (TopCat.of PEmpty))
    have : IsEmpty (SSet.toTop.obj (SSet.relativeCellComplexOfMono.sigmaBoundary i 0)) :=
      Function.isEmpty ((c1a5_realization_sigma_iso
        (fun _ : SSet.relativeCellComplexOfMono.Cell i 0 ↦ (SSet.boundary.{0} 0 : SSet))).hom)
    exact c1a5_empty_attachment_singular_excision sq
  | succ n =>
    exact c1a5_realized_coproduct_simplex_excision
      (SSet.relativeCellComplexOfMono.Cell i (n + 1)) n
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.t i (n + 1)))
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i (n + 1)))
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.b i (n + 1))) sq

end HodgeLean.Foundations.Program
