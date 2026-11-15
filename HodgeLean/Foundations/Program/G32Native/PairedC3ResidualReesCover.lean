import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The residual open cover induced by paired Rees charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A paired chart cover above the centre–slice intersection covers the
literal inverse-image subscheme. No coverage away from that intersection
is required for the residual component. -/
theorem pairedC3_residual_rees_iSup
    {X Y : Scheme} (p : X ⟶ Y) (D : Y.IdealSheafData)
    {ι : Type*} (U : ι → Y.Opens) (V : ι → Fin 2 → X.Opens)
    (hD : (D.support : Set Y) ⊆ ⋃ i, (U i : Set Y))
    (hV : ∀ i, V i 0 ⊔ V i 1 = p ⁻¹ᵁ U i) :
    (⨆ j : ι × Fin 2, (D.comap p).subschemeι ⁻¹ᵁ V j.1 j.2) = ⊤ := by
  apply top_unique
  intro x _
  have hx : (D.comap p).subschemeι x ∈ (D.comap p).support := by
    change (D.comap p).subschemeι x ∈ ((D.comap p).support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨x, rfl⟩
  rw [Scheme.IdealSheafData.support_comap] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hD hx)
  have hv : (D.comap p).subschemeι x ∈ V i 0 ⊔ V i 1 := by
    rw [hV]
    exact hi
  rcases hv with h | h
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, 0), h⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, 1), h⟩

/-- The inverse-image residual scheme carries an honest open cover indexed
by the two charts above each base neighbourhood. -/
def pairedC3ResidualReesCover
    {X Y : Scheme} (p : X ⟶ Y) (D : Y.IdealSheafData)
    {ι : Type*} (U : ι → Y.Opens) (V : ι → Fin 2 → X.Opens)
    (hD : (D.support : Set Y) ⊆ ⋃ i, (U i : Set Y))
    (hV : ∀ i, V i 0 ⊔ V i 1 = p ⁻¹ᵁ U i) :
    (D.comap p).subscheme.OpenCover :=
  (D.comap p).subscheme.openCoverOfIsOpenCover
    (fun j : ι × Fin 2 => (D.comap p).subschemeι ⁻¹ᵁ V j.1 j.2)
    (pairedC3_residual_rees_iSup p D U V hD hV)

#print axioms pairedC3_residual_rees_iSup
#print axioms pairedC3ResidualReesCover
end HodgeLean.Foundations.Program.G32Native
