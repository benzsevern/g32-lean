import HodgeLean.Foundations.Program.SchoenTransferC1a5UnionExcisionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5NeighborhoodHelpers

/-! Binary open-cover excision in the integral singular subcomplex model.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- A binary small singular complex is the union of the two actual singular image subcomplexes.
Source: the definition of coverSmallSingularSubcomplex and the two-element supremum. -/
lemma c1a5_binary_small_subcomplex (X : TopCat.{0}) (U V : Set X) :
    coverSmallSingularSubcomplex X (fun b : Bool ↦ if b then V else U) =
      SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U)) ⊔
        SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V)) := by
  simp [coverSmallSingularSubcomplex, iSup_bool_eq, sup_comm]

/-- The union of the two singular image subcomplexes compares with all singular chains.
Source: Hatcher §2.1, Theorem 2.20, open-cover subdivision. -/
lemma c1a5_binary_cover_comparison (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (c1a5Chains.map
      (SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U)) ⊔
        SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V))).ι) := by
  have h := c1a5_module_open_cover_comparison X (fun b : Bool ↦ if b then V else U)
    (by intro b; cases b <;> assumption)
    (by
      apply Set.eq_univ_of_forall
      intro x
      have hx : x ∈ U ∪ V := by rw [hcover]; trivial
      rcases hx with hx | hx
      · exact Set.mem_iUnion.mpr ⟨false, hx⟩
      · exact Set.mem_iUnion.mpr ⟨true, hx⟩)
  rw [c1a5_binary_small_subcomplex] at h
  exact h

/-- Quotienting the binary small-chain comparison gives the actual image-subcomplex excision map.
Source: Hatcher §2.1, Theorem 2.20, relative small-chain quotient construction. -/
lemma c1a5_binary_cover_relative_excision (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    let A := SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U))
    let B := SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V))
    QuasiIso (c1a5RelativeMap c1a5Chains
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) A.ι
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) B.ι (by rfl)) := by
  dsimp only
  exact c1a5_union_relative_excision _ _ (c1a5_binary_cover_comparison X U V hU hV hcover)

end HodgeLean.Foundations.Program
