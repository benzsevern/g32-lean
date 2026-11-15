import HodgeLean.Foundations.QuotientDuality.ProperCycleSmallCoverExcision
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexRelativeNaturality

/-! # Actual relative quotients for a pair of open subspaces
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal quotient map from the two original open small-chain subcomplexes to their actual union is a quasi-isomorphism.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_small_cover_quotient_quasiIso.
HC no distance; AV milestone no distance. -/
theorem properCycle_open_pair_quotient_quasiIso (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso (properCycle_subcomplex_quotient_map
      (sup_le (properCycle_subset_subcomplex_mono X (Set.subset_union_left : U ⊆ U ∪ V))
        (properCycle_subset_subcomplex_mono X (Set.subset_union_right : V ⊆ U ∪ V)))) := by
  let W : Bool → Set X := fun b => if b then U else V
  have hWo : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact hV
    · exact hU
  have hcover : ⋃ b, W b = U ∪ V := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
      cases b
      · exact Or.inr hb
      · exact Or.inl hb
    · rintro (hx | hx)
      · exact Set.mem_iUnion.mpr ⟨true, hx⟩
      · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  have hsmall : coverSmallSingularSubcomplex X W =
      subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V := by
    simp [coverSmallSingularSubcomplex, W, subsetSingularSubcomplex, iSup_bool_eq]
  have h := properCycle_small_cover_quotient_quasiIso X W (U ∪ V) hWo hcover
  have hj : coverSmallSingularSubcomplex X W ≤ subsetSingularSubcomplex X (U ∪ V) :=
    properCycle_small_cover_le_subset X W (U ∪ V)
      (fun b => (Set.subset_iUnion W b).trans hcover.le)
  letI : QuasiIso (properCycle_subcomplex_quotient_map hj) := h
  let e := properCycle_subcomplex_quotient_iso_of_eq hsmall.symm
  have hq : QuasiIso (e.hom ≫ properCycle_subcomplex_quotient_map hj) := inferInstance
  change QuasiIso (properCycle_subcomplex_quotient_map hsmall.symm.le ≫
    properCycle_subcomplex_quotient_map hj) at hq
  rw [properCycle_subcomplex_quotient_map_comp] at hq
  exact hq

end HodgeLean.Foundations.QuotientDuality
