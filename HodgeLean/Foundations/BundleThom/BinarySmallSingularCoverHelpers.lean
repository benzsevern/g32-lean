import HodgeLean.Foundations.BundleThom.SingularSubsetIntersectionHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Field

/-! # Actual binary small singular covers

The union of the two singular subset ranges is the small singular subcomplex of the supplied binary cover.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual binary small singular cover is the union of the two supplied singular subset ranges.
Source: Hatcher, Algebraic Topology, §2.2, small singular chains. -/
theorem i1_binarySmallSingularSubcomplex_eq (X : TopCat) (U V : Set X) :
    coverSmallSingularSubcomplex X (fun b : Bool => if b then V else U) =
      i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V := by
  ext n σ
  change σ ∈ (coverSmallSingularSubcomplex X (fun b : Bool => if b then V else U)).obj n ↔
    (σ ∈ (i1_singularSubsetRange X U).obj n ∨ σ ∈ (i1_singularSubsetRange X V).obj n)
  rw [mem_coverSmallSingularSubcomplex_iff]
  constructor
  · rintro ⟨b, hb⟩
    cases b with
    | false => exact Or.inl hb
    | true => exact Or.inr hb
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

/-- The actual rational binary small-chain inclusion is a quasi-isomorphism for a supplied open cover.
Source: Hatcher, Algebraic Topology, §2.2, subdivision and small-chain approximation. -/
theorem i1_binarySmallChainInclusion_quasiIso (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (SSet.chainComplexMap (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V).ι
      (ModuleCat.of ℚ ℚ)) := by
  have hopen : ∀ b : Bool, IsOpen (if b then V else U) := by
    intro b
    cases b <;> assumption
  have hcov : ⋃ b : Bool, (if b then V else U) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ U ∪ V := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩
  have hq := (coverSmallRationalChainHomotopyEquiv_of_openCover X
    (fun b : Bool => if b then V else U) hopen hcov).quasiIso_hom
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom] at hq
  change QuasiIso (SSet.chainComplexMap
    (coverSmallSingularSubcomplex X (fun b : Bool => if b then V else U)).ι (ModuleCat.of ℚ ℚ)) at hq
  rw [i1_binarySmallSingularSubcomplex_eq] at hq
  exact hq

end HodgeLean.Foundations.BundleThom
