import HodgeLean.Foundations.BundleThom.ProductMatrixPairHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import Mathlib.Topology.Homotopy.Contractible

/-! # Actual product normal contractions over topological bases

The contraction changes only the base coordinate and retains the supplied fibre section.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Inclusion of the actual normal fibre over a specified base point into the product pair.
Source: Hatcher, Algebraic Topology, §2.1, maps of relative pairs. -/
def i1_productNormalSection {B : Type} [TopologicalSpace B] (k : ℕ) (b : B) :
    puncturedPair ℂ k ⟶ i1_productNormalPair B k :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun v => (b, v), continuous_const.prodMk continuous_id⟩)
    (fun _ h => h)

/-- The supplied actual fibre section is a right inverse to normal projection.
Source: Hatcher, Algebraic Topology, §2.1, relative product projection. -/
theorem i1_productNormalSection_projection {B : Type} [TopologicalSpace B] (k : ℕ) (b : B) :
    i1_productNormalSection k b ≫ i1_productNormalProjection B k = 𝟙 _ := rfl

/-- A supplied base contraction gives an actual pair homotopy fixing every normal coordinate.
Source: Hatcher, Algebraic Topology, §2.1, relative homotopy invariance. -/
def i1_productNormalContraction {B : Type} [TopologicalSpace B] (k : ℕ) (b : B)
    (H : ContinuousMap.Homotopy (ContinuousMap.const B b) (ContinuousMap.id B)) :
    TopPair.Homotopy (i1_productNormalProjection B k ≫ i1_productNormalSection k b)
      (𝟙 (i1_productNormalPair B k)) where
  fst := {
    toFun := fun p => (H (p.1, p.2.1), p.2.2)
    continuous_toFun := (H.continuous.comp
      (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd
    map_zero_left := fun p => Prod.ext (H.map_zero_left p.1) rfl
    map_one_left := fun p => Prod.ext (H.map_one_left p.1) rfl }
  snd := {
    toFun := fun p => ⟨(H (p.1, p.2.1.1), p.2.1.2), p.2.2⟩
    continuous_toFun := ((H.continuous.comp
      (continuous_fst.prodMk continuous_snd.subtype_val.fst)).prodMk
        continuous_snd.subtype_val.snd).subtype_mk _
    map_zero_left := fun p => Subtype.ext (Prod.ext (H.map_zero_left p.1.1) rfl)
    map_one_left := fun p => Subtype.ext (Prod.ext (H.map_one_left p.1.1) rfl) }
  w := rfl

end HodgeLean.Foundations.BundleThom
