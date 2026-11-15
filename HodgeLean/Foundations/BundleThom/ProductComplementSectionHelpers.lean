import HodgeLean.Foundations.BundleThom.ProductContractionHelpers

/-! # Actual complement sections over arbitrary topological bases

Only the normal coordinate is interpolated; the base is fixed throughout.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Replacing the normal coordinate by a specified nonzero vector maps the whole product into its actual complement.
Source: Hatcher, Algebraic Topology, §2.1, relative product pairs. -/
def i1_productComplementSection {B : Type} [TopologicalSpace B] (k : ℕ)
    (w : Fin k → ℂ) (hw : w ≠ 0) :
    (i1_productNormalPair B k).fst ⟶ (i1_productNormalPair B k).snd :=
  TopCat.ofHom ⟨fun p => ⟨(p.1, w), hw⟩,
    (continuous_fst.prodMk continuous_const).subtype_mk _⟩

/-- Inclusion after the specified complement section is homotopic to the identity on the actual product for every base.
Source: Hatcher, Algebraic Topology, §2.1, homotopy invariance. -/
def i1_productComplementSectionHomotopy {B : Type} [TopologicalSpace B] (k : ℕ)
    (w : Fin k → ℂ) (hw : w ≠ 0) :
    TopCat.Homotopy (i1_productComplementSection (B := B) k w hw ≫ (i1_productNormalPair B k).map)
      (𝟙 (i1_productNormalPair B k).fst) where
  toFun := fun p => (p.2.1, (1 - (p.1 : ℝ)) • w + (p.1 : ℝ) • p.2.2)
  continuous_toFun := by fun_prop
  map_zero_left := fun p => by
    change (p.1, (1 - (0 : ℝ)) • w + (0 : ℝ) • p.2) = (p.1, w)
    simp
  map_one_left := fun p => by
    change (p.1, (1 - (1 : ℝ)) • w + (1 : ℝ) • p.2) = p
    simp <;> rfl

end HodgeLean.Foundations.BundleThom
