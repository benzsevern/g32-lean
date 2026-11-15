import HodgeLean.Foundations.BundleThom.Defs

/-! # Detection of degree-zero homology maps by actual vertices

The degree-zero chain generators detect maps out of degree-zero singular homology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology.Singular Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- The homology generator supplied by an actual singular vertex.
Source: Hatcher, Algebraic Topology, §2.1, degree-zero singular homology. -/
def i1_vertexHomologyMap (X : TopCat) (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    ModuleCat.of ℚ ℚ ⟶ Homology ℚ X 0 :=
  (SingularChainComplex ℚ X).liftCycles ((TopCat.toSSet.obj X).ιChainComplex x)
    0 (by simp) (by simp) ≫ (SingularChainComplex ℚ X).homologyπ 0

/-- Vertex homology generators commute with every actual continuous map.
Source: Hatcher, Algebraic Topology, §2.1, naturality of singular homology. -/
theorem i1_vertexHomologyMap_naturality {X Y : TopCat} (f : X ⟶ Y)
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    i1_vertexHomologyMap X x ≫ HomologicalComplex.homologyMap (singularChainComplexMap ℚ f) 0 =
      i1_vertexHomologyMap Y ((TopCat.toSSet.map f).app _ x) := by
  unfold i1_vertexHomologyMap
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  apply (cancel_mono ((SingularChainComplex ℚ Y).iCycles 0)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  exact SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
    (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) x

/-- Equality on every actual vertex detects linear maps out of degree-zero homology.
Source: Hatcher, Algebraic Topology, §2.1, generators of degree-zero homology. -/
theorem i1_homologyZero_hom_ext (X : TopCat) {M : ModuleCat ℚ}
    (f g : Homology ℚ X 0 ⟶ M)
    (h : ∀ x : (TopCat.toSSet.obj X) _⦋0⦌,
      i1_vertexHomologyMap X x ≫ f = i1_vertexHomologyMap X x ≫ g) : f = g := by
  let K := SingularChainComplex ℚ X
  let e := SSet.chainComplexXZeroIsoCyclesZero K
  apply (cancel_epi (K.homologyπ 0)).mp
  apply (cancel_epi e.hom).mp
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  simp only [← Category.assoc, e, SSet.chainComplexXZeroIsoCyclesZero,
    HomologicalComplex.comp_liftCycles, Category.comp_id]
  exact h x

end HodgeLean.Foundations.BundleThom
