import HodgeLean.Foundations.RationalHomologyManifold.RationalChainLifts
import HodgeLean.Foundations.RationalHomologyManifold.RelativeChainKernel

/-! Concrete coefficient maps for supported singular chains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Extract the rational coefficient of one singular simplex from an actual singular chain.
Source: Hatcher, Algebraic Topology, section 2.1, the free singular chain group.
HC no distance; AV milestone no distance.
-/
def singularChainCoefficient (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (SingularChainComplex ℚ X).X n ⟶ ModuleCat.of ℚ ℚ :=
  (chainGroupFinsuppIso ℚ X n).hom ≫ ModuleCat.ofHom (Finsupp.lapply s)

#print axioms singularChainCoefficient
/-- A simplex generator contributes its coefficient exactly at that simplex.
Source: Hatcher, Algebraic Topology, section 2.1, the free singular chain group.
HC no distance; AV milestone no distance.
-/
theorem singularChainCoefficient_iota (X : TopCat.{0}) (n : ℕ)
    (s t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) (q : ℚ) :
    (singularChainCoefficient X n s).hom
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) t).hom q) =
      Finsupp.single t q s := by
  classical
  change ((chainGroupFinsuppIso ℚ X n).toLinearEquiv
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) t).hom q)) s = _
  rw [chainGroupFinsuppIso_iota]

#print axioms singularChainCoefficient_iota
/-- Actual rational singular chains are determined by their simplex coefficients.
Source: Hatcher, Algebraic Topology, section 2.1, the free singular chain group.
HC no distance; AV milestone no distance.
-/
theorem singularChain_ext (X : TopCat.{0}) (n : ℕ)
    (z w : (SingularChainComplex ℚ X).X n)
    (h : ∀ s, (singularChainCoefficient X n s).hom z =
      (singularChainCoefficient X n s).hom w) : z = w := by
  apply (chainGroupFinsuppIso ℚ X n).toLinearEquiv.injective
  ext s
  exact h s

#print axioms singularChain_ext
/-- A simplex outside the image of a continuous map has zero coefficient in every image chain.
Source: Hatcher, Algebraic Topology, section 2.1, induced maps on singular chains.
HC no distance; AV milestone no distance.
-/
theorem singularChainCoefficient_chainMap_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (s : (TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : ∀ t, s ≠ (TopCat.toSSet.map f).app _ t) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n ≫
      singularChainCoefficient Y n s = 0 := by
  apply SSet.chainComplex_hom_ext
  intro t
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, comp_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change (singularChainCoefficient Y n s).hom
    (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℚ ℚ)
      ((TopCat.toSSet.map f).app _ t)).hom q) = 0
  rw [singularChainCoefficient_iota]
  exact Finsupp.single_eq_of_ne (hs t)

#print axioms singularChainCoefficient_chainMap_zero
/-- The coefficient of a simplex absent from the subspace descends to the actual relative chain quotient.
Source: Hatcher, Algebraic Topology, section 2.1, relative singular chains.
HC no distance; AV milestone no distance.
-/
def relativeChainCoefficient (P : TopPair.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj P.fst).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : ∀ t, s ≠ (TopCat.toSSet.map P.map).app _ t) :
    ((relativeChainFunctor ℚ).obj P).X n ⟶ ModuleCat.of ℚ ℚ :=
  (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P n).desc
    (CokernelCofork.ofπ (singularChainCoefficient P.fst n s)
      (singularChainCoefficient_chainMap_zero P.map n s hs))

#print axioms relativeChainCoefficient
/-- Relative coefficient extraction agrees with ambient coefficient extraction on the actual projection.
Source: Hatcher, Algebraic Topology, section 2.1, relative singular chains.
HC no distance; AV milestone no distance.
-/
theorem relativeChainCoefficient_projection (P : TopPair.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj P.fst).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : ∀ t, s ≠ (TopCat.toSSet.map P.map).app _ t) :
    (relativeChainProjection ℚ P).f n ≫ relativeChainCoefficient P n s hs =
      singularChainCoefficient P.fst n s := by
  exact (Cofork.IsColimit.π_desc
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P n)
    (t := CokernelCofork.ofπ (singularChainCoefficient P.fst n s)
      (singularChainCoefficient_chainMap_zero P.map n s hs))).trans
    (CokernelCofork.π_ofπ _ _ _)

#print axioms relativeChainCoefficient_projection
/-- A simplex absent from a simplicial map has zero coefficient in every image chain.
Source: Hatcher, Algebraic Topology, section 2.1, induced maps on free chain groups.
HC no distance; AV milestone no distance.
-/
theorem singularChainCoefficient_simplicialMap_zero (S : SSet.{0}) (X : TopCat.{0})
    (f : S ⟶ TopCat.toSSet.obj X) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (hs : ∀ t, s ≠ f.app _ t) :
    (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n ≫ singularChainCoefficient X n s = 0 := by
  apply SSet.chainComplex_hom_ext
  intro t
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, comp_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change (singularChainCoefficient X n s).hom
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) (f.app _ t)).hom q) = 0
  rw [singularChainCoefficient_iota]
  exact Finsupp.single_eq_of_ne (hs t)

#print axioms singularChainCoefficient_simplicialMap_zero
end HodgeLean.Foundations.RationalHomologyManifold
