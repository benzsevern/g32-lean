import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapMap

/-! Comparison of the fixed-cycle morphism with actual singular cap on homology.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The fixed cycle as a cycle in the standard total-degree short complex.
Source: Hatcher, Algebraic Topology, section 2.1, cycle representatives of homology.
HC no distance; AV milestone no distance.
-/
def fixedTotalCycle (X : TopCat.{0}) (p q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0) :
    LinearMap.ker ((SingularChainComplex ℚ X).sc ((p + 1) + (q + 1))).g.hom := by
  refine ⟨reassocChain ℚ p (q + 1) z, ?_⟩
  change ((SingularChainComplex ℚ X).d (p + 1 + (q + 1))
    ((ComplexShape.down ℕ).next (p + 1 + (q + 1)))).hom _ = 0
  erw [ChainComplex.next_nat_succ]
  exact fixedCycle_reassoc X p q z hz

#print axioms fixedTotalCycle
set_option maxHeartbeats 200000 in
/-- The fixed-cycle morphism induces the existing singular cap product on homology.
Source: Hatcher, Algebraic Topology, section 3.3, descent of cap to homology.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCapHom_homology (X : TopCat.{0}) (p q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0)
    (a : AlgebraicTopology.Singular.CochainCohomology ℚ X (p + 1)) :
    (ShortComplex.homologyMap (fixedCycleCapHom X p q z hz)).hom a =
      AlgebraicTopology.Singular.capCohomologyLinear ℚ X (p + 1) (q + 1) a
        (((SingularChainComplex ℚ X).sc ((p + 1) + (q + 1))).moduleCatHomologyClass
          (fixedTotalCycle X p q z hz)) := by
  let K := SingularChainComplex ℚ X
  let T := (K.sc (p + 1)).linearDual
  let c := (K.sc ((p + 1) + (q + 1))).moduleCatHomologyClass
    (fixedTotalCycle X p q z hz)
  obtain ⟨φ, rfl⟩ := T.moduleCatHomologyClass_surjective a
  let ψ := cohomologyCycleToCocycle ℚ (p + 1) φ
  let F := fixedCycleCapHom X p q z hz
  let G := capShortComplexHom ℚ (p + 1) (q + 1) ψ.1 ψ.2
  let w := fixedTotalCycle X p q z hz
  have hco := LinearMap.congr_fun
    (AlgebraicTopology.Simplicial.capCohomologyLinear_on_cycle ℚ (p + 1) (q + 1) φ) c
  calc
    _ = (K.sc (q + 1)).moduleCatHomologyClass (ShortComplex.moduleCatCycleMap F φ) :=
      ShortComplex.moduleCatHomologyClass_naturality F φ
    _ = (K.sc (q + 1)).moduleCatHomologyClass (ShortComplex.moduleCatCycleMap G w) := by
      apply congrArg ((K.sc (q + 1)).moduleCatHomologyClass)
      apply Subtype.ext
      change F.τ₂.hom φ.1 = G.τ₂.hom w.1
      rw [fixedCycleCapHom_middle, capShortComplexHom_τ₂]
      rfl
    _ = (ShortComplex.homologyMap G).hom c :=
      (ShortComplex.moduleCatHomologyClass_naturality G w).symm
    _ = _ := hco.symm

#print axioms fixedCycleCapHom_homology
/-- In the standard singular cohomology model, the fixed-cycle map is localTraceCap.
Source: Hatcher, Algebraic Topology, section 3.3, the cap construction on homology.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCapHom_localTraceCap (X : TopCat.{0}) (p q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0) (a : Cohomology ℚ X (p + 1)) :
    (ShortComplex.homologyMap (fixedCycleCapHom X p q z hz)).hom
      ((cochainCohomologyEquiv ℚ X (p + 1)).symm a) =
      localTraceCap X (p + 1) (q + 1)
        (((SingularChainComplex ℚ X).sc ((p + 1) + (q + 1))).moduleCatHomologyClass
          (fixedTotalCycle X p q z hz)) a :=
  fixedCycleCapHom_homology X p q z hz ((cochainCohomologyEquiv ℚ X (p + 1)).symm a)

#print axioms fixedCycleCapHom_localTraceCap
end HodgeLean.Foundations.RationalHomologyManifold
