import HodgeLean.Foundations.RationalHomologyManifold.SingularCapTargetWindow

/-! The actual bounded cap comparison on standard singular-chain short complexes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Retain the standard actual singular-chain short complex as the source of the bounded cap comparison.
Source: Hatcher, Algebraic Topology, section 2.1; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
def singularCapTargetStandardWindowComparison (X : TopCat.{0}) (p q : ℕ) :
    (((SingularChainComplex ℚ X).sc (q + 1)).map (forget₂ (ModuleCat ℚ) AddCommGrpCat)) ⟶
    ((((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
      (capTargetComplex X (p + q + 2))).sc' p (p + 1) (p + 2)) :=
  (forget₂ (ModuleCat ℚ) AddCommGrpCat).mapShortComplex.map
      ((SingularChainComplex ℚ X).isoSc' (q + 2) (q + 1) q
        (ChainComplex.prev ℕ (q + 1)) (ChainComplex.next_nat_succ q)).hom ≫
    singularCapTargetWindowComparison X p q

#print axioms singularCapTargetStandardWindowComparison
/-- The actual standard-window comparison retains its original literal middle chain component.
Source: Hatcher, Algebraic Topology, section 3.3; the actual middle cap convention.
HC no distance; AV milestone no distance.
-/
theorem singularCapTargetStandardWindowComparison_middle (X : TopCat.{0}) (p q : ℕ) :
    (singularCapTargetStandardWindowComparison X p q).τ₂ =
      (singularCapTargetWindowComparison X p q).τ₂ := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  rfl

#print axioms singularCapTargetStandardWindowComparison_middle
/-- The actual standard singular-chain window comparison is a quasi-isomorphism with its original global projection.
Source: Bredon, Sheaf Theory, second edition, VI.12; singular-chain and bounded cap-window comparison.
HC no distance; AV milestone no distance.
-/
theorem singularCapTargetStandardWindowComparison_quasiIso (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X)
    (p q : ℕ) (o : LocalRationalOrientation X (p + q + 2)) :
    ShortComplex.QuasiIso (singularCapTargetStandardWindowComparison X p q) := by
  letI := singularCapTargetWindowComparison_quasiIso X t p q o
  exact ShortComplex.quasiIso_comp _ _

#print axioms singularCapTargetStandardWindowComparison_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
