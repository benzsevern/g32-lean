import HodgeLean.Adapters.CycleClassFlatComparisonDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtensionVanishing
import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport

/-! # Canonical finite support sum

The map sums the canonical enlargements of all component supports.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace
namespace HodgeLean.Adapters

/-- Canonical additive structure on the supported Ext group.
Source: `CategoryTheory.Abelian.Ext.instAddCommGroup`. -/
local instance ccm5_supportGroup (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T)
    (S : Closeds T) (n : ℕ) : AddCommGroup (TopCat.Sheaf.supportH T S F n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup


/-- The canonical map from a finite product of supported groups to the group
supported on their union. Finite products are finite direct sums here.
Source: the relative cohomology functor `CategoryTheory.Sheaf.relH.restrict`. -/
def ccm5_supportSum (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T)
    (r : ℕ) (S : Fin r → Closeds T) (n : ℕ) :
    (∀ i, TopCat.Sheaf.supportH T (S i) F n) →+
      TopCat.Sheaf.supportH T (⨆ i, S i) F n := by
  classical
  exact ∑ i, (CategoryTheory.Sheaf.relH.restrict F
    (homOfLE (show (S i).compl ≤ ⊤ from le_top))
    (homOfLE (show (⨆ j, S j).compl ≤ ⊤ from le_top))
    (homOfLE (show (⨆ j, S j).compl ≤ (S i).compl from
      fun _ hx hi => hx ((le_iSup S i) hi))) (𝟙 _)
    (Subsingleton.elim _ _) n).comp (Pi.evalAddMonoidHom (fun j => TopCat.Sheaf.supportH T (S j) F n) i)

/-- Empty support families give the empty sum.
Source: the empty sum law for additive maps. -/
example (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T) (n : ℕ) :
    ccm5_supportSum T F 0 Fin.elim0 n = 0 := by
  simp [ccm5_supportSum]

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

/-- The closed boundary removed to separate a finite family of prime supports:
all singular boundaries and every pairwise intersection.
Source: cycle-component singular filtrations and the intersection of closed supports. -/
def ccm5_componentBoundary (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x : Fin r → X.left) : Closeds (ComplexPoint X) := by
  classical
  exact (⨆ i, cycleComponentSingularAnalyticClosedFiltration X (x i) 0) ⊔
    ⨆ i, ⨆ j, if i = j then ⊥ else
      cycleComponentAnalyticClosedSupport X (x i) ⊓
        cycleComponentAnalyticClosedSupport X (x j)

/-- An empty component family has empty boundary.
Source: the empty supremum law. -/
example (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ccm5_componentBoundary X 0 Fin.elim0 = ⊥ := by
  simp [ccm5_componentBoundary]

/-- Restriction from the full finite component union to the complement of its boundary.
Source: the restriction morphism of relative cohomology pairs. -/
def ccm5_componentRestriction (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x : Fin r → X.left) (n : ℕ) :=
  CategoryTheory.Sheaf.relH.restrict
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (homOfLE (show (⨆ i, cycleComponentAnalyticClosedSupport X (x i)).compl ≤ ⊤ from le_top))
    (homOfLE (show (⨆ i, cycleComponentAnalyticClosedSupport X (x i)).compl ⊓
      (ccm5_componentBoundary X r x).compl ≤ (ccm5_componentBoundary X r x).compl
      from inf_le_right))
    (homOfLE inf_le_left) (homOfLE le_top) (Subsingleton.elim _ _) n

/-- Restriction sends the zero class to zero.
Source: additivity of `CategoryTheory.Sheaf.relH.restrict`. -/
example (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x : Fin r → X.left) (n : ℕ) :
    ccm5_componentRestriction X r x n 0 = 0 :=
  map_zero _

/-- A component support restricted to the open complement of the finite boundary.
Source: inverse image of a closed set under the open-subspace inclusion. -/
def ccm5_separatedComponentSupport (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x : Fin r → X.left) (i : Fin r) :
    Closeds (ccm5_componentBoundary X r x).compl :=
  ⟨Subtype.val ⁻¹' (cycleComponentAnalyticClosedSupport X (x i) : Set (ComplexPoint X)),
    (cycleComponentAnalyticClosedSupport X (x i)).isClosed.preimage continuous_subtype_val⟩

/-- Membership is membership in the original component support on the good open.
Source: the definition of subspace restriction. -/
example (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x : Fin r → X.left) (i : Fin r)
    (z : (ccm5_componentBoundary X r x).compl) :
    z ∈ ccm5_separatedComponentSupport X r x i ↔
      z.val ∈ cycleComponentAnalyticClosedSupport X (x i) := Iff.rfl


/-- All nonzero prime-pullback coefficients form a finite set.
Source: `ccm3_inverse_components_finite` and `ccm3_flatPullbackPrime_support`. -/
theorem ccm5_primeSupport_finite {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    Set.Finite {z : X.left | ccm3_flatPullbackPrime f.left x z ≠ 0} := by
  apply ((ccm3_inverse_components_finite f x).image
    (ccm3_inverseIdeal f.left x).subschemeι).subset
  intro z hz
  obtain ⟨y, hy, hc⟩ := (ccm3_flatPullbackPrime_support f x z).mp hz
  exact ⟨y, hc, hy⟩

/-- A finite type structure enumerating exactly the nonzero coefficients.
Source: finite inverse-image irreducible components. -/
noncomputable instance ccm5_primeSupport_fintype {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    Fintype {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0} :=
  (ccm5_primeSupport_finite f x).fintype

/-- Enumeration of every component with nonzero coefficient, without repetition.
Source: `Fintype.equivFin`. -/
def ccm5_primeEnumeration {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    Fin (Fintype.card {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0}) ≃
      {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0} :=
  (Fintype.equivFin _).symm

/-- The germ of a supported class in the local relative-cohomology sheaf.
Source: `supportedSingularClass` and `supportRelativeCohomologyGerm`. -/
def ccm5_supportGerm (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ) (a : ComplexPoint X) :
    TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n →+
      (AlgebraicTopology.Singular.supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) n).presheaf.stalk a :=
  ((AlgebraicTopology.Singular.supportRelativeCohomologySheaf
    (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) n).presheaf.germ
      ⊤ a (by trivial)).hom.comp
    (((AlgebraicTopology.Singular.supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) n).app
        (Opposite.op ⊤)).hom.comp
      (HodgeLean.RealDefs.supportedSingularClass X S n).toAddMonoidHom)

/-- Points on the complement of the boundary of the complete prime enumeration.
Source: `ccm5_primeEnumeration` and `ccm5_componentBoundary`. -/
def ccm5_primeGoodOpen {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) : Opens (ComplexPoint X) :=
  (ccm5_componentBoundary X
    (Fintype.card {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (fun i => (ccm5_primeEnumeration f x i).1)).compl

end HodgeLean.Adapters
