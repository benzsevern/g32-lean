import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-! Shared actual relative chain constructions for realization comparison.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program
/-- Integral simplicial chains.
Source: Mathlib SSet.chainComplexFunctor. -/
abbrev c1a5Chains : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- Singular chains of realization, retaining the actual realization functor.
Source: Mathlib sSetTopAdj. -/
abbrev c1a5SingularChains : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  SSet.toTop ⋙ TopCat.toSSet ⋙ c1a5Chains

/-- The literal unit on integral chains.
Source: Mathlib sSetTopAdj.unit. -/
abbrev c1a5Unit (K : SSet.{0}) := c1a5Chains.map (sSetTopAdj.unit.app K)

/-- Naturality supplies the square for the relative unit.
Source: Mathlib Adjunction.unit and Functor.map_comp. -/
lemma c1a5Unit_naturality {A B : SSet.{0}} (f : A ⟶ B) :
    c1a5Chains.map f ≫ c1a5Unit B = c1a5Unit A ≫ c1a5SingularChains.map f := by
  change c1a5Chains.map f ≫ c1a5Chains.map _ =
    c1a5Chains.map _ ≫ c1a5Chains.map _
  rw [← c1a5Chains.map_comp, ← c1a5Chains.map_comp]
  exact congrArg c1a5Chains.map (sSetTopAdj.unit.naturality f)

/-- Relative chains are the cokernel of the inclusion on chains.
Source: Hatcher, Algebraic Topology, §2.1, relative chain groups. -/
abbrev c1a5Relative {A B : SSet.{0}} (f : A ⟶ B) :=
  cokernel (c1a5Chains.map f)

/-- The induced relative unit, specified without an existence premise.
Source: Hatcher, Algebraic Topology, §2.1, maps of pairs; Mathlib cokernel.map. -/
def c1a5RelativeUnit {A B : SSet.{0}} (f : A ⟶ B) :
    c1a5Relative f ⟶ cokernel (c1a5SingularChains.map f) :=
  cokernel.map _ _ (c1a5Unit A) (c1a5Unit B) (c1a5Unit_naturality f)

/-- Relative map of a commutative square for a specified chain functor.
Source: Hatcher, Algebraic Topology, §2.1, functoriality for pairs. -/
def c1a5RelativeMap (F : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ)
    {A B C D : SSet.{0}} (f : A ⟶ B) (g : C ⟶ D)
    (a : A ⟶ C) (b : B ⟶ D) (w : f ≫ b = a ≫ g) :
    cokernel (F.map f) ⟶ cokernel (F.map g) :=
  cokernel.map _ _ (F.map a) (F.map b)
    (by rw [← F.map_comp, ← F.map_comp, w])

/-- Projection of the standard simplex to its vertex model.
Source: Hatcher, Algebraic Topology, §2.1, simplex contraction. -/
abbrev c1a5Augment (n : ℕ) : (Δ[n] : SSet.{0}) ⟶ Δ[0] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)

example := @c1a5RelativeUnit
example := @c1a5RelativeMap
example := c1a5Augment 1


end HodgeLean.Foundations.Program
