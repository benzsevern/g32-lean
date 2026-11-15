import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.Algebra.Category.Grp.AB

/-! Local equality for concrete sheafification on a topological space.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equal sheafified sections of an abelian-group presheaf already agree on a neighborhood of each point.
Source: Bredon, Sheaf Theory, second edition, I.6; the local equality property of sheafification.
HC no distance; AV milestone no distance.
-/
theorem sheafification_eq_locally (X : TopCat.{0}) (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    (U : Opens X) (a b : P.obj (Opposite.op U))
    (hab : ((toSheafify (Opens.grothendieckTopology X) P).app (Opposite.op U)) a =
      ((toSheafify (Opens.grothendieckTopology X) P).app (Opposite.op U)) b)
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hV : V ≤ U), x ∈ V ∧
      P.map (homOfLE hV).op a = P.map (homOfLE hV).op b := by
  have hcov := CategoryTheory.Presheaf.equalizerSieve_mem
    (Opens.grothendieckTopology X) (toSheafify (Opens.grothendieckTopology X) P) a b hab
  obtain ⟨V, i, heq, hxV⟩ := hcov x hx
  exact ⟨V, leOfHom i, hxV, heq⟩

#print axioms sheafification_eq_locally
end HodgeLean.Foundations.RationalHomologyManifold
