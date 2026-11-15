import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSections
import HodgeLean.Foundations.RationalHomologyManifold.SheafificationLocalEquality

/-! Finite-stage local equality in the actual supported subdivision sheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equality of finite-stage sections in the subdivision sheaf is witnessed locally at a later actual stage.
Source: Bredon, Sheaf Theory, second edition, VI.12; local equality in supported subdivision limits.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_eq_locally_eventually (X : TopCat.{0}) (n m : ℕ) (U : Opens X)
    (a b : ((singularChainPresheafComplex ℚ X).X n).obj (Opposite.op U))
    (hab : ((toSheafify (Opens.grothendieckTopology X)
        ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op U))
        ((((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U)) a) =
      ((toSheafify (Opens.grothendieckTopology X)
        ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op U))
        ((((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U)) b))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hV : V ≤ U) (k : ℕ) (hk : m ≤ k), x ∈ V ∧
      ((((presheafSubdivisionDiagram X).map (homOfLE hk)).f n).app (Opposite.op V))
        (((singularChainPresheafComplex ℚ X).X n).map (homOfLE hV).op a) =
      ((((presheafSubdivisionDiagram X).map (homOfLE hk)).f n).app (Opposite.op V))
        (((singularChainPresheafComplex ℚ X).X n).map (homOfLE hV).op b) := by
  let A := (colimit.ι (presheafSubdivisionDiagram X) m).f n
  obtain ⟨V, hV, hxV, hVeq⟩ := sheafification_eq_locally X
    ((subdivisionLimitPresheafComplex X).X n) U (A.app _ a) (A.app _ b) hab x hx
  have ha := ConcreteCategory.congr_hom (A.naturality (homOfLE hV).op) a
  have hb := ConcreteCategory.congr_hom (A.naturality (homOfLE hV).op) b
  simp only [ConcreteCategory.comp_apply] at ha hb
  have heq := ha.trans (hVeq.trans hb.symm)
  obtain ⟨k, hk, hkeq⟩ := subdivisionLimitPresheaf_section_eq_eventually X n m V
    (((singularChainPresheafComplex ℚ X).X n).map (homOfLE hV).op a)
    (((singularChainPresheafComplex ℚ X).X n).map (homOfLE hV).op b) heq
  exact ⟨V, hV, k, hk, hxV, hkeq⟩

#print axioms subdivisionLimitSheaf_eq_locally_eventually
end HodgeLean.Foundations.RationalHomologyManifold
