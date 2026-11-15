import HodgeLean.Foundations.Program.PrymParabolicSkeleta

/-! # H3b step D: the comparison into a parameter fibre

The map is defined on chains through the step-C homology map and the product coordinate.
No inverse or restriction is selected from an open statement.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The cellular-to-singular map followed by the product coordinate into the actual fibre.
Source: Hatcher, *Algebraic Topology*, Theorem 2.35; `hg8_H1map`, `b6m_coordinate`. -/
def hg9_toFibre {C : Type} [TopologicalSpace C]
    (F : hg8_DeltaMap b4b_root C)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V) :
    hg2_H1 ℤ b4b_root →ₗ[ℤ] b6m_H1 (b63l_parameterFibre mr_base C V hV t) :=
  (b6m_H1Equiv (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩).symm).toLinearMap ∘ₗ
    hg8_H1map F

example {C : Type} [TopologicalSpace C] (F : hg8_DeltaMap b4b_root C)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    (x : hg2_H1 ℤ b4b_root) :
    hg9_toFibre F V hV t x =
      b6m_H1Equiv (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩).symm (hg8_H1map F x) := rfl

end HodgeLean.Foundations.Program
