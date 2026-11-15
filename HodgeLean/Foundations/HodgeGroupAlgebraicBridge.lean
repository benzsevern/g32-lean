import HodgeLean.Foundations.HodgeGroupAlgebraicDefs

/-! # Track G2: a `ℚ`-algebraic subgroup as a matrix algebraic group over `ℂ`

A `ℚ`-algebraic subgroup (`g2_IsRatAlgSubgroup`) is the zero set of rational polynomials; mapping
those polynomials to `ℂ` presents it as a `MatrixAlgGroup ℂ n` with the same carrier, so that
Track G1's results apply.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial HodgeLean.Foundations.Program

variable {n : ℕ}

theorem g2b_aeval_eq_eval_map (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (f : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (g1_coords g) f = eval (g1_coords g) (map (algebraMap ℚ ℂ) f) := by
  rw [eval_map, aeval_def]

/-- The subgroup of `GL_n(ℂ)` carried by a `ℚ`-algebraic subgroup.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.1 (closed subgroups). -/
def g2b_subgroup {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)} (hG : g2_IsRatAlgSubgroup G) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ) where
  carrier := G
  one_mem' := hG.2.1
  mul_mem' := fun {x y} hx hy => hG.2.2.1 x hx y hy
  inv_mem' := fun {x} hx => hG.2.2.2 x hx

example : ((g2b_subgroup (n := n) (G := Set.univ)
    ⟨⟨∅, by simp [g2_ratZeroSet]⟩, trivial, fun _ _ _ _ => trivial, fun _ _ => trivial⟩ :
      Subgroup _) : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) = Set.univ := rfl

/-- A `ℚ`-algebraic subgroup as a matrix algebraic group over `ℂ`: its rational equations,
mapped to `ℂ`, present its carrier.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.11.3 and §1.1 (a `k`-closed subgroup is a
closed subgroup of `GL_n(K)`). -/
def g2b_algGroup {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)} (hG : g2_IsRatAlgSubgroup G) :
    MatrixAlgGroup ℂ n :=
  g1_ofEquations (map (algebraMap ℚ ℂ) '' hG.1.choose) (g2b_subgroup hG) (by
    intro g
    change g ∈ G ↔ _
    conv_lhs => rw [hG.1.choose_spec]
    simp only [g2_ratZeroSet, Set.forall_mem_image, g2b_aeval_eq_eval_map]
    rfl)

theorem g2b_algGroup_carrier {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hG : g2_IsRatAlgSubgroup G) :
    ((g2b_algGroup hG).carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) = G := rfl

example {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)} (hG : g2_IsRatAlgSubgroup G) :
    g1_lieAlgebra (g2b_algGroup hG) = g1_lieOfSet G := rfl

end HodgeLean.Foundations
