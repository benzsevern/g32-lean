import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOriginalAction
import HodgeLean.Foundations.Program.SchoenTowerN1bcHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained original cyclic cover has the specified actual function-field degree. -/
theorem s2v_l1b_divisor_original_degree
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) [IsFinite p.left] (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y) :
    ∃ κ : Z.left.functionField ⟶ Y.left.functionField,
      (Spec.map κ ≫ Z.left.fromSpecStalk (genericPoint Z.left) =
        Y.left.fromSpecStalk (genericPoint Y.left) ≫ p.left) ∧
      (letI := κ.hom.toAlgebra
       Module.Finite Z.left.functionField Y.left.functionField ∧
       IsGalois Z.left.functionField Y.left.functionField ∧
       IsCyclic (Y.left.functionField ≃ₐ[Z.left.functionField] Y.left.functionField) ∧
       Module.finrank Z.left.functionField Y.left.functionField = S.m) := by
  let G := S.H ⧸ S.χ.ker
  let ρ := s2v_l1b_divisor_original_action S Y a ha1 hamul
  have hρ : Function.Injective ρ := by
    intro u v huv
    apply hinj
    exact congrArg (fun g : Aut Y => g.asIso.hom) huv
  haveI : IsCyclic G := isCyclic_of_injective e.toMonoidHom e.injective
  haveI : IsDominant p.left := n1bc_dominant_of_points_surjective p hpsurj
  have hcat := s2v_l1b_categorical_quotient_of_point_orbits Y Z G ρ p hpsurj hp hporbit
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint Z.left) (U := ⊤) trivial
  letI : Nonempty U := ⟨⟨genericPoint Z.left, hxU⟩⟩
  obtain ⟨hfin, hgal, hcyc, hdeg⟩ :=
    s2v_l1b_cyclic_categorical_quotient_degree Y Z G ρ hρ p hp hcat ⟨U, hU⟩
  have hcard : Nat.card G = S.m := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (ZMod S.m) = S.m
    rw [Nat.card_eq_fintype_card, ZMod.card]
  exact ⟨s2v_l1b_functionFieldPullback p.left,
    s2v_l1b_functionFieldPullback_generic_square p.left,
    hfin, hgal, hcyc, hdeg.trans hcard⟩

end HodgeLean.Foundations.Program
