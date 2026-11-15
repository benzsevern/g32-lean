import HodgeLean.Foundations.Program.SchoenTowerFoundB3Proofs

/-! # B3: first ratio-coordinate piece
Implication from explicit ring elements to the coordinate of their fraction chart.
HC no distance; AV milestone no distance.
Transforms, overlap isomorphisms and recursion remain later work.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The two-generator fraction chart has its specified ratio coordinate and equation.
Source: Hartshorne, Algebraic Geometry, II.7, proof of Proposition 7.13;
Stacks Project, Section 10.70 (Tag 052Q). -/
theorem s2t_pairChart_coordinate (R : Type) [CommRing R] (x y : R) :
    ∃ t : s2t_reesChart (Ideal.span {x, y}) x,
      t.val = algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x ∧
      algebraMap R _ y = algebraMap R _ x * t ∧
      Function.Surjective (Polynomial.aeval t :
        Polynomial R →ₐ[R] s2t_reesChart (Ideal.span {x, y}) x) :=
  s2t_pairChart_coordinate_aux R x y

example := @s2t_pairChart_coordinate

end HodgeLean.Foundations.Program
