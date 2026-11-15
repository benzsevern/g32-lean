import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Extension to a stalk preserves finite products of ideal sheaves. -/
theorem s2v_l1b_divisor_ideal_germ_product
    (X : Scheme) {J : Type*} [Fintype J] (I : J → X.IdealSheafData)
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    ((∏ j, I j).ideal U).map (X.presheaf.germ U.1 x hx).hom =
      ∏ j, ((I j).ideal U).map (X.presheaf.germ U.1 x hx).hom := by
  classical
  have H (s : Finset J) : ((∏ j ∈ s, I j).ideal U).map
      (X.presheaf.germ U.1 x hx).hom =
        ∏ j ∈ s, ((I j).ideal U).map (X.presheaf.germ U.1 x hx).hom := by
    induction s using Finset.induction_on with
    | empty => simp [Ideal.map_top]
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Scheme.IdealSheafData.ideal_mul]
      change Ideal.map _ ((I j).ideal U * (∏ k ∈ s, I k).ideal U) = _
      rw [Ideal.map_mul, ih]
  exact H Finset.univ

end HodgeLean.Foundations.Program
