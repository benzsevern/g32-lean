import HodgeLean.Foundations.Program.SchoenTowerN2bRegularizedTransitions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A coordinate with value one makes the homogeneous evaluation relevant. -/
theorem n2b_polynomial_evaluation_irrelevant
    {R A κ : Type} [CommRing R] [CommRing A]
    (q : R →+* A) (a : κ → A) (k : κ) (hk : a k = 1) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule κ R)).toIdeal.map
      (eval₂Hom q a) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ zero_lt_one
      (isHomogeneous_X _ k)))
  simpa only [eval₂Hom_X', hk] using (isUnit_one : IsUnit (1 : A))

/-- Scaling every coordinate scales a homogeneous evaluation by its degree. -/
theorem n2b_homogeneous_evaluation_scale
    {R A κ : Type} [CommRing R] [CommRing A]
    (q : R →+* A) (a : κ → A) (u : A)
    (d : ℕ) (p : MvPolynomial κ R) (hp : p.IsHomogeneous d) :
    eval₂Hom q (fun k => u * a k) p = u ^ d * eval₂Hom q a p := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | add p t _ _ hp ht =>
      simp only [map_add, hp, ht, mul_add]
  | monomial m r hm =>
      simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
      have hdegree : ∑ k ∈ m.support, m k = d := by
        simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using hm
      rw [hdegree]
      ring

/-- A coordinate of the homogeneous evaluation has its actual principal-open preimage. -/
theorem n2b_homogeneous_evaluation_preimage
    {R κ : Type} [CommRing R] (X : Scheme.{0})
    (q : R →+* Γ(X, ⊤)) (a : κ → Γ(X, ⊤))
    (k : κ) (hk : a k = 1) (t : κ) :
    Proj.fromOfGlobalSections (X := X) (homogeneousSubmodule κ R)
      (eval₂Hom q a) (n2b_polynomial_evaluation_irrelevant q a k hk) ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule κ R) (MvPolynomial.X t) =
      X.basicOpen (a t) := by
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one (isHomogeneous_X R t),
    eval₂Hom_X']

end HodgeLean.Foundations.Program
