import HodgeLean.Foundations.Program.G32Native.CanonicalAbelCanonicalClass

/-! # Constancy on the original canonical component -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The weighted extension retains literal unit-weight tuples. -/
theorem weightedSum_tuple {S A : Type*} [AddCommGroup A] {n : ℕ}
    (a : S → A) (z : Fin n → S) :
    weightedSum a (∑ i, Finsupp.single (z i) (1 : ℤ)) = ∑ i, a (z i) := by
  rw [map_sum]
  simp only [weightedSum, LinearMap.toAddMonoidHom_coe,
    Finsupp.linearCombination_single, one_smul]

/-- The symmetric Abel value of an actual canonical divisor is its original weighted divisor sum. -/
theorem canonicalSymmetricAbel_canonical_divisor (G : CanonicalAbelGeometry)
    (p : ComplexPoint G.Z)
    (R : Projectivization ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z))) :
    canonicalSymmetricAbel G p (s2e_canonicalQuotientPoint G.Z G.B (2 * G.k) G.γ G.hg R) =
      weightedSum (analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p)
        (s2e_projectiveCanonicalDivisor (Module.finrank_fin_fun (n := 1) ℂ) R) := by
  induction R using Projectivization.ind with
  | h θ hθ =>
    obtain ⟨z, hz⟩ := s2e_holomorphic_divisor_exists_tuple
      (Module.finrank_fin_fun (n := 1) ℂ) G.k (by rw [G.hd]; omega) θ hθ
    have hpoint := s2e_canonicalQuotientPoint_eq G.Z G.B (2 * G.k) G.γ
      G.invariantγ G.hg θ hθ z hz
    have hsum := canonicalSymmetricAbel_tuple G p z
    have hdiv := (congrArg (weightedSum (analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p)) hz).trans
      (weightedSum_tuple (analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p) z)
    exact (congrArg (canonicalSymmetricAbel G p) hpoint).trans (hsum.trans hdiv.symm)


/-- Every canonical projective form retains the same symmetric Abel value. -/
theorem canonicalSymmetricAbel_canonical_eq (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (R S : Projectivization ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z))) :
    canonicalSymmetricAbel G p (s2e_canonicalQuotientPoint G.Z G.B (2 * G.k) G.γ G.hg R) =
      canonicalSymmetricAbel G p (s2e_canonicalQuotientPoint G.Z G.B (2 * G.k) G.γ G.hg S) := by
  rw [canonicalSymmetricAbel_canonical_divisor, canonicalSymmetricAbel_canonical_divisor]
  induction R using Projectivization.ind with
  | h θ hθ =>
    induction S using Projectivization.ind with
    | h η hη =>
      exact canonical_divisor_abel_sum_eq (Module.finrank_fin_fun (n := 1) ℂ) p θ η hθ hη

/-- The specified etale sheet square retains the same canonical Abel class at all component points. -/
theorem canonicalSymmetricAbel_component_constant (G : CanonicalAbelGeometry)
    (p : ComplexPoint G.Z) (x y : ComplexPoint G.Q) :
    canonicalSymmetricAbel G p (Point.map G.β (Point.map G.ι x)) =
      canonicalSymmetricAbel G p (Point.map G.β (Point.map G.ι y)) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z)) :=
    Module.finite_of_finrank_pos (by rw [G.hd]; omega)
  let ep := s2e_finiteDimensionalProjectivePointEquiv G.k G.hd
  have hpoint (q : ComplexPoint G.Q) : Point.map G.β (Point.map G.ι q) =
      s2e_canonicalQuotientPoint G.Z G.B (2 * G.k) G.γ G.hg (ep.symm (Point.map G.eQ.hom q)) := by
    calc
      Point.map G.β (Point.map G.ι q) = Point.map (G.ι ≫ G.β) q :=
        (Point.map_comp_apply G.ι G.β q).symm
      _ = Point.map (G.eQ.hom ≫ G.ℓ) q := congrArg (fun f => Point.map f q) G.square
      _ = Point.map G.ℓ (Point.map G.eQ.hom q) := Point.map_comp_apply _ _ _
      _ = _ := congrFun G.canonical _
  rw [hpoint x, hpoint y]
  exact canonicalSymmetricAbel_canonical_eq G p _ _

#print axioms canonicalSymmetricAbel_canonical_divisor
#print axioms canonicalSymmetricAbel_canonical_eq
#print axioms canonicalSymmetricAbel_component_constant
end HodgeLean.Foundations.Program.G32Native
