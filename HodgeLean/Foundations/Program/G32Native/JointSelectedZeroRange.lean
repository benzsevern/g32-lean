import HodgeLean.Foundations.Program.G32Native.JointSelectedZeroGeometry

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Transport the divisor-range expression through an equality of power degrees. -/
theorem jointSymmetricQuotient_range_transport
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    {n m : ℕ} (h : n = m) (K : G32JointSymmetricQuotient Z B n)
    (k : ℕ) (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hrange : ∀ b : ComplexPoint B, b ∈ Set.range (Point.map ℓ) ↔
      ∃ z : Fin m → ComplexPoint Z,
        Point.map (h ▸ K : G32JointSymmetricQuotient Z B m).γ (s2_lift m z) = b ∧
        ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
          b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
            (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
              ∑ t, Finsupp.single (z t) (1 : ℤ)) :
    ∀ b : ComplexPoint B, b ∈ Set.range (Point.map ℓ) ↔
      ∃ z : Fin n → ComplexPoint Z,
        Point.map K.γ (s2_lift n z) = b ∧
        ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
          b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
            (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
              ∑ t, Finsupp.single (z t) (1 : ℤ) := by
  cases h
  exact hrange

attribute [local instance] G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6
  G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11
  

/-- The canonical point formula supplies U17's range row at the original quotient degree. -/
theorem jointSelectedZeroGeometry_range
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (U : G32JointZeroGeometry R) :
    letI := U.smoothZ
    ∀ b : ComplexPoint R.B₀, b ∈ Set.range (Point.map U.ℓ) ↔
      ∃ z : Fin (R.h + 1) → ComplexPoint R.Z,
        Point.map R.γ (s2_lift (R.h + 1) z) = b ∧
        ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint R.Z), θ ≠ 0 ∧
          b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint R.Z)
            (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
              ∑ t, Finsupp.single (z t) (1 : ℤ) := by
  letI := U.smoothZ
  let K := jointSelectedSymmetricQuotient R
  letI := K.finiteγ
  have hrange := s2e_chain_canonical_range_exact R.Z R.B₀ R.P.k K.γ
    K.surjectiveγ K.invariantγ K.quotientγ U.hg U.hd U.ℓ U.canonical
  exact jointSymmetricQuotient_range_transport R.Z R.B₀ R.hselected
    ({ «γ» := R.γ, finiteγ := R.inst18, surjectiveγ := R.hγsurj,
       invariantγ := R.hγinv, quotientγ := R.hγ } :
      G32JointSymmetricQuotient R.Z R.B₀ (R.h + 1)) R.P.k U.ℓ hrange

#print axioms jointSymmetricQuotient_range_transport
#print axioms jointSelectedZeroGeometry_range
end HodgeLean.Foundations.Program
