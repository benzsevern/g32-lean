import HodgeLean.Foundations.Program.G32Native.JointSelectedPrefix

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The symmetric quotient data indexed by its literal power degree. -/
structure G32JointSymmetricQuotient (Z B : Over (Spec ↧ℂ)) (n : ℕ) where
  γ : g3_power Z n ⟶ B
  finiteγ : IsFinite γ.left
  surjectiveγ : Function.Surjective (Point.map γ)
  invariantγ : ∀ σ, s2_permute Z n σ ≫ γ = γ
  quotientγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z n ⟶ T),
    (∀ σ, s2_permute Z n σ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f

/-- Transport the quotient's degree along the retained primitive-degree equality. -/
def jointSelectedSymmetricQuotient
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) :
    G32JointSymmetricQuotient R.Z R.B₀ (2 * R.P.k) :=
  R.hselected ▸ ({
    «γ» := R.γ
    finiteγ := R.inst18
    surjectiveγ := R.hγsurj
    invariantγ := R.hγinv
    quotientγ := R.hγ } : G32JointSymmetricQuotient R.Z R.B₀ (R.h + 1))

/-- Degree transport preserves the quotient map heterogeneously. -/
theorem jointSymmetricQuotient_transport_hEq
    {Z B : Over (Spec ↧ℂ)} {n m : ℕ} (h : n = m)
    (K : G32JointSymmetricQuotient Z B n) :
    HEq (h ▸ K : G32JointSymmetricQuotient Z B m).γ K.γ := by
  cases h
  rfl

#print axioms jointSelectedSymmetricQuotient
#print axioms jointSymmetricQuotient_transport_hEq
end HodgeLean.Foundations.Program
