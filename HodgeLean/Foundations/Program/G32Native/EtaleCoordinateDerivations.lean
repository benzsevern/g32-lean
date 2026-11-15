import HodgeLean.Foundations.Program.G32Native.EtaleCoordinateDifferentials

/-! # Point derivations in specified etale coordinate values -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native

/-- Values on the specified etale coordinates identify the actual point
values of derivations without changing the coordinate map. -/
def etaleCoordinateDerivationEquiv
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (n : ℕ)
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale) :
    (Fin n → k) ≃ₗ[k] Derivation k R k :=
  ((etaleCoordinateDifferentialBasis k R n c hc).constr k (M' := k)).trans
    ((KaehlerDifferential.linearMapEquivDerivation (R := k) (S := R) (M := k)).restrictScalars k)

/-- Evaluation on an original coordinate is precisely the prescribed
coordinate value of the point derivation. -/
theorem etaleCoordinateDerivationEquiv_apply
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (n : ℕ)
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (v : Fin n → k) (i : Fin n) :
    etaleCoordinateDerivationEquiv k R n c hc v (c (MvPolynomial.X i)) = v i := by
  change (etaleCoordinateDifferentialBasis k R n c hc).constr k v
    (KaehlerDifferential.D k R (c (MvPolynomial.X i))) = v i
  rw [← etaleCoordinateDifferentialBasis_apply k R n c hc i]
  exact (etaleCoordinateDifferentialBasis k R n c hc).constr_basis k v i

/-- Agreement on the original etale coordinate functions determines the
entire original point-valued derivation. -/
theorem etaleCoordinateDerivation_ext
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (n : ℕ)
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (D E : Derivation k R k)
    (h : ∀ i : Fin n, D (c (MvPolynomial.X i)) = E (c (MvPolynomial.X i))) : D = E := by
  apply (KaehlerDifferential.linearMapEquivDerivation (R := k) (S := R) (M := k)).symm.injective
  apply (etaleCoordinateDifferentialBasis k R n c hc).ext
  intro i
  change D.liftKaehlerDifferential (etaleCoordinateDifferentialBasis k R n c hc i) =
    E.liftKaehlerDifferential (etaleCoordinateDifferentialBasis k R n c hc i)
  rw [etaleCoordinateDifferentialBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D]
  exact h i

#print axioms etaleCoordinateDerivation_ext
#print axioms etaleCoordinateDerivationEquiv
#print axioms etaleCoordinateDerivationEquiv_apply
end HodgeLean.Foundations.Program.G32Native
