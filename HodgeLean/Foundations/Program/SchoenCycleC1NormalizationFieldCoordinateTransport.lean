import HodgeLean.Foundations.Program.SchoenCycleC1CompatibleFieldTowerTransport
import HodgeLean.Foundations.Program.SchoenCycleC1SignedNormalizationChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A signed paired equation in the original covering field gives etaleness
of the actual affine normalization, through a section-ring identification
compatible with the original projection. The section-field action and power
basis are transported internally. -/
theorem s2e_c1_affine_normalization_etale_in_original_field
    {T X : Scheme} [IsAffine X] (f : T ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDomain Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (K L : Type*) [Field K] [Field L]
    [Algebra Γ(X, ⊤) K] [IsFractionRing Γ(X, ⊤) K]
    [Algebra Γ(X, ⊤) L] [Algebra K L] [IsScalarTower Γ(X, ⊤) K L]
    [Algebra.IsSeparable K L]
    (E : Γ(T, f ⁻¹ᵁ ⊤) ≃+* L)
    (hE : ∀ r : Γ(X, ⊤), E ((f.app ⊤).hom r) = algebraMap Γ(X, ⊤) L r)
    (B : PowerBasis K L) (a b : ℤ) (m : ℕ)
    (hm : 0 < m) (hdim : Module.finrank K L = m) (hab : (m : ℤ) ∣ a + b)
    (x : Γ(X, ⊤)) (hx : algebraMap Γ(X, ⊤) K x ≠ 0)
    (v u d : Γ(X, ⊤)ˣ) (hd : (d : Γ(X, ⊤)) = (m : Γ(X, ⊤)))
    (hz : B.gen ^ m = algebraMap K L
      ((algebraMap Γ(X, ⊤) K x) ^ a *
        (algebraMap Γ(X, ⊤) K x * algebraMap Γ(X, ⊤) K (v : Γ(X, ⊤))) ^ b *
        algebraMap Γ(X, ⊤) K (u : Γ(X, ⊤)))) :
    Etale f.fromNormalization := by
  have hL : IsField Γ(T, f ⁻¹ᵁ ⊤) := E.toMulEquiv.isField (Field.toIsField L)
  letI := hL.toField
  letI := (f.app ⊤).hom.toAlgebra
  obtain ⟨hKA, ht, e, he⟩ := s2e_c1_compatible_field_tower_transport
    (R := Γ(X, ⊤)) (K := K) E hE
  letI := hKA
  letI := ht
  letI : Algebra.IsSeparable K Γ(T, f ⁻¹ᵁ ⊤) := AlgEquiv.Algebra.isSeparable e.symm
  let Q := B.map e.symm
  have hdimQ : Module.finrank K Γ(T, f ⁻¹ᵁ ⊤) = m :=
    e.toLinearEquiv.finrank_eq.trans hdim
  apply s2e_c1_affine_normalization_etale_of_signed_paired_equation
    f hL K Q a b m hm hdimQ hab x hx v u d hd
  apply e.injective
  rw [map_pow, e.commutes]
  change (e (e.symm B.gen)) ^ m = _
  rw [e.apply_symm_apply]
  exact hz

end HodgeLean.Foundations.Program
