import HodgeLean.Foundations.Program.SchoenCycleCanonicalCoefficientAdicIso
import HodgeLean.Foundations.Program.SchoenCycleLocalAdicFaithfullyFlat
import HodgeLean.Foundations.Program.SchoenCycleFlatExtensionDescent
import Mathlib.RingTheory.MvPolynomial.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Actual represented cotangent coordinates give a flat polynomial scalar map whenever the actual local algebra has a coefficient formal model.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10; EGA IV, 2.5.1. -/
theorem s2e_polynomial_coordinates_flat_of_formal_model
    (k R σ : Type*) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [Finite σ]
    (E : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[k]
      AdicCompletion (idealOfVars σ k) (MvPolynomial σ k))
    (c : σ → IsLocalRing.maximalIdeal R)
    (b : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal R).toCotangent (c i)) :
    letI : Algebra (MvPolynomial σ k) R := (aeval (R := k) (fun i => (c i).val)).toAlgebra
    Module.Flat (MvPolynomial σ k) R := by
  let P := MvPolynomial σ k
  let I := idealOfVars σ k
  let D := AdicCompletion I P
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let f : P →ₐ[k] R := aeval (fun i => (c i).val)
  letI : Algebra P R := f.toAlgebra
  letI : Algebra P A := ((algebraMap R A).comp f.toRingHom).toAlgebra
  letI : IsScalarTower P R A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨h, hbij⟩ := s2e_canonical_coefficient_adic_map_bijective k R σ E c b hb
  let G : D →ₐ[P] A :=
    { toRingHom := (s2e_adic_algebra_map I (IsLocalRing.maximalIdeal R) f h).toRingHom
      commutes' := fun p => s2e_adic_algebra_map_of I (IsLocalRing.maximalIdeal R) f h p }
  let F := AlgEquiv.ofBijective G hbij
  letI : Module.Flat P A := Module.Flat.of_linearEquiv F.symm.toLinearEquiv
  letI : Module.FaithfullyFlat R A := s2e_local_adic_faithfullyFlat R
  exact s2e_flat_of_faithfullyFlat_extension P R A

#print axioms s2e_polynomial_coordinates_flat_of_formal_model
end HodgeLean.Foundations.Program
