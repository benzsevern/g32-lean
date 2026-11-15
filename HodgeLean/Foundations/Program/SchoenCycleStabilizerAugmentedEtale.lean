import HodgeLean.Foundations.Program.SchoenCycleStabilizerFixedFunctionAdic
import HodgeLean.Foundations.Program.SchoenCycleLocalizedAdicEtale
import HodgeLean.Foundations.Program.SchoenCycleFixedAlgebraFinite

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual prime stabilizer fixed-function algebra is étale over the quotient base at every augmented retained prime, without prescribed source coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1; EGA IV, 17.6.1. -/
theorem s2e_prime_stabilizer_fixed_function_etale
    (A C G : Type*) [CommRing A] [Algebra ℂ A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] [Module.Finite A C]
    [Group G] [Fintype G] [MulSemiringAction G C]
    [SMulCommClass G A C] [Algebra.IsInvariant A C G]
    (hinj : Function.Injective (algebraMap A C)) (P : Ideal C) [P.IsMaximal] :
    let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
    let H := MulAction.stabilizer G o
    let S := FixedPoints.subalgebra A C H
    letI : Algebra ℂ S := ((algebraMap A S).comp (algebraMap ℂ A)).toAlgebra
    let Q := P.under S
    let I := P.under A
    ∀ ε : Localization.AtPrime Q →ₐ[ℂ] ℂ, Algebra.IsEtaleAt A Q := by
  dsimp only
  let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
  let H := MulAction.stabilizer G o
  let S := FixedPoints.subalgebra A C H
  letI : Algebra ℂ S := ((algebraMap A S).comp (algebraMap ℂ A)).toAlgebra
  letI : IsScalarTower ℂ A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let I := P.under A
  let Q := P.under S
  letI : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  letI : Module.Finite A S := s2e_fixed_algebra_module_finite A C H
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  letI : Algebra.FinitePresentation A S := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  letI : Algebra.IsIntegral A C := Algebra.IsInvariant.isIntegral A C G
  letI : Algebra.IsIntegral S C := Algebra.IsInvariant.isIntegral S C H
  letI : I.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  letI : Q.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  letI : Q.LiesOver I := inferInstance
  intro ε
  obtain ⟨h, hbij⟩ := s2e_stabilizer_fixed_function_adic_map_bijective A C G hinj P
  exact s2e_isEtaleAt_of_localized_adic_bijective ℂ A S I Q h hbij ε

#print axioms s2e_prime_stabilizer_fixed_function_etale
end HodgeLean.Foundations.Program
