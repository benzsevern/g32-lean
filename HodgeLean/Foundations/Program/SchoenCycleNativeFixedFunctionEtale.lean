import HodgeLean.Foundations.Program.SchoenCycleIdentifiedStabilizerEtale
import HodgeLean.Foundations.Program.SchoenCycleFixedScalarAlgebraFinite
import HodgeLean.Foundations.Program.SchoenCycleFixedFunctionScalarTowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Stabilizer etaleness retains the original complex invariant subalgebra and its canonical quotient-base map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1; EGA IV, 17.6.1. -/
theorem s2e_native_fixed_function_etale_of_stabilizer_eq
    (A C G : Type*) [CommRing A] [CommRing C] [Algebra ℂ A] [Algebra ℂ C]
    [Algebra A C] [IsScalarTower ℂ A C] [IsNoetherianRing A] [Module.Finite A C]
    [Group G] [Fintype G] [MulSemiringAction G C]
    [SMulCommClass G ℂ C] [SMulCommClass G A C] [Algebra.IsInvariant A C G]
    (hinj : Function.Injective (algebraMap A C)) (P : Ideal C) [P.IsMaximal]
    (H : Subgroup G)
    (hH : H = MulAction.stabilizer G
      (⟨P, MulAction.mem_orbit_self P⟩ : MulAction.orbit G P)) :
    let S := FixedPoints.subalgebra ℂ C H
    letI : Algebra A S := (s2e_fixed_action_base_map ℂ A C H).toAlgebra
    ∀ ε : Localization.AtPrime (P.under S) →ₐ[ℂ] ℂ,
      Algebra.IsEtaleAt A (P.under S) := by
  dsimp only
  subst H
  let H := MulAction.stabilizer G
    (⟨P, MulAction.mem_orbit_self P⟩ : MulAction.orbit G P)
  let S := FixedPoints.subalgebra ℂ C H
  letI : Algebra A S := (s2e_fixed_action_base_map ℂ A C H).toAlgebra
  letI : IsScalarTower ℂ A S := (s2e_fixed_function_scalar_towers ℂ A C H).1
  letI : IsScalarTower A S C := (s2e_fixed_function_scalar_towers ℂ A C H).2
  letI : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  letI : Module.Finite A S := s2e_fixed_scalar_algebra_module_finite ℂ A C H
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  letI : Algebra.FinitePresentation A S := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  letI : Algebra.IsIntegral A C := Algebra.IsInvariant.isIntegral A C G
  letI : Algebra.IsIntegral S C := Algebra.IsInvariant.isIntegral S C H
  let I := P.under A
  let Q := P.under S
  letI : I.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  letI : Q.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  letI : Q.LiesOver I := inferInstance
  intro ε
  obtain ⟨h, hbij⟩ := s2e_stabilizer_fixed_function_adic_map_bijective A C G hinj P
  exact s2e_isEtaleAt_of_localized_adic_bijective ℂ A S I Q h hbij ε

#print axioms s2e_native_fixed_function_etale_of_stabilizer_eq
end HodgeLean.Foundations.Program
