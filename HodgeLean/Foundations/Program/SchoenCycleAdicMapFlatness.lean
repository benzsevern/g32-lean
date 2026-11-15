import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues
import HodgeLean.Foundations.Program.SchoenCycleLocalAdicFaithfullyFlat
import HodgeLean.Foundations.Program.SchoenCycleFlatExtensionDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Bijectivity of the actual canonical adic map gives flatness of the original map into a Noetherian local target.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10; EGA IV, 2.5.1. -/
theorem s2e_actual_map_flat_of_adic_bijective
    (k R S : Type*) [CommRing k] [CommRing R] [IsNoetherianRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra k R] [Algebra k S]
    (I : Ideal R) (f : R →ₐ[k] S)
    (h : ∀ n r, r ∈ I ^ n → f r ∈ IsLocalRing.maximalIdeal S ^ n)
    (hbij : Function.Bijective (s2e_adic_algebra_map I (IsLocalRing.maximalIdeal S) f h)) :
    letI : Algebra R S := f.toAlgebra
    Module.Flat R S := by
  let D := AdicCompletion I R
  let A := AdicCompletion (IsLocalRing.maximalIdeal S) S
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R A := ((algebraMap S A).comp f.toRingHom).toAlgebra
  letI hRSA : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let G : D →ₐ[R] A :=
    { toRingHom := (s2e_adic_algebra_map I (IsLocalRing.maximalIdeal S) f h).toRingHom
      commutes' := fun r => s2e_adic_algebra_map_of I (IsLocalRing.maximalIdeal S) f h r }
  let E := AlgEquiv.ofBijective G hbij
  letI hRA : Module.Flat R A := Module.Flat.of_linearEquiv E.symm.toLinearEquiv
  letI hSA : Module.FaithfullyFlat S A := s2e_local_adic_faithfullyFlat S
  have hflat : Module.Flat R S := @s2e_flat_of_faithfullyFlat_extension R S A _ _ _ _ _ _ hRSA hRA hSA
  exact hflat

#print axioms s2e_actual_map_flat_of_adic_bijective
end HodgeLean.Foundations.Program
