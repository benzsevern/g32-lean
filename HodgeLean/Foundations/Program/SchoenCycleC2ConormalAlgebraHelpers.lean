import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.LocalRing.Module

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The conormal module of a surjection between formally smooth algebras is projective. -/
theorem s2e_conormal_projective_of_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) [Algebra.FormallySmooth R P.Ring]
    [Algebra.FormallySmooth R S] : Module.Projective S P.Cotangent := by
  obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp inferInstance
  exact Module.Projective.of_split P.cotangentComplex l hl

/-- Over a local quotient ring the conormal module of a Noetherian formally
smooth algebra surjection is free. -/
theorem s2e_conormal_free_of_local_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
    (P : Algebra.Extension R S) [IsNoetherianRing P.Ring]
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R S] :
    Module.Free S P.Cotangent := by
  letI : Module.Projective S P.Cotangent := s2e_conormal_projective_of_formallySmooth P
  letI : Module.Finite S P.Cotangent := Algebra.Extension.Cotangent.finite (P := P) (IsNoetherian.noetherian _)
  exact Module.free_of_flat_of_isLocalRing

end HodgeLean.Foundations.Program
