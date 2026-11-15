import HodgeLean.Foundations.Program.SchoenCycleC2ConormalAlgebraHelpers
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The cotangent sequence of a formally smooth algebra quotient splits. -/
theorem s2e_conormal_split_of_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) [Algebra.FormallySmooth R P.Ring]
    [Algebra.FormallySmooth R S] :
    ∃ e : P.CotangentSpace ≃ₗ[S] P.Cotangent × Ω[S⁄R],
      P.cotangentComplex = e.symm.toLinearMap ∘ₗ LinearMap.inl S _ _ ∧
      P.toKaehler = LinearMap.snd S _ _ ∘ₗ e.toLinearMap := by
  obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp inferInstance
  exact ⟨_, (P.exact_cotangentComplex_toKaehler.splitInjectiveEquiv
    P.toKaehler_surjective ⟨l, hl⟩).property⟩

/-- Over a local ring, the conormal and quotient differential ranks add to
that of the ambient differentials after scalar extension. -/
theorem s2e_conormal_finrank_add_of_local_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S]
    (P : Algebra.Extension R S) [IsNoetherianRing P.Ring]
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R S]
    [Module.Finite S Ω[S⁄R]] :
    Module.finrank S P.Cotangent + Module.finrank S Ω[S⁄R] =
      Module.finrank S P.CotangentSpace := by
  let : Module.Free S P.Cotangent := s2e_conormal_free_of_local_formallySmooth P
  let : Module.Finite S P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) (IsNoetherian.noetherian _)
  let : Module.Free S Ω[S⁄R] := Module.free_of_flat_of_isLocalRing
  obtain ⟨e, _, _⟩ := s2e_conormal_split_of_formallySmooth P
  rw [e.finrank_eq, Module.finrank_prod]

/-- A quotient of local smooth algebras with differential ranks `n + k`
and `n` has a conormal basis indexed by `Fin k`. -/
theorem s2e_conormal_basis_of_local_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S]
    (P : Algebra.Extension R S) [IsNoetherianRing P.Ring]
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R S]
    [Module.Finite S Ω[S⁄R]] (n k : ℕ)
    (hambient : Module.finrank S P.CotangentSpace = n + k)
    (hquotient : Module.finrank S Ω[S⁄R] = n) :
    Nonempty (Module.Basis (Fin k) S P.Cotangent) := by
  let : Module.Free S P.Cotangent := s2e_conormal_free_of_local_formallySmooth P
  let : Module.Finite S P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) (IsNoetherian.noetherian _)
  have h := s2e_conormal_finrank_add_of_local_formallySmooth P
  rw [hambient, hquotient, Nat.add_comm n k] at h
  have hrank : Module.finrank S P.Cotangent = k := Nat.add_right_cancel h
  exact ⟨Module.finBasisOfFinrankEq S P.Cotangent hrank⟩

end HodgeLean.Foundations.Program
