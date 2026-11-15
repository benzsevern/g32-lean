import HodgeLean.Foundations.Program.SchoenCycleU1LocalTangent
import Mathlib.RingTheory.Unramified.Locus

/-! # Maximal-point detection of unramifiedness -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Residue-field tangent tests at maximal points suffice for an essentially
finite-type algebra. The cotangent module has closed support.
Source: Mathlib, `Algebra.unramifiedLocus_eq_compl_support`,
`Module.support_eq_zeroLocus`; Stacks Project, Tag 00UM. -/
theorem s2e_u1_unramified_of_maximal_residue_derivations
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.EssFiniteType A B]
    (hder : ∀ (q : Ideal B) [q.IsMaximal],
      ∀ d : Derivation A (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)), d = 0) :
    Algebra.FormallyUnramified A B := by
  classical
  by_contra hn
  have hJ : Module.annihilator B (KaehlerDifferential A B) ≠ ⊤ := by
    intro he
    exact hn ⟨Module.annihilator_eq_top_iff.mp he⟩
  obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal _ hJ
  letI := hq
  let x : PrimeSpectrum B := ⟨q, hq.isPrime⟩
  have hs : x ∈ Module.support B (KaehlerDifferential A B) := by
    rw [Module.support_eq_zeroLocus]
    exact hJq
  have hu : x ∈ Algebra.unramifiedLocus A B :=
    s2e_u1_local_unramified_of_residue_derivations A (Localization.AtPrime q) (hder q)
  rw [Algebra.unramifiedLocus_eq_compl_support] at hu
  exact hu hs

end HodgeLean.Foundations.Program
