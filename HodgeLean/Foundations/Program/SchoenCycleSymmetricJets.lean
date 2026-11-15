import HodgeLean.Foundations.Program.SchoenCycleInvariantJets
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Data.Fintype.Perm

/-! # Elementary coefficient representatives of symmetric finite jets -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Permutations act on polynomial coordinates by renaming variables.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2. -/
def s2e_polynomial_permutation_action (σ : Type*) :
    Equiv.Perm σ →* (MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ) where
  toFun g := renameEquiv ℂ g
  map_one' := by
    apply AlgEquiv.ext
    intro p
    change rename id p = p
    rw [rename_id]
    rfl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro p
    change rename (g * h) p = rename g (rename h p)
    rw [rename_rename]
    rfl

/-- A polynomial class invariant under permutations has an elementary
coefficient representative, including classes in nonreduced neighbourhoods.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1. -/
theorem s2e_symmetric_jet_coefficient_representative
    (σ : Type*) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (p : MvPolynomial σ ℂ) (hp : ∀ g : Equiv.Perm σ, rename g p - p ∈ I) :
    ∃ q : MvPolynomial (Fin (Fintype.card σ)) ℂ,
      ((esymmAlgHom σ ℂ (Fintype.card σ) q : symmetricSubalgebra σ ℂ) :
        MvPolynomial σ ℂ) - p ∈ I := by
  classical
  obtain ⟨y, hy, hi⟩ := s2e_invariant_jet_representative (Equiv.Perm σ)
    (MvPolynomial σ ℂ) (s2e_polynomial_permutation_action σ) I p hp
  have hsym : IsSymmetric y := hy
  let e := esymmAlgEquiv σ ℂ (n := Fintype.card σ) rfl
  refine ⟨e.symm ⟨y, hsym⟩, ?_⟩
  have he := e.apply_symm_apply ⟨y, hsym⟩
  have hev := congrArg (fun z : symmetricSubalgebra σ ℂ => (z : MvPolynomial σ ℂ)) he
  change ((e (e.symm ⟨y, hsym⟩) : symmetricSubalgebra σ ℂ) : MvPolynomial σ ℂ) - p ∈ I
  rw [hev]
  exact hi

end HodgeLean.Foundations.Program
