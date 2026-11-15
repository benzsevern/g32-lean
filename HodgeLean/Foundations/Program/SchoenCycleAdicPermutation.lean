import HodgeLean.Foundations.Program.SchoenCycleAdicRingMaps
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Complex.Basic

/-! # Coordinate renaming on polynomial adic rings -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Renaming variables induces an endomorphism on the polynomial adic ring.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
def s2e_polynomial_adic_rename {ι : Type*} (σ : ι → ι) :
    AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ) →+*
      AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ) :=
  s2e_adic_ring_map (idealOfVars ι ℂ) (idealOfVars ι ℂ)
    (rename σ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ).toRingHom (by
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change rename σ (MvPolynomial.X i) ∈ Ideal.span (Set.range (MvPolynomial.X : ι → MvPolynomial ι ℂ))
    rw [rename_X]
    exact Ideal.subset_span (Set.mem_range_self (σ i)))

#print axioms s2e_polynomial_adic_rename
/-- Adic coordinate renaming respects composition on all adic elements.
Source: Mathlib, MvPolynomial.rename_rename and finite quotient evaluation. -/
theorem s2e_polynomial_adic_rename_comp {ι : Type*} (σ τ : ι → ι)
    (z : AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) :
    s2e_polynomial_adic_rename σ (s2e_polynomial_adic_rename τ z) =
      s2e_polynomial_adic_rename (σ ∘ τ) z := by
  apply AdicCompletion.ext_evalₐ
  intro n
  unfold s2e_polynomial_adic_rename
  rw [s2e_adic_ring_map_eval, s2e_adic_ring_map_eval, s2e_adic_ring_map_eval]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (idealOfVars ι ℂ) n z)
  rw [← hp]
  change Ideal.Quotient.mk _ (rename σ (rename τ p)) = Ideal.Quotient.mk _ (rename (σ ∘ τ) p)
  rw [rename_rename]

#print axioms s2e_polynomial_adic_rename_comp
/-- Identity renaming acts trivially on the polynomial adic ring.
Source: Mathlib, MvPolynomial.rename_id and finite quotient evaluation. -/
theorem s2e_polynomial_adic_rename_id {ι : Type*}
    (z : AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) :
    s2e_polynomial_adic_rename id z = z := by
  apply AdicCompletion.ext_evalₐ
  intro n
  unfold s2e_polynomial_adic_rename
  rw [s2e_adic_ring_map_eval]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (idealOfVars ι ℂ) n z)
  rw [← hp]
  change Ideal.Quotient.mk _ (rename id p) = Ideal.Quotient.mk _ p
  rw [rename_id]
  rfl

#print axioms s2e_polynomial_adic_rename_id
/-- Adic coordinate renaming fixes the complex scalars.
Source: Mathlib, MvPolynomial.rename_C and AdicCompletion.algebraMap_apply. -/
theorem s2e_polynomial_adic_rename_scalar {ι : Type*} (σ : ι → ι) (c : ℂ) :
    s2e_polynomial_adic_rename σ
      (algebraMap ℂ (AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) c) =
    algebraMap ℂ (AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) c := by
  change s2e_polynomial_adic_rename σ (AdicCompletion.of (idealOfVars ι ℂ) _ (C c)) =
    AdicCompletion.of (idealOfVars ι ℂ) _ (C c)
  unfold s2e_polynomial_adic_rename
  rw [s2e_adic_ring_map_of]
  change AdicCompletion.of (idealOfVars ι ℂ) _ (rename σ (C c)) = _
  rw [rename_C]

#print axioms s2e_polynomial_adic_rename_scalar
/-- Coordinate permutations act by complex algebra automorphisms on the
polynomial adic ring.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
def s2e_polynomial_adic_permutation_action (ι : Type*) :
    Equiv.Perm ι →* (AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ) ≃ₐ[ℂ]
      AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) where
  toFun σ :=
    { s2e_polynomial_adic_rename σ with
      invFun := s2e_polynomial_adic_rename σ.symm
      left_inv := fun z => by
        change s2e_polynomial_adic_rename σ.symm (s2e_polynomial_adic_rename σ z) = z
        rw [s2e_polynomial_adic_rename_comp]
        simpa only [Equiv.symm_comp_self] using s2e_polynomial_adic_rename_id z
      right_inv := fun z => by
        change s2e_polynomial_adic_rename σ (s2e_polynomial_adic_rename σ.symm z) = z
        rw [s2e_polynomial_adic_rename_comp]
        simpa only [Equiv.self_comp_symm] using s2e_polynomial_adic_rename_id z
      commutes' := s2e_polynomial_adic_rename_scalar σ }
  map_one' := by
    apply AlgEquiv.ext
    intro z
    exact s2e_polynomial_adic_rename_id z
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro z
    exact (s2e_polynomial_adic_rename_comp σ τ z).symm

#print axioms s2e_polynomial_adic_permutation_action
end HodgeLean.Foundations.Program
