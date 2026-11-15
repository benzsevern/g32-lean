import HodgeLean.Foundations.Program.SchoenTowerL1aCoefficientHelpers
import HodgeLean.Foundations.Program.SchoenTowerOverSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Elementary symmetric sections descend through the actual affine quotient
presentation with its specified permutation pullbacks.
Source: Schoen (1988), Lemma 2.2, printed p. 13. -/
theorem s2v_i2a_ordered_coefficient_descent
    (U V : Over (Spec ↧ℂ)) (h : ℕ) (q : V ⟶ U)
    (ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V))
    (z : Fin (h + 1) → Γ(V.left, ⊤))
    (hinj : Function.Injective q.left.appTop.hom)
    (himage : ∀ s : Γ(V.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
      ∀ τ, (ρ τ).left.appTop.hom s = s)
    (hcov : ∀ τ i, (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i)) :
    ∃! c : Fin (h + 1) → Γ(U.left, ⊤), ∀ j,
      q.left.appTop.hom (c j) =
        MvPolynomial.aeval (R := ℂ) z
          (MvPolynomial.esymm (Fin (h + 1)) ℂ (j.val + 1)) := by
  let ρR (τ : Equiv.Perm (Fin (h + 1))) := (ρ τ⁻¹).left.appTop.hom
  have hR (τ : Equiv.Perm (Fin (h + 1))) :
      (ρR τ).comp (algebraMap ℂ Γ(V.left, ⊤)) = algebraMap ℂ Γ(V.left, ⊤) := by
    ext a
    exact (s2t_overSectionsAlgHom (ρ τ⁻¹)).commutes a
  have hz (τ : Equiv.Perm (Fin (h + 1))) (i : Fin (h + 1)) :
      ρR τ (z i) = z (τ i) := by
    simpa only [ρR, inv_inv] using hcov τ⁻¹ i
  have hi (s : Γ(V.left, ⊤)) : s ∈ Set.range q.left.appTop.hom ↔
      ∀ τ, ρR τ s = s := by
    constructor
    · intro hs τ
      exact (himage s).mp hs τ⁻¹
    · intro hs
      apply (himage s).mpr
      intro τ
      simpa only [ρR, inv_inv] using hs τ⁻¹
  exact s2v_l1a_symmetric_coefficient_descent (algebraMap ℂ Γ(V.left, ⊤))
    q.left.appTop.hom hinj h z ρR hR hz hi

end HodgeLean.Foundations.Program
