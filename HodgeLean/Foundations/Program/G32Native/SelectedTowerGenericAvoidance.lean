import HodgeLean.Foundations.WitnessSelection.SliceHelpers

/-! # The paired slice generic point on the initial unmarked open -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The paired hyperplane sections exclude the generic point, although their
closed intersections with the slice need not be empty.
Source: Schoen (1988), printed pp. 13–15; Hartshorne, Algebraic Geometry, I.1. -/
theorem selected_paired_slice_generic_open
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] (k r : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (B₀ : Over (Spec ↧ℂ))
    (ℓ₀ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B₀)
    (D : Fin (2 * r) → B₀.left.IdealSheafData)
    (hpair : ∀ i : Fin r,
      (D ⟨2 * i.val, by omega⟩).comap (eQ.hom ≫ ℓ₀).left =
      (D ⟨2 * i.val + 1, by omega⟩).comap (eQ.hom ≫ ℓ₀).left)
    (hsingle : ∀ i : Fin r, Nonempty (s2c_subscheme Q
      ((D ⟨2 * i.val, by omega⟩).comap (eQ.hom ≫ ℓ₀).left) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ)))) :
    ∃ U : B₀.left.Opens,
      (∀ x, x ∈ U ↔ ∀ t, x ∉ (D t).support) ∧
      (eQ.hom ≫ ℓ₀).left (genericPoint Q.left) ∈ U := by
  let U : B₀.left.Opens :=
    ⟨⋂ t, ((D t).support : Set B₀.left)ᶜ,
      isOpen_iInter_of_finite fun t => (D t).support.isClosed.isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · intro x
    exact Set.mem_iInter
  · apply Set.mem_iInter.mpr
    intro t
    exact HodgeLean.WitnessSelection.paired_generic_avoidance Q k r hk eQ
      B₀.left (eQ.hom ≫ ℓ₀).left D hpair hsingle t _ (genericPoint_spec Q.left)

#print axioms selected_paired_slice_generic_open
end HodgeLean.Foundations.Program.G32Native
