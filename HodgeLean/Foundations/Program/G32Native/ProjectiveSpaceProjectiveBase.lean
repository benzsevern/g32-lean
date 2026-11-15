import HodgeLean.Foundations.SegreProjective
import HodgeLean.Foundations.Program.SchoenProjectiveBaseIso

/-! Projectivity of projective space over a projective base. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective space on the source is the pullback of projective space on the target. -/
def g32l4_projectiveSpace_baseChangeIso {X S : Scheme.{0}} (K : Type) (f : X ⟶ S) :
    ProjectiveSpace K X ≅ pullback f (ProjectiveSpace.toBase K S) where
  hom := pullback.lift (ProjectiveSpace.toBase K X)
    (pullback.lift (ProjectiveSpace.toBase K X ≫ f)
      (pullback.snd (terminal.from X) (terminal.from
        (Proj (MvPolynomial.homogeneousSubmodule K (ULift.{0} ℤ))))) (Subsingleton.elim _ _))
    (by simp [ProjectiveSpace.toBase])
  inv := pullback.lift (pullback.fst f (ProjectiveSpace.toBase K S))
    (pullback.snd f (ProjectiveSpace.toBase K S) ≫
      pullback.snd (terminal.from S) (terminal.from
        (Proj (MvPolynomial.homogeneousSubmodule K (ULift.{0} ℤ))))) (Subsingleton.elim _ _)
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [ProjectiveSpace.toBase]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [ProjectiveSpace.toBase]
    · apply pullback.hom_ext
      · simp [ProjectiveSpace.toBase, pullback.condition]
      · simp [ProjectiveSpace.toBase]

/-- Finite projective space over a projective base is projective over the original target. -/
theorem g32l4_projectiveSpace_over_projective {X S : Scheme.{0}}
    (f : X ⟶ S) [IsProjective f] (m : ℕ) :
    IsProjective (ProjectiveSpace.toBase (Fin (m + 1)) X ≫ f) := by
  let K := Fin (m + 1)
  haveI : IsProjective (ProjectiveSpace.toBase K S) :=
    ⟨⟨⟨m, 𝟙 _, by simp [K]⟩⟩⟩
  haveI : IsProjective (pullback.fst f (ProjectiveSpace.toBase K S) ≫ f) :=
    spec_g3c_isProjective_pullback f (ProjectiveSpace.toBase K S)
  have h := s2_projective_precomp_iso
    (g32l4_projectiveSpace_baseChangeIso K f).hom
    (pullback.fst f (ProjectiveSpace.toBase K S) ≫ f)
  simpa only [g32l4_projectiveSpace_baseChangeIso, Category.assoc, pullback.lift_fst_assoc] using h

end HodgeLean.Foundations.Program
