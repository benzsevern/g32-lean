import HodgeLean.Foundations.Program.G32Native.PairedConormalProjectiveLift
import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeStabilizedFrame

/-! # Finite free extensions on polynomial projective space

The section is constructed for the original quotient arrow, one basis
vector at a time, using the existing degree-zero twisting-sheaf vanishing.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- A finite free quotient has a section when the kernel is finite free on
polynomial projective space.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1, degree zero;
vanishing of the first cohomology of the structure sheaf. -/
theorem paired_c3_free_extension_section
    (R : Type) [CommRing R] (d : ℕ)
    (S : ShortComplex
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R)).Modules)
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (I J : Type) [Finite I]
    (e₁ : S.X₁ ≅ SheafOfModules.free I)
    (e₃ : S.X₃ ≅ SheafOfModules.free J) :
    ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 _ := by
  have hlift (j : J) := conormal_polynomial_projective_unit_lift R d S hS I e₁
    (SheafOfModules.ιFree j ≫ e₃.inv)
  choose l hl using hlift
  let a : SheafOfModules.free J ⟶ S.X₂ := Sigma.desc l
  have ha : a ≫ S.g = e₃.inv := by
    apply Sigma.hom_ext
    intro j
    simpa only [a, Category.assoc, Sigma.ι_desc_assoc, SheafOfModules.ιFree] using hl j
  refine ⟨e₃.hom ≫ a, ?_⟩
  rw [Category.assoc, ha, e₃.hom_inv_id]

/-- A specified exact extension of free modules gives a free frame of the
middle module, with the sum of the two ranks.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1, degree zero. -/
def pairedC3FreeExtensionFrame
    (R : Type) [CommRing R] (d : ℕ)
    (S : ShortComplex
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R)).Modules)
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (a b : ℕ)
    (e₁ : S.X₁ ≅ SheafOfModules.free (Fin a))
    (e₃ : S.X₃ ≅ SheafOfModules.free (Fin b)) :
    S.X₂ ≅ SheafOfModules.free (Fin (a + b)) := by
  let h := paired_c3_free_extension_section R d S hS (Fin a) (Fin b) e₁ e₃
  let s := Classical.choose h
  have hs := Classical.choose_spec h
  let split := ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f
  exact split.isoBinaryBiproduct ≪≫ biprod.mapIso e₁ e₃ ≪≫
    biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso (Fin a) (Fin b) ≪≫
    (SheafOfModules.freeFunctor).mapIso (finSumFinEquiv.toIso)

#print axioms paired_c3_free_extension_section
#print axioms pairedC3FreeExtensionFrame
end HodgeLean.Foundations.Program.G32Native
