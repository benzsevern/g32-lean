import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The union equation on affine top sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The kernel-infimum equation gives the same intersection of ring kernels
on top sections of an affine ambient scheme. -/
lemma unionConormal_affine_kernel_inf
    {V T T₁ T₂ : Scheme} [IsAffine V]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [QuasiCompact t] [QuasiCompact t₁] [QuasiCompact t₂]
    (hunion : t.ker = t₁.ker ⊓ t₂.ker) :
    RingHom.ker t.appTop.hom = RingHom.ker t₁.appTop.hom ⊓ RingHom.ker t₂.appTop.hom := by
  have h := congrArg (fun I : V.IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top V⟩) hunion
  simpa only [Scheme.Hom.appTop, Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_inf, Pi.inf_apply] using h

/-- Restricting the ambient scheme retains the union's kernel-infimum equation. -/
lemma unionConormal_restrict_kernel_inf
    {V T T₁ T₂ : Scheme}
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [QuasiCompact t] [QuasiCompact t₁] [QuasiCompact t₂]
    (hunion : t.ker = t₁.ker ⊓ t₂.ker) (U : V.Opens) :
    (t ∣_ U).ker = (t₁ ∣_ U).ker ⊓ (t₂ ∣_ U).ker := by
  ext W
  simp only [Scheme.ker_morphismRestrict_ideal, hunion,
    Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]

#print axioms unionConormal_affine_kernel_inf
#print axioms unionConormal_restrict_kernel_inf
end HodgeLean.Foundations.Program.G32Native
