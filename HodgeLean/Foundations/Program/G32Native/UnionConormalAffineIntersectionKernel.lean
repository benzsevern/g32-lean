import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineKernelInf
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The intersection equation in affine kernel coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The intersection equation gives the supremum of the affine ring kernels. -/
lemma unionConormal_affine_kernel_sup
    {V X T₁ T₂ : Scheme} [IsAffine V]
    (u : X ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [QuasiCompact u] [QuasiCompact t₁] [QuasiCompact t₂]
    (h : u.ker = t₁.ker ⊔ t₂.ker) :
    RingHom.ker u.appTop.hom = RingHom.ker t₁.appTop.hom ⊔ RingHom.ker t₂.appTop.hom := by
  have he := congrArg (fun I : V.IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top V⟩) h
  simpa only [Scheme.Hom.appTop, Scheme.Hom.ker_apply,
    Scheme.IdealSheafData.ideal_sup, Pi.sup_apply] using he

/-- The intersection equation persists under ambient open restriction. -/
lemma unionConormal_restrict_kernel_sup
    {V X T₁ T₂ : Scheme}
    (u : X ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [QuasiCompact u] [QuasiCompact t₁] [QuasiCompact t₂]
    (h : u.ker = t₁.ker ⊔ t₂.ker) (U : V.Opens) :
    (u ∣_ U).ker = (t₁ ∣_ U).ker ⊔ (t₂ ∣_ U).ker := by
  ext W
  simp only [Scheme.ker_morphismRestrict_ideal, h,
    Scheme.IdealSheafData.ideal_sup, Pi.sup_apply]

/-- For a surjective ambient ring map, the intersection kernel is generated
by the first component kernel. -/
lemma unionConormal_intersection_kernel_map
    {R A C D : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing D]
    (q : R →+* A) (r : R →+* C) (s : C →+* D)
    (hr : Function.Surjective r)
    (h : RingHom.ker (s.comp r) = RingHom.ker q ⊔ RingHom.ker r) :
    (RingHom.ker q).map r = RingHom.ker s := by
  apply (Ideal.comap_injective_of_surjective r hr)
  rw [Ideal.comap_map_of_surjective _ hr, RingHom.comap_ker, h]
  rfl

end HodgeLean.Foundations.Program.G32Native
