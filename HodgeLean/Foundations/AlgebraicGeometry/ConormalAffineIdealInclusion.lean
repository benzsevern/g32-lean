import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineFlatIdeal

/-! # Global sections detect maps from associated module sheaves
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Conormal

/-- Global sections detect morphisms from a module sheaf with invertible affine counit. -/
lemma affineModuleHom_ext (R : CommRingCat.{0}) {M N : (Spec R).Modules}
    [IsIso M.fromTildeΓ] (a b : M ⟶ N)
    (h : (moduleSpecΓFunctor (R := R)).map a = (moduleSpecΓFunctor (R := R)).map b) :
    a = b := by
  apply (cancel_epi M.fromTildeΓ).mp
  calc
    M.fromTildeΓ ≫ a = (tilde.functor R).map
        ((moduleSpecΓFunctor (R := R)).map a) ≫ N.fromTildeΓ :=
      ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality a).symm
    _ = (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map b) ≫ N.fromTildeΓ := by
      rw [h]
    _ = M.fromTildeΓ ≫ b :=
      (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality b

/-- Affine kernel ideal inclusions can be compared on global sections. -/
lemma affineIdealHom_ext (R A : CommRingCat.{0}) (p : R ⟶ A)
    {N : (Spec R).Modules} (a b : idealModule (Spec.map p) ⟶ N)
    (h : (moduleSpecΓFunctor (R := R)).map a = (moduleSpecΓFunctor (R := R)).map b) :
    a = b := by
  have : IsIso (idealModule (Spec.map p)).fromTildeΓ :=
    HodgeLean.Foundations.Program.s2e_idealModule_spec_fromTilde_isIso R (Spec.map p)
  exact affineModuleHom_ext R a b h

/-- The associated affine kernel module recovers the actual ideal inclusion. -/
lemma affineIdealIso_inv_inclusion (R A : CommRingCat.{0}) (p : R ⟶ A) :
    (affineIdealIso R A p).inv ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (Spec.map p).toRingCatSheafHom) =
      (tilde.functor R).map (ModuleCat.ofHom (RingHom.ker p.hom).subtype) := by
  let M := idealModule (Spec.map p)
  let e := HodgeLean.Foundations.Program.s2e_affine_ideal_sections_equiv R A p
  let j := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (Spec.map p).toRingCatSheafHom)
  let adj := tilde.adjunction (R := R)
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _
    ((tilde.functor R).map e.symm.toModuleIso.hom ≫ M.fromTildeΓ ≫ j) = _
  rw [adj.homEquiv_naturality_right]
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm e.symm.toModuleIso.hom) ≫
    (moduleSpecΓFunctor (R := R)).map j = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change e.symm.toModuleIso.hom ≫ (moduleSpecΓFunctor (R := R)).map j =
    adj.unit.app _ ≫ (tilde.functor R ⋙ moduleSpecΓFunctor).map
      (ModuleCat.ofHom (RingHom.ker p.hom).subtype)
  rw [← adj.unit.naturality (ModuleCat.ofHom (RingHom.ker p.hom).subtype)]
  ext x
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).injective
  change (Scheme.ΓSpecIso R).hom (j.val.app (op ⊤) (e.symm x)) = _
  rw [← HodgeLean.Foundations.Program.s2e_idealModule_sections_equiv_coe]
  change (e (e.symm x)).val =
    (Scheme.ΓSpecIso R).hom ((adj.unit.app (ModuleCat.of R R)).hom x.val)
  rw [e.apply_symm_apply]
  change x.val = (Scheme.ΓSpecIso R).hom ((Scheme.ΓSpecIso R).inv x.val)
  rw [Iso.inv_hom_id_apply]

end AlgebraicGeometry.Conormal
