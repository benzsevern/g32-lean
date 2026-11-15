import HodgeLean.Foundations.Program.G32Native.PairedResidualHyperplaneSheafTransport
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Transport of an elementary conormal sequence to standard coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An elementary modification becomes the standard one under a supplied scheme normalization.
The middle module is retained by an explicit pullback isomorphism.
Source: Hartshorne, Algebraic Geometry, II.5 and II.7.1. -/
theorem residual_hyperplane_sequence_transport_iso (k : ℕ)
    (n : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (I : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData)
    (hI : I.comap n.hom.left = s2e_hyperplaneIdeal k)
    (M : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)
    (f : (SheafOfModules.free
      (R := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf) (Fin k) :
        (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules) ⟶ M)
    (g : M ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf))
    (hfg : f ≫ g = 0) (hseq : (ShortComplex.mk f g hfg).ShortExact) :
    ∃ (M' : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)
      (_ : M ≅ (Scheme.Modules.pullback n.inv.left).obj M')
      (f' : (SheafOfModules.free
        (R := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf) (Fin k) :
          (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules) ⟶ M')
      (g' : M' ⟶ (Scheme.Modules.pushforward (s2e_hyperplaneIdeal k).subschemeι).obj
        (SheafOfModules.unit (s2e_hyperplaneIdeal k).subscheme.ringCatSheaf))
      (hz : f' ≫ g' = 0), (ShortComplex.mk f' g' hz).ShortExact := by
  let e : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) ≅
      (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) :=
    ⟨n.inv.left, n.hom.left, congrArg (fun f => f.left) n.inv_hom_id,
      congrArg (fun f => f.left) n.hom_inv_id⟩
  let F := Scheme.Modules.pullback e.inv
  haveI := unionConormal_isoPullback_isEquivalence e.inv
  let M' := F.obj M
  let EM : M ≅ (Scheme.Modules.pullback e.hom).obj M' :=
    ((Scheme.Modules.pullbackComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pullbackId _).app M).symm
  letI : (TopologicalSpace.Opens.map e.inv.base).Final := inferInstance
  letI : (SheafOfModules.pushforward e.inv.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward e.inv).IsRightAdjoint
  let EF := SheafOfModules.pullbackObjFreeIso e.inv.toRingCatSheafHom (Fin k)
  have hK : I.comap e.inv = s2e_hyperplaneIdeal k :=
    hI
  let EG := residualComapStructureSheafIso e.symm I ≪≫
    eqToIso (congrArg (fun I : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData =>
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) hK)
  let f' := EF.inv ≫ F.map f
  let g' := F.map g ≫ EG.hom
  have hz : f' ≫ g' = 0 := by
    simp only [f', g', Category.assoc, ← Category.assoc (F.map f),
      ← F.map_comp, hfg, F.map_zero, zero_comp, comp_zero]
  refine ⟨M', EM, f', g', hz, ?_⟩
  let E : (ShortComplex.mk f g hfg).map F ≅ ShortComplex.mk f' g' hz :=
    ShortComplex.isoMk EF (Iso.refl _) EG (by
      change EF.hom ≫ f' = F.map f ≫ (Iso.refl _).hom
      simp only [f', Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]) (by
      change (Iso.refl _).hom ≫ g' = F.map g ≫ EG.hom
      simp only [g', Iso.refl_hom, Category.id_comp])
  exact ShortComplex.shortExact_of_iso E (hseq.map_of_exact F)

#print axioms residual_hyperplane_sequence_transport_iso
end HodgeLean.Foundations.Program.G32Native
