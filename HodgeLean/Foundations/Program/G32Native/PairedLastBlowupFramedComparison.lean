import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineFrames
import HodgeLean.Foundations.Program.G32Native.UnionConormalCartesianComparisonEpi
import Mathlib.RingTheory.OrzechProperty

/-! # Conormal comparison of equal finite rank on affine charts

The morphism tested here is the natural comparison, not an independently
chosen identification of bundles. No flatness of the ambient map is used.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- An epic map between equally framed affine associated sheaves is invertible.
Source: Orzech, Onto endomorphisms are isomorphisms, American Mathematical
Monthly 78 (1971), 357–362;
the surjective endomorphism property for finite modules over a commutative ring. -/
theorem paired_affine_framed_epi_isIso
    (A : CommRingCat) (M N : ModuleCat A) (f : M ⟶ N)
    [Epi ((tilde.functor A).map f)] (k : ℕ)
    (eM : tilde M ≅ (SheafOfModules.free (R := (Spec A).ringCatSheaf) (Fin k) :
      (Spec A).Modules))
    (eN : tilde N ≅ (SheafOfModules.free (R := (Spec A).ringCatSheaf) (Fin k) :
      (Spec A).Modules)) : IsIso ((tilde.functor A).map f) := by
  letI : Module.Finite A N := unionAffineFrame_finite A N k eN
  let e : M ≃ₗ[A] N :=
    (unionAffineFrameEquiv A M k eM).trans (unionAffineFrameEquiv A N k eN).symm
  haveI : Epi f := (tilde.functor A).epi_of_epi_map inferInstance
  have hs := (ModuleCat.epi_iff_surjective f).mp inferInstance
  have hi := OrzechProperty.injective_of_surjective_of_injective
    e.toLinearMap f.hom e.injective hs
  haveI : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr ⟨hi, hs⟩
  infer_instance

/-- The natural comparison in a cartesian immersion diagram is invertible
when its affine source and target have the same finite frame. The frame
hypotheses are local freeness data, not an assumption about this morphism.
Source: Hartshorne, Algebraic Geometry, II.8, conormal base change for
regular immersions of unchanged codimension. -/
theorem paired_affine_conormal_comparison_isIso
    {Q W W' : Scheme.{0}} (A : CommRingCat)
    (i : Q ⟶ W) (i' : Spec A ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) (g : Spec A ⟶ Q)
    (sq : CategoryTheory.IsPullback g i' i f)
    (M N : ModuleCat A)
    (eM : tilde M ≅ (Scheme.Modules.pullback g).obj (Conormal.sheaf i))
    (eN : tilde N ≅ Conormal.sheaf i')
    (k : ℕ)
    (bM : tilde M ≅ (SheafOfModules.free (R := (Spec A).ringCatSheaf) (Fin k) :
      (Spec A).Modules))
    (bN : tilde N ≅ (SheafOfModules.free (R := (Spec A).ringCatSheaf) (Fin k) :
      (Spec A).Modules)) :
    IsIso (Conormal.comparisonMap i i' f g sq.w) := by
  let a := Conormal.comparisonMap i i' f g sq.w
  haveI : Epi a := unionConormal_comparison_epi_of_isPullback i i' f g sq
  let b := eM.hom ≫ a ≫ eN.inv
  let u := (tilde.functor A).preimage b
  have hu : (tilde.functor A).map u = b := (tilde.functor A).map_preimage b
  haveI : Epi ((tilde.functor A).map u) := by
    rw [hu]
    dsimp only [b]
    infer_instance
  haveI := paired_affine_framed_epi_isIso A M N u k bM bN
  haveI : IsIso b := by rw [← hu]; infer_instance
  have ha : a = eM.inv ≫ b ≫ eN.hom := by
    simp only [b, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  change IsIso a
  rw [ha]
  infer_instance

#print axioms paired_affine_framed_epi_isIso
#print axioms paired_affine_conormal_comparison_isIso
end HodgeLean.Foundations.Program.G32Native
