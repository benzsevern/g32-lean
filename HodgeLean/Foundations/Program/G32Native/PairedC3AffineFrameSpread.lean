import HodgeLean.Foundations.Program.G32Native.PairedC3FreeGeneratorSynthesis
import Mathlib.AlgebraicGeometry.Modules.Tilde
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineBasisSections

/-! # Affine global section frames on every original subopen -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- The arrow of original global sections intertwines finite synthesis on every open. -/
theorem paired_c3_free_generator_arrow_synthesis {X : Scheme.{0}}
    (M : X.Modules) {σ : Type} [Fintype σ] (g : σ → Γ(M, ⊤))
    (V : X.Opens) (c : σ → Γ(X, V)) :
    Scheme.Modules.Hom.app (X := X) (pairedC3FreeGeneratorArrow M g) V
      (pairedC3FiniteFrameSynthesis (pairedC3FreeGenerator X σ ⊤) V le_top c) =
      pairedC3FiniteFrameSynthesis g V le_top c := by
  change Scheme.Modules.Hom.app (X := X) (pairedC3FreeGeneratorArrow M g) V (∑ b, c b • _) = ∑ b, c b • _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Scheme.Modules.Hom.app_smul, paired_c3_free_generator_restrict,
    paired_c3_free_generator_arrow_apply]

/-- A free generator arrow that is an isomorphism gives a frame on every open. -/
theorem paired_c3_generator_frame_of_isIso {X : Scheme.{0}}
    (M : X.Modules) {σ : Type} [Fintype σ] (g : σ → Γ(M, ⊤))
    [IsIso (pairedC3FreeGeneratorArrow M g)] (V : X.Opens) :
    Function.Bijective (pairedC3FiniteFrameSynthesis g V le_top) := by
  have heq : (pairedC3FiniteFrameSynthesis g V le_top : (σ → Γ(X, V)) → Γ(M, V)) =
      Scheme.Modules.Hom.app (X := X) (pairedC3FreeGeneratorArrow M g) V ∘
        pairedC3FiniteFrameSynthesis (pairedC3FreeGenerator X σ ⊤) V le_top := by
    funext c
    exact (paired_c3_free_generator_arrow_synthesis M g V c).symm
  rw [heq]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app (X := X) (pairedC3FreeGeneratorArrow M g) V)).comp
    (paired_c3_free_generator_synthesis_bijective V)

/-- For an associated affine module, bijective synthesis on the full affine
scheme is enough for the same original sections to frame every subopen. -/
theorem paired_c3_affine_frame_spread (R : CommRingCat.{0})
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] {σ : Type} [Fintype σ]
    (g : σ → Γ(M, ⊤))
    (hg : Function.Bijective (pairedC3FiniteFrameSynthesis g ⊤ le_top))
    (V : (Spec R).Opens) :
    Function.Bijective (pairedC3FiniteFrameSynthesis g V le_top) := by
  let f := pairedC3FreeGeneratorArrow M g
  let F := moduleSpecΓFunctor (R := R)
  let N : (Spec R).Modules := SheafOfModules.free σ
  have hcomp : (F.map f : F.obj N → F.obj M) ∘
      pairedC3FiniteFrameSynthesis (pairedC3FreeGenerator (Spec R) σ ⊤) ⊤ le_top =
      pairedC3FiniteFrameSynthesis g ⊤ le_top := by
    funext c
    exact paired_c3_free_generator_arrow_synthesis M g ⊤ c
  have hΓ : Function.Bijective (F.map f) := by
    apply (Function.Bijective.of_comp_iff (F.map f)
      (paired_c3_free_generator_synthesis_bijective (X := Spec R) (σ := σ) ⊤)).mp
    rw [hcomp]
    exact hg
  letI : IsIso (F.map f) := (ConcreteCategory.isIso_iff_bijective _).mpr hΓ
  letI : IsIso ((tilde.functor R).map (F.map f)) := inferInstance
  have heq : f = (asIso N.fromTildeΓ).inv ≫
      (tilde.functor R).map (F.map f) ≫ M.fromTildeΓ := by
    have hn := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f
    change (tilde.functor R).map (F.map f) ≫ M.fromTildeΓ = N.fromTildeΓ ≫ f at hn
    have hv := congrArg (fun t => inv N.fromTildeΓ ≫ t) hn
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, asIso_inv] using hv.symm
  haveI : IsIso f := by
    rw [heq]
    infer_instance
  exact paired_c3_generator_frame_of_isIso M g V

/-- A specified affine comparison carrying the original generators to a basis
gives their frame on every original subopen. -/
theorem paired_c3_affine_frame_of_basis_images (R : CommRingCat.{0})
    (M N : (Spec R).Modules) [IsIso M.fromTildeΓ] {σ : Type} [Fintype σ]
    (e : M ≅ N) (b : Module.Basis σ R ((moduleSpecΓFunctor (R := R)).obj N))
    (g : σ → Γ(M, ⊤)) (hg : ∀ a, e.hom.app ⊤ (g a) = b a) (V : (Spec R).Opens) :
    Function.Bijective (pairedC3FiniteFrameSynthesis g V le_top) := by
  let C := (moduleSpecΓFunctor (R := R)).mapIso e
  let b' := b.map C.symm.toLinearEquiv
  have hb (a) : b' a = g a := by
    change C.symm.toLinearEquiv (b a) = _
    apply C.toLinearEquiv.injective
    change C.hom (C.inv (b a)) = C.hom _
    rw [Iso.inv_hom_id_apply]
    exact (hg a).symm
  exact paired_c3_affine_frame_spread R M g
    (paired_c3_affine_basis_section_synthesis R M b' g hb) V

#print axioms paired_c3_affine_frame_spread
end HodgeLean.Foundations.Program.G32Native
