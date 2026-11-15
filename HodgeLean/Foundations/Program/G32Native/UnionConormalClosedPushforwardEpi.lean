import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Direct image along an immersion retains epimorphisms -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- Direct image along an immersion retains epimorphy of module maps. -/
lemma unionConormal_closedPushforward_epi
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    {M N : X.Modules} (φ : M ⟶ N) [Epi φ] :
    Epi ((Scheme.Modules.pushforward f).map φ) := by
  apply (Scheme.Modules.Hom.epi_iff_locallySurjective _).mpr
  intro U s x hx
  by_cases him : x ∈ Set.range f
  · obtain ⟨y, rfl⟩ := him
    obtain ⟨W, hW, hyW, m, hm⟩ :=
      (Scheme.Modules.Hom.epi_iff_locallySurjective φ).mp inferInstance (f ⁻¹ᵁ U) s y hx
    let Z : Y.Opens := ⟨(f '' (W : Set X)ᶜ)ᶜ,
      (f.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
    let V := U ⊓ Z
    have hVU : V ≤ U := inf_le_left
    have hyV : f y ∈ V := by
      refine ⟨hx, ?_⟩
      rintro ⟨z, hz, he⟩
      exact hz (f.isClosedEmbedding.injective he ▸ hyW)
    have hpre : f ⁻¹ᵁ V ≤ W := by
      intro z hz
      by_contra hn
      exact hz.2 ⟨z, hn, rfl⟩
    refine ⟨V, hVU, hyV, M.presheaf.map (homOfLE hpre).op m, ?_⟩
    change φ.app (f ⁻¹ᵁ V) (M.presheaf.map (homOfLE hpre).op m) =
      N.presheaf.map (homOfLE (f.preimage_mono hVU)).op s
    have hn := CategoryTheory.congr_fun
      (((Scheme.Modules.toPresheaf X).map φ).naturality (homOfLE hpre).op) m
    change φ.app (f ⁻¹ᵁ V) (M.presheaf.map (homOfLE hpre).op m) =
      N.presheaf.map (homOfLE hpre).op (φ.app W m) at hn
    rw [hn, hm]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · let Z : Y.Opens := ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    let V := U ⊓ Z
    have hpre : f ⁻¹ᵁ V = ⊥ := by
      ext z
      exact ⟨fun hz => hz.2 ⟨z, rfl⟩, False.elim⟩
    haveI : Subsingleton Γ(X, f ⁻¹ᵁ V) := by rw [hpre]; infer_instance
    haveI : Subsingleton Γ(N, f ⁻¹ᵁ V) := Module.subsingleton Γ(X, f ⁻¹ᵁ V) _
    refine ⟨V, inf_le_left, ⟨hx, him⟩, 0, ?_⟩
    change φ.app (f ⁻¹ᵁ V) 0 = _
    exact Subsingleton.elim _ _

end HodgeLean.Foundations.Program.G32Native
