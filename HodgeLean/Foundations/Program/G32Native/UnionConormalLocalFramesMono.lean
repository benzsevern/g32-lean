import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineSchemeMono
import HodgeLean.Foundations.Program.G32Native.UnionConormalFrameChart
import HodgeLean.Foundations.Program.G32Native.UnionConormalDenseComplement
import HodgeLean.Foundations.Program.G32Native.UnionConormalLocalExact
import HodgeLean.Foundations.AlgebraicGeometry.ConormalOpenComparison

/-! # Generic monicity from local conormal frames -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal HodgeLean.Foundations.Program

/-- For a closed union, equally ranked local frames and component
noncontainment make the natural first conormal arrow monic. -/
lemma unionConormal_mono_of_local_frames
    {V T T₁ T₂ : Scheme.{0}} [IsIntegral T₁]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t] [IsClosedImmersion t₁] [IsClosedImmersion t₂]
    (a : T₁ ⟶ T) (ha : a ≫ t = t₁)
    (hunion : t.ker = t₁.ker ⊓ t₂.ker)
    (hnot : ¬ Set.range t₁ ⊆ Set.range t₂) (n : ℕ)
    (hfree : ∀ x : T₁, ∃ U : T₁.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict
        ((Scheme.Modules.pullback a).obj (s2c_conormal t)) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) : U.toScheme.Modules)) ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal t₁) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) : U.toScheme.Modules))) :
    Mono (unionConormalFirst t t₁ a ha) := by
  apply unionConormal_mono_of_open_neighborhoods
  intro x
  obtain ⟨U, hx, ⟨eM⟩, ⟨eN⟩⟩ := hfree x
  obtain ⟨W, hW, hxW, hWU⟩ := unionConormal_exists_affine_frame_chart t₁ U x hx
  let U₀ := t ⁻¹ᵁ W
  let U₁ := t₁ ⁻¹ᵁ W
  let U₂ := t₂ ⁻¹ᵁ W
  have hle : U₁ ≤ a ⁻¹ᵁ U₀ := by
    intro y hy
    change t (a y) ∈ W
    change t₁ y ∈ W at hy
    simpa only [← Scheme.Hom.comp_apply, ha] using hy
  let a' := a.resLE U₀ U₁ hle
  have hb : a' ≫ U₀.ι = U₁.ι ≫ a := a.resLE_comp_ι hle
  have ha' : a' ≫ (t ∣_ W) = t₁ ∣_ W := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hb,
      Category.assoc, ha, morphismRestrict_ι]
  have h₀ : U₀.ι ≫ t = (t ∣_ W) ≫ W.ι := (morphismRestrict_ι t W).symm
  have h₁ : U₁.ι ≫ t₁ = (t₁ ∣_ W) ≫ W.ι := (morphismRestrict_ι t₁ W).symm
  haveI : IsIso (idealPullbackMap t (t ∣_ W) W.ι U₀.ι h₀) :=
    idealPullbackMap_open_isIso t W
  haveI : IsIso (idealPullbackMap t₁ (t₁ ∣_ W) W.ι U₁.ι h₁) :=
    idealPullbackMap_open_isIso t₁ W
  let em := unionConormalFrameOnSmallerOpen _ U U₁ hWU n eM
  let en := unionConormalFrameOnSmallerOpen _ U U₁ hWU n eN
  let em' := unionConormalSourcePulledFrameTransport t a (t ∣_ W) a' W.ι U₀.ι U₁.ι
    h₀ hb.symm n em
  let en' := unionConormalTargetPulledFrameTransport t₁ (t₁ ∣_ W) W.ι U₁.ι h₁ n en
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffine U₀.toScheme := hW.preimage t
  haveI : IsAffine U₁.toScheme := hW.preimage t₁
  haveI : IsAffine U₂.toScheme := hW.preimage t₂
  haveI : Nonempty U₁ := ⟨⟨x, hxW⟩⟩
  haveI : IsIntegral U₁.toScheme := isIntegral_of_isOpenImmersion U₁.ι
  haveI : Mono (comparisonMap (t ∣_ W) (t₁ ∣_ W) (𝟙 _) a'
      (ha'.trans (Category.comp_id (t₁ ∣_ W)).symm)) :=
    unionConormal_affine_scheme_mono (t ∣_ W) (t₁ ∣_ W) (t₂ ∣_ W) a' ha'
      (unionConormal_restrict_kernel_inf t t₁ t₂ hunion W)
      (union_component_noncontainment_restrict t₁ t₂ hnot W) n em' en'
  haveI := unionConormal_baseChange_mono t t₁ a ha (t ∣_ W) (t₁ ∣_ W) a' ha'
    W.ι U₀.ι U₁.ι h₀ h₁ hb
  haveI : Mono ((Scheme.Modules.pullback U₁.ι).map (unionConormalFirst t t₁ a ha)) := by
    change Mono ((Scheme.Modules.pullback U₁.ι).map
      (comparisonMap t t₁ (𝟙 V) a (ha.trans (Category.comp_id t₁).symm)))
    infer_instance
  refine ⟨U₁, hxW, ?_⟩
  exact unionConormal_mono_map_of_natIso
    (Scheme.Modules.restrictFunctorIsoPullback U₁.ι).symm
    (unionConormalFirst t t₁ a ha)

#print axioms unionConormal_mono_of_local_frames
end HodgeLean.Foundations.Program.G32Native
