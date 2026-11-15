import HodgeLean.Foundations.Program.G32Native.UnionConormalMaps
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineNaturalMono
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineNoncontainment
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineKernelInf
import HodgeLean.Foundations.Program.G32Native.UnionConormalFrameTransport
import HodgeLean.Foundations.Program.G32Native.UnionConormalIsoTransport
import HodgeLean.Foundations.Program.G32Native.UnionConormalBaseChangeMono
import HodgeLean.Foundations.AlgebraicGeometry.ConormalIsoComparison

/-! # Generic monicity on affine ambient schemes -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal HodgeLean.Foundations.Program

/-- On an affine ambient scheme, the union equation and equal global frames
make the natural first conormal arrow monic. -/
lemma unionConormal_affine_scheme_mono
    {V T T₁ T₂ : Scheme.{0}} [IsAffine V] [IsAffine T] [IsAffine T₁] [IsAffine T₂]
    [IsIntegral T₁]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t] [IsClosedImmersion t₁] [IsClosedImmersion t₂]
    (a : T₁ ⟶ T) (ha : a ≫ t = t₁)
    (hunion : t.ker = t₁.ker ⊓ t₂.ker)
    (hnot : ¬ Set.range t₁ ⊆ Set.range t₂) (n : ℕ)
    (eM : (Scheme.Modules.pullback a).obj (s2c_conormal t) ≅
      (SheafOfModules.free (R := T₁.ringCatSheaf) (Fin n) : T₁.Modules))
    (eN : s2c_conormal t₁ ≅
      (SheafOfModules.free (R := T₁.ringCatSheaf) (Fin n) : T₁.Modules)) :
    Mono (unionConormalFirst t t₁ a ha) := by
  let t' := Spec.map t.appTop
  let t₁' := Spec.map t₁.appTop
  let t₂' := Spec.map t₂.appTop
  let a' := Spec.map a.appTop
  let j := V.isoSpec.inv
  let b₀ := T.isoSpec.inv
  let b₁ := T₁.isoSpec.inv
  let b₂ := T₂.isoSpec.inv
  have h₀ : b₀ ≫ t = t' ≫ j := (Scheme.isoSpec_inv_naturality t).symm
  have h₁ : b₁ ≫ t₁ = t₁' ≫ j := (Scheme.isoSpec_inv_naturality t₁).symm
  have h₂ : b₂ ≫ t₂ = t₂' ≫ j := (Scheme.isoSpec_inv_naturality t₂).symm
  have hb : a' ≫ b₀ = b₁ ≫ a := Scheme.isoSpec_inv_naturality a
  have ha' : a' ≫ t' = t₁' := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop, ha]
  haveI : IsIso (idealPullbackMap t t' j b₀ h₀) :=
    idealPullbackMap_isIso_of_isIso t t' j b₀ h₀
  haveI : IsIso (idealPullbackMap t₁ t₁' j b₁ h₁) :=
    idealPullbackMap_isIso_of_isIso t₁ t₁' j b₁ h₁
  let eM' := unionConormalSourceFrameTransport t a t' a' j b₀ b₁ h₀ hb.symm n eM
  let eN' := unionConormalTargetFrameTransport t₁ t₁' j b₁ h₁ n eN
  have hnot' := unionConormal_noncontainment_of_iso_squares
    t₁ t₂ t₁' t₂' b₁ b₂ j h₁ h₂ hnot
  obtain ⟨u, hu⟩ := unionConormal_affine_nonzero_kernel_section
    Γ(V, ⊤) Γ(T₁, ⊤) Γ(T₂, ⊤) t₁.appTop t₂.appTop
    (t₁.app_surjective ⊤ (isAffineOpen_top V))
    (t₂.app_surjective ⊤ (isAffineOpen_top V)) hnot'
  have hid : Spec.map (CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(V, ⊤))) =
      𝟙 (Spec Γ(V, ⊤)) := by
    change Spec.map (𝟙 Γ(V, ⊤)) = _
    simp only [Spec.map_id]
  have hs : a' ≫ t' = t₁' ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(V, ⊤))) := by
    rw [hid, Category.comp_id]
    exact ha'
  have hm := unionConormal_affine_natural_mono
    Γ(V, ⊤) Γ(T, ⊤) Γ(T₁, ⊤) Γ(T₂, ⊤)
    t.appTop t₁.appTop t₂.appTop a.appTop hs
    (unionConormal_affine_kernel_inf t t₁ t₂ hunion) u hu n eM' eN'
  haveI : Mono (comparisonMap t' t₁' (𝟙 _) a'
      (ha'.trans (Category.comp_id t₁').symm)) :=
    unionConormal_comparison_mono_congr t' t₁' hid a' hs
      (ha'.trans (Category.comp_id t₁').symm) hm
  haveI := unionConormal_baseChange_mono t t₁ a ha t' t₁' a' ha' j b₀ b₁ h₀ h₁ hb
  change Mono (comparisonMap t t₁ (𝟙 V) a (ha.trans (Category.comp_id t₁).symm))
  exact unionConormal_mono_of_iso_pullback b₁
    (comparisonMap t t₁ (𝟙 V) a (ha.trans (Category.comp_id t₁).symm))

#print axioms unionConormal_affine_scheme_mono
end HodgeLean.Foundations.Program.G32Native
