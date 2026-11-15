import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Exact fraction evaluation on arbitrary positively graded affine charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program.G32Native
universe u

/-- Actual positively homogeneous affine-chart pullback recovers the same homogeneous fraction. -/
theorem conormal_graded_awayToSection_chart_evaluation
    {S : Type*} {A : Type u} [CommRing A] [SetLike S A] [AddSubgroupClass S A]
    (𝒜 : ℕ → S) [GradedRing 𝒜] {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (h : (⊤ : (Spec (CommRingCat.of (Away 𝒜 f))).Opens) ≤
      Proj.awayι 𝒜 f hf hd ⁻¹ᵁ Proj.basicOpen 𝒜 f) :
    Proj.awayToSection 𝒜 f ≫ (Proj.awayι 𝒜 f hf hd).appLE
      (Proj.basicOpen 𝒜 f) ⊤ h = (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).inv := by
  let U := Proj.basicOpen 𝒜 f
  let e := Proj.basicOpenIsoSpec 𝒜 f hf hd
  have he : Proj.awayToSection 𝒜 f ≫ U.topIso.inv ≫
      e.inv.appTop = (Scheme.ΓSpecIso _).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso _).hom).mp
    rw [Iso.hom_inv_id]
    calc
      (Scheme.ΓSpecIso _).hom ≫
          (Proj.awayToSection 𝒜 f ≫ U.topIso.inv ≫ e.inv.appTop) =
          e.hom.appTop ≫ e.inv.appTop := by
        rw [Proj.basicOpenIsoSpec_hom]
        change _ = (Proj.basicOpenToSpec 𝒜 f).app ⊤ ≫ e.inv.appTop
        rw [Proj.basicOpenToSpec_app_top]
        simp only [Category.assoc]
        rfl
      _ = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
  have hc := Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤ (by simp) (by simp)
  have hc' : U.topIso.inv ≫ e.inv.appTop =
      (Proj.awayι 𝒜 f hf hd).appLE
        U ⊤ h := by
    convert hc using 1
    · have ht : e.inv.appLE ⊤ ⊤ (by simp) = e.inv.appTop := by
        simp [Scheme.Hom.appLE]
      rw [ht]
      congr 1
    · rfl
  rw [← hc']
  exact he


end HodgeLean.Foundations.Program.G32Native
