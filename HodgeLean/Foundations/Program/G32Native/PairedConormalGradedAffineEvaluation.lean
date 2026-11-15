import HodgeLean.Foundations.Program.G32Native.PairedConormalGradedChartEvaluation

/-! # Exact affine evaluation for arbitrary homogeneous fraction charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program.G32Native
universe u

/-- The actual fraction section evaluates through any specified affine chart ring map. -/
theorem conormal_graded_affine_fraction_evaluation
    {S : Type*} {A : Type u} [CommRing A] [SetLike S A] [AddSubgroupClass S A]
    (𝒜 : ℕ → S) [GradedRing 𝒜] {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d)
    {R : Type u} [CommRing R] (f : Away 𝒜 s →+* R)
    (h : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      (Spec.map (CommRingCat.ofHom f) ≫ Proj.awayι 𝒜 s hs hd) ⁻¹ᵁ Proj.basicOpen 𝒜 s) :
    Proj.awayToSection 𝒜 s ≫
      (Spec.map (CommRingCat.ofHom f) ≫ Proj.awayι 𝒜 s hs hd).appLE
        (Proj.basicOpen 𝒜 s) ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      CommRingCat.ofHom f := by
  let t := Proj.awayι 𝒜 s hs hd
  let U := Proj.basicOpen 𝒜 s
  have ht : (⊤ : (Spec (CommRingCat.of
      (HomogeneousLocalization.Away 𝒜 s))).Opens) ≤ t ⁻¹ᵁ U := by
    intro x _
    change t x ∈ Proj.basicOpen 𝒜 s
    rw [← Proj.opensRange_awayι 𝒜 s hs hd]
    exact ⟨x, rfl⟩
  have hc := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom f)) t
    U ⊤ ⊤ ht (by simp)
  have hz : (Spec.map (CommRingCat.ofHom f)).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom f)).appTop := by simp [Scheme.Hom.appLE]
  rw [hz] at hc
  calc
    _ = (Proj.awayToSection 𝒜 s ≫ t.appLE U ⊤ ht) ≫
        ((Spec.map (CommRingCat.ofHom f)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) := by
      rw [← hc]
      simp only [Category.assoc]
    _ = _ := by
      rw [conormal_graded_awayToSection_chart_evaluation, Scheme.ΓSpecIso_naturality,
        Iso.inv_hom_id_assoc]


end HodgeLean.Foundations.Program.G32Native
