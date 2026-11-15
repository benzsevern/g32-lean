import HodgeLean.Foundations.Program.SchoenSelectedGeometryPeriodDescent
import HodgeLean.Foundations.Program.HurwitzPrymCovDescent

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Rational degree-one pullback along a finite Galois curve map has exactly the invariant image. -/
theorem s0_galois_pullback_range
    {C Y G : Type} [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f) (a : Cohomology ℚ (TopCat.of C) 1) :
    a ∈ LinearMap.range (cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩)) ↔
      ∀ g : G, cohomologyMap ℚ 1 (TopCat.ofHom ⟨fun x : C ↦ g • x, (hG g).continuous⟩) a = a := by
  constructor
  · rintro ⟨b, rfl⟩ g
    have hm : TopCat.ofHom ⟨fun x : C ↦ g • x, (hG g).continuous⟩ ≫
        TopCat.ofHom ⟨f, hf.continuous⟩ = TopCat.ofHom ⟨f, hf.continuous⟩ := by
      ext x : 1
      exact hgal.1 g x
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hm]
  · intro ha
    let θ := b3Rest2_T (Module.finrank_self ℂ) a
    have hθ : (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ∈ b4_invariantForms ℂ C G := by
      refine ⟨θ.property, ?_⟩
      change (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) ∈
        ⨅ g : G, LinearMap.ker (b4_formAct ℂ g - LinearMap.id)
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      have ht := s0_period_form_pullback (fun x : C ↦ g⁻¹ • x) (hG g⁻¹) a
      rw [ha g⁻¹] at ht
      exact (congrArg Subtype.val ht).symm
    let η : b3_HolForm ℂ Y := ⟨b4cov_descend (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ) f θ,
      b4cov_descend_mem_holForm (E := ℂ) (E' := ℂ) (G := G) (Module.finrank_self ℂ) (Module.finrank_self ℂ)
        hG f hf hgal θ hθ⟩
    apply s0_class_descends_of_period_form f hf a η
    apply Subtype.ext
    exact (b4cov_pullback_descend (E := ℂ) (E' := ℂ) (G := G) (Module.finrank_self ℂ) (Module.finrank_self ℂ)
      hG f hf hgal θ hθ).symm

#print axioms s0_galois_pullback_range
end HodgeLean.Foundations.Program
