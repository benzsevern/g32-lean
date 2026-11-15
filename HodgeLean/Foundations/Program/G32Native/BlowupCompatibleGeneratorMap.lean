import HodgeLean.Foundations.Program.G32Native.BlowupGeneratorCover
import HodgeLean.Foundations.Program.G32Native.BlowupChartProjectiveMap
import HodgeLean.Foundations.Program.G32Native.BlowupChartCoordinateProduct
import HodgeLean.Foundations.Program.G32Native.PullbackSectionTransition
import HodgeLean.Foundations.Program.G32Native.NormalizedProjectiveGluing

/-! Global projective coordinates from compatible generators of a centre ideal. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Compatible indexed ideal generators define global projective coordinates on the blow-up. -/
theorem g32l4_blowUp_compatible_generator_map {X : Scheme.{0}} {J : Type}
    (I : X.IdealSheafData) (U : J → X.affineOpens) (hU : ⨆ j, (U j).1 = ⊤)
    (m : ℕ) (g : ∀ j, Fin (m + 1) → I.ideal (U j))
    (hg : ∀ j, Ideal.span (Set.range (fun k => (g j k : Γ(X, U j)))) = I.ideal (U j))
    (htrans : ∀ i j, ∃ c : Γ(X, (U i).1 ⊓ (U j).1), ∀ k,
      X.presheaf.map (homOfLE inf_le_left).op (g i k).val =
        c * X.presheaf.map (homOfLE inf_le_right).op (g j k).val) :
    ∃ f : I.blowUp ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ)),
      ∀ i k, blowUp.chart I (U i) (g i k) ≫ f =
        g32l4_blowUp_chart_projectiveMap (I.ideal (U i)) m (g i) k := by
  let 𝒰 := g32l4_blowUp_generatorCover I U hU g hg
  letI : ∀ p, IsAffine (𝒰.X p) := fun p => inferInstanceAs
    (IsAffine (Spec (.of (affineBlowUpAlgebra (I.ideal (U p.1)) (g p.1 p.2)))))
  let q : ∀ p, ULift.{0} ℤ →+* Γ(𝒰.X p, ⊤) := fun _ =>
    (Int.castRingHom _).comp ULift.ringEquiv.toRingHom
  let a : ∀ p, Fin (m + 1) → Γ(𝒰.X p, ⊤) :=
    fun p k => g32l4_blowUp_coordinate (I.ideal (U p.1)) (g p.1 p.2) (g p.1 k)
  let s : ∀ p, Γ(𝒰.X p, ⊤) :=
    fun p => affineBlowUp.chartGenerator (I.ideal (U p.1)) (g p.1 p.2)
  have hk (p : 𝒰.I₀) : a p p.2 = 1 := g32l4_blowUp_coordinate_self _ _
  have hs (p : 𝒰.I₀) : s p ∈ nonZeroDivisors Γ(𝒰.X p, ⊤) :=
    affineBlowUp.chartGenerator_mem_nonZeroDivisors _ _
  obtain ⟨f, hf⟩ := g32l4_glue_normalized_generator_maps 𝒰 q a (fun p => p.2) hk s hs
    (by
      intro p r
      obtain ⟨c, hc⟩ := htrans p.1 r.1
      obtain ⟨c', hc'⟩ := g32l4_pullback_section_transition I.blowUpπ (𝒰.f p) (𝒰.f r)
        (U p.1).1 (U r.1).1 (chart_comp_le I (U p.1) (g p.1 p.2))
        (chart_comp_le I (U r.1) (g r.1 r.2))
        (fun k => (g p.1 k).val) (fun k => (g r.1 k).val) c hc
      refine ⟨c' * (pullback.snd (𝒰.f p) (𝒰.f r)).appTop.hom (s r), fun k => ?_⟩
      change (pullback.fst (𝒰.f p) (𝒰.f r)).appTop.hom
          (s p) * (pullback.fst (𝒰.f p) (𝒰.f r)).appTop.hom (a p k) = _
      rw [← map_mul, g32l4_blowUp_chart_coordinate_product]
      calc
        _ = c' * (pullback.snd (𝒰.f p) (𝒰.f r)).appTop.hom
            ((blowUp.chart I (U r.1) (g r.1 r.2) ≫ I.blowUpπ).appLE (U r.1).1 ⊤
              (chart_comp_le I (U r.1) (g r.1 r.2)) (g r.1 k).val) := hc' k
        _ = _ := by rw [← g32l4_blowUp_chart_coordinate_product, map_mul, mul_assoc])
  exact ⟨f, fun i k => hf (i, k)⟩

end HodgeLean.Foundations.Program
