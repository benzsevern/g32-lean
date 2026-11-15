import HodgeLean.Foundations.Program.G32Native.BlowupGraphChartDomains
import HodgeLean.Foundations.Program.G32Native.BlowupChartGraphImmersion
import HodgeLean.Foundations.Program.G32Native.BlowupGeneratorCover
import HodgeLean.Foundations.Program.G32Native.ProjectiveSpaceBaseMap
import HodgeLean.Foundations.Program.SchoenTowerN2bProjectiveGluing

/-! The graph of compatible blow-up coordinates is a projective-space embedding over the base. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Compatible blow-up coordinates give an embedding into projective space over the original base. -/
theorem g32l4_blowUp_graph_closedImmersion {X : Scheme.{0}} [IsLocallyNoetherian X] {J : Type}
    (I : X.IdealSheafData) (U : J → X.affineOpens) (hU : ⨆ j, (U j).1 = ⊤)
    (m : ℕ) (g : ∀ j, Fin (m + 1) → I.ideal (U j))
    (hg : ∀ j, Ideal.span (Set.range (fun k => (g j k : Γ(X, U j)))) = I.ideal (U j))
    (f : I.blowUp ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ)))
    (hf : ∀ i k, blowUp.chart I (U i) (g i k) ≫ f =
      g32l4_blowUp_chart_projectiveMap (I.ideal (U i)) m (g i) k) :
    IsClosedImmersion (pullback.lift I.blowUpπ f (Subsingleton.elim _ _) :
      I.blowUp ⟶ ProjectiveSpace (Fin (m + 1)) X) := by
  let K := Fin (m + 1)
  let 𝒰 := g32l4_blowUp_generatorCover I U hU g hg
  let j : I.blowUp ⟶ ProjectiveSpace K X := pullback.lift I.blowUpπ f (Subsingleton.elim _ _)
  let V (p : 𝒰.I₀) : (ProjectiveSpace K X).Opens :=
    ProjectiveSpace.toBase K X ⁻¹ᵁ (U p.1).1 ⊓
      pullback.snd (terminal.from X) (terminal.from (Proj (homogeneousSubmodule K (ULift.{0} ℤ))))
        ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule K (ULift.{0} ℤ)) (MvPolynomial.X p.2)
  have hpre (p : 𝒰.I₀) : (𝒰.f p).opensRange = j ⁻¹ᵁ V p := by
    change (blowUp.chart I (U p.1) (g p.1 p.2)).opensRange = _
    simp only [V, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      j, pullback.lift_fst, ProjectiveSpace.toBase, pullback.lift_snd]
    exact g32l4_blowUp_graph_chart_domain I (U p.1) m (g p.1) (hg p.1) f (hf p.1) p.2
  haveI hlocal (p : 𝒰.I₀) : IsImmersion (𝒰.f p ≫ j) := by
    let σ := Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U p.1) (affineBlowUpAlgebra (I.ideal (U p.1)) (g p.1 p.2))))
    let j₀ : 𝒰.X p ⟶ ProjectiveSpace K (Spec Γ(X, U p.1)) := pullback.lift σ
      (g32l4_blowUp_chart_projectiveMap (I.ideal (U p.1)) m (g p.1) p.2)
      (Subsingleton.elim _ _)
    haveI : IsImmersion j₀ := g32l4_blowUp_chart_graph_immersion _ m _ (hg p.1) p.2
    let b := g32l4_projectiveSpace_baseMap K (U p.1).2.fromSpec
    have he : 𝒰.f p ≫ j = j₀ ≫ b := by
      apply pullback.hom_ext
      · simp only [j, j₀, b, g32l4_projectiveSpace_baseMap, Category.assoc,
          pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
        exact chart_comp_π_eq I (U p.1) (g p.1 p.2)
      · simp only [j, j₀, b, g32l4_projectiveSpace_baseMap, Category.assoc,
          pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
        exact hf p.1 p.2
    rw [he]
    infer_instance
  haveI : IsImmersion j := n2b_immersion_of_matching_charts j 𝒰 V hpre
  haveI : IsProper I.blowUpπ := blowUp.isProper_π I
  haveI : IsProper (j ≫ ProjectiveSpace.toBase K X) := by
    simpa only [j, ProjectiveSpace.toBase, pullback.lift_fst] using
      (inferInstance : IsProper I.blowUpπ)
  haveI : IsProper j := IsProper.of_comp j (ProjectiveSpace.toBase K X)
  exact IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range

end HodgeLean.Foundations.Program
