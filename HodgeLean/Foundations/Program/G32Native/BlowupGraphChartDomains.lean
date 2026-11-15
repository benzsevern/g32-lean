import HodgeLean.Foundations.Program.G32Native.BlowupCoordinateMapPreimage
import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Composite.Descend

/-! Matching source and target opens for the blow-up coordinate graph. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme.IdealSheafData
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A generator chart is exactly the intersection of its base open and projective coordinate open. -/
theorem g32l4_blowUp_graph_chart_domain {X : Scheme.{0}} (I : X.IdealSheafData)
    (U : X.affineOpens) (m : ℕ) (g : Fin (m + 1) → I.ideal U)
    (hg : Ideal.span (Set.range (fun k => (g k : Γ(X, U)))) = I.ideal U)
    (f : I.blowUp ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ)))
    (hf : ∀ p, blowUp.chart I U (g p) ≫ f =
      g32l4_blowUp_chart_projectiveMap (I.ideal U) m g p) (k : Fin (m + 1)) :
    (blowUp.chart I U (g k)).opensRange =
      I.blowUpπ ⁻¹ᵁ U.1 ⊓ f ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ)) (MvPolynomial.X k) := by
  have hpre := g32l4_blowUp_coordinateMap_preimage (I.ideal U) m g hg (blowUp.ι I U) f
    (fun p => by simpa only [blowUp.chart_eq, Category.assoc] using hf p) k
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx
    refine ⟨chart_comp_le I U (g k) (by trivial), ?_⟩
    have hz : affineBlowUp.chart (I.ideal U) (g k) z ∈
        (affineBlowUp.chart (I.ideal U) (g k)).opensRange :=
      Scheme.Hom.mem_opensRange.mpr ⟨z, rfl⟩
    rw [← hpre] at hz
    exact hz
  · rintro ⟨hx, hfx⟩
    have hx' : x ∈ (blowUp.ι I U).opensRange := by rw [blowUp.opensRange_ι]; exact hx
    obtain ⟨y, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx'
    have hy : y ∈ (blowUp.ι I U ≫ f) ⁻¹ᵁ _ := hfx
    rw [hpre] at hy
    obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hy
    exact Scheme.Hom.mem_opensRange.mpr ⟨z, rfl⟩

end HodgeLean.Foundations.Program
