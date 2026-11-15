import HodgeLean.Foundations.Program.G32Native.PairedC3RatioRefinedComparison

/-! # Agreement of supplied ratio charts on their actual overlaps -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
namespace PairedC3AffineRatioData
variable {X Q : Scheme} {Y : Over (Spec ↧ℂ)} {p : Y.left ⟶ X} {i : Q ⟶ X}
  {D₀ D₁ : X.IdealSheafData}

/-- The specified normalized maps of any two supplied affine ratio charts
agree on their actual residual quotient overlap.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem overlap_comparison [IsIntegral X] [IsIntegral Q] [IsIntegral Y.left]
    [IsClosedImmersion i] [IsDominant p] [QuasiCompact p]
    (hproper₀ : (D₀.comap i).support ≠ ⊤) (hproper₁ : (D₁.comap i).support ≠ ⊤)
    (A B : PairedC3AffineRatioData Y p i D₀ D₁) :
    let M := (((D₀ ⊔ D₁) ⊔ i.ker).comap p)
    pullback.fst (M.subschemeCover.f A.V) (M.subschemeCover.f B.V) ≫ A.map.left =
      pullback.snd _ _ ≫ B.map.left := by
  let D := (D₀ ⊔ D₁) ⊔ i.ker
  let M := D.comap p
  apply pairedC3_quotient_overlap_ext_of_local M A.V B.V A.map.left B.map.left
  intro x hxA hxB
  let y := M.subschemeι x
  have hyD : p y ∈ (D.support : Set X) := by
    have hy : y ∈ (M.support : Set Y.left) := by
      rw [← M.range_subschemeι]
      exact ⟨x, rfl⟩
    simpa only [M, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage] using hy
  have hySlice : p y ∈ (i.ker.support : Set X) := by
    have hy : p y ∈ ((D₀ ⊔ D₁).support : Set X) ∧ p y ∈ (i.ker.support : Set X) := by
      simpa only [D, Scheme.IdealSheafData.support_sup,
        TopologicalSpace.Closeds.coe_inf, Set.mem_inter_iff] using hyD
    exact hy.2
  have hyRange : p y ∈ Set.range i := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq] at hySlice
    exact hySlice
  obtain ⟨z, hz⟩ := hyRange
  obtain ⟨U, W, hyU, hyW, hUA, hUB, hWA, hWB, hW⟩ :=
    pairedC3_affine_overlap_refinement p y A.U B.U A.V B.V
      (A.liesOver hxA) (B.liesOver hxB) hxA hxB
  letI : Nonempty (i ⁻¹ᵁ U.1) := ⟨⟨z, by
    change i z ∈ U.1
    rw [hz]
    exact hyU⟩⟩
  letI : Nonempty W.1 := ⟨⟨y, hyW⟩⟩
  exact ⟨W, hWA, hWB, hyW,
    A.refined_comparison hproper₀ hproper₁ B U W hUA hUB hWA hWB hW⟩

end PairedC3AffineRatioData
#print axioms PairedC3AffineRatioData.overlap_comparison
end HodgeLean.Foundations.Program.G32Native
