import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Glue.BlowUp

/-! Chart covers indexed by specified ideal generators. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
namespace HodgeLean.Foundations.Program

/-- The charts of an indexed generating family cover the affine blow-up. -/
theorem g32l4_affine_blowUp_generator_chart_covers {R K : Type} [CommRing R]
    (I : Ideal R) (g : K → I)
    (hg : Ideal.span (Set.range (fun k => (g k : R))) = I) (x : affineBlowUp I) :
    ∃ k, x ∈ (affineBlowUp.chart I (g k)).opensRange := by
  obtain ⟨⟨a, ha⟩, hx⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq I _ hg x
  have ha' := ha
  obtain ⟨k, hk⟩ := ha
  refine ⟨k, ?_⟩
  have he : (⟨a, hg ▸ Ideal.subset_span ha'⟩ : I) = g k := Subtype.ext hk.symm
  rwa [he] at hx

/-- Affine base opens and indexed generators give an open cover of the global blow-up. -/
def g32l4_blowUp_generatorCover {X : Scheme.{0}} {J K : Type}
    (I : X.IdealSheafData) (U : J → X.affineOpens) (hU : ⨆ j, (U j).1 = ⊤)
    (g : ∀ j, K → I.ideal (U j))
    (hg : ∀ j, Ideal.span (Set.range (fun k => (g j k : Γ(X, U j)))) = I.ideal (U j)) :
    I.blowUp.OpenCover := by
  have hcov (x : I.blowUp) : ∃ p : J × K,
      x ∈ (blowUp.chart I (U p.1) (g p.1 p.2)).opensRange := by
    have hx : I.blowUpπ x ∈ ⨆ j, (U j).1 := by rw [hU]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    have hx' : x ∈ (blowUp.ι I (U j)).opensRange := by
      rw [blowUp.opensRange_ι]
      exact hj
    obtain ⟨y, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx'
    obtain ⟨k, hk⟩ := g32l4_affine_blowUp_generator_chart_covers _ (g j) (hg j) y
    obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hk
    refine ⟨(j, k), ?_⟩
    exact Scheme.Hom.mem_opensRange.mpr ⟨z, rfl⟩
  let C : I.blowUp.AffineOpenCover := {
    I₀ := J × K
    X p := .of (affineBlowUpAlgebra (I.ideal (U p.1)) (g p.1 p.2))
    f p := blowUp.chart I (U p.1) (g p.1 p.2)
    idx x := (hcov x).choose
    covers x := (hcov x).choose_spec }
  exact C.openCover

end HodgeLean.Foundations.Program
