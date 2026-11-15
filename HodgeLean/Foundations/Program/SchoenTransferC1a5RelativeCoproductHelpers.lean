import HodgeLean.Foundations.Program.SchoenTransferC1a5CellCoproductHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeHelpers

/-! Cokernel identifications for relative cell coproducts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
namespace HodgeLean.Foundations.Program

/-- Cokernels commute with coproducts of integral chain maps.
Source: Hatcher §2.1, relative chains of disjoint unions; Mathlib cokernel.desc. -/
def c1a5_cokernel_coproduct_iso {I : Type}
    {A B : I → ChainComplex (ModuleCat ℤ) ℕ} (f : ∀ i, A i ⟶ B i) :
    (∐ fun i ↦ cokernel (f i)) ≅ cokernel (CategoryTheory.Limits.Sigma.map f) := by
  let π : ∀ i, B i ⟶ cokernel (f i) := fun i ↦ cokernel.π (f i)
  let h : (∐ fun i ↦ cokernel (f i)) ⟶ cokernel (CategoryTheory.Limits.Sigma.map f) :=
    CategoryTheory.Limits.Sigma.desc (fun i ↦ cokernel.desc (f i)
      (CategoryTheory.Limits.Sigma.ι B i ≫ cokernel.π (CategoryTheory.Limits.Sigma.map f)) (by
        rw [← Category.assoc, ← CategoryTheory.Limits.Sigma.ι_map, Category.assoc,
          cokernel.condition, comp_zero]))
  let v : cokernel (CategoryTheory.Limits.Sigma.map f) ⟶ (∐ fun i ↦ cokernel (f i)) :=
    cokernel.desc _ (CategoryTheory.Limits.Sigma.map π) (by
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro i
      simp only [CategoryTheory.Limits.Sigma.ι_map_assoc, Category.assoc,
        CategoryTheory.Limits.Sigma.ι_map, π, comp_zero]
      rw [← Category.assoc, cokernel.condition, zero_comp])
  refine ⟨h, v, ?_, ?_⟩
  · apply CategoryTheory.Limits.Sigma.hom_ext
    intro i
    apply (cancel_epi (cokernel.π (f i))).1
    simp only [h, v, π, CategoryTheory.Limits.Sigma.ι_comp_desc_assoc, Category.assoc,
      cokernel.π_desc_assoc, cokernel.π_desc, CategoryTheory.Limits.Sigma.ι_map,
      comp_id]
  · apply (cancel_epi (cokernel.π (CategoryTheory.Limits.Sigma.map f))).1
    apply CategoryTheory.Limits.Sigma.hom_ext
    intro i
    simp only [h, v, π, Category.assoc, cokernel.π_desc_assoc,
      CategoryTheory.Limits.Sigma.ι_map_assoc, CategoryTheory.Limits.Sigma.ι_comp_desc,
      cokernel.π_desc, comp_id]

/-- Projection formula for the coproduct cokernel identification.
Source: Mathlib cokernel.π_desc and Sigma.ι_comp_desc. -/
@[reassoc]
lemma c1a5_cokernel_coproduct_iso_projection {I : Type}
    {A B : I → ChainComplex (ModuleCat ℤ) ℕ} (f : ∀ i, A i ⟶ B i) (i : I) :
    cokernel.π (f i) ≫ CategoryTheory.Limits.Sigma.ι (fun i ↦ cokernel (f i)) i ≫
      (c1a5_cokernel_coproduct_iso f).hom =
        CategoryTheory.Limits.Sigma.ι B i ≫ cokernel.π (CategoryTheory.Limits.Sigma.map f) := by
  simp only [c1a5_cokernel_coproduct_iso, CategoryTheory.Limits.Sigma.ι_comp_desc,
    cokernel.π_desc]

/-- Relative chains of a coproduct identify with the coproduct of the relative chains
for a specified coproduct-preserving chain functor.
Source: Hatcher §2.1, relative chains of disjoint unions; Mathlib sigmaComparison. -/
def c1a5_relative_coproduct_iso {I : Type}
    (F : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ)
    [PreservesColimitsOfShape (Discrete I) F]
    {A B : I → SSet.{0}} (f : ∀ i, A i ⟶ B i) :
    (∐ fun i ↦ cokernel (F.map (f i))) ≅
      cokernel (F.map (CategoryTheory.Limits.Sigma.map f)) := by
  have w : CategoryTheory.Limits.Sigma.map (fun i ↦ F.map (f i)) ≫ sigmaComparison F B =
      sigmaComparison F A ≫ F.map (CategoryTheory.Limits.Sigma.map f) := by
    apply CategoryTheory.Limits.Sigma.hom_ext
    intro i
    simp only [CategoryTheory.Limits.Sigma.ι_map_assoc, Category.assoc,
      ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc,
      ← F.map_comp, CategoryTheory.Limits.Sigma.ι_map]
  exact c1a5_cokernel_coproduct_iso (fun i ↦ F.map (f i)) ≪≫
    asIso (cokernel.map _ _ (sigmaComparison F A) (sigmaComparison F B) w)

/-- The relative coproduct identification preserves the actual quotient projections.
Source: Mathlib cokernel.π_desc and sigmaComparison. -/
@[reassoc]
lemma c1a5_relative_coproduct_iso_projection {I : Type}
    (F : SSet.{0} ⥤ ChainComplex (ModuleCat ℤ) ℕ)
    [PreservesColimitsOfShape (Discrete I) F]
    {A B : I → SSet.{0}} (f : ∀ i, A i ⟶ B i) (i : I) :
    cokernel.π (F.map (f i)) ≫ CategoryTheory.Limits.Sigma.ι (fun i ↦ cokernel (F.map (f i))) i ≫
      (c1a5_relative_coproduct_iso F f).hom =
        F.map (CategoryTheory.Limits.Sigma.ι B i) ≫
          cokernel.π (F.map (CategoryTheory.Limits.Sigma.map f)) := by
  simp only [c1a5_relative_coproduct_iso, c1a5_cokernel_coproduct_iso,
    Iso.trans_hom, asIso_hom, Category.assoc, CategoryTheory.Limits.Sigma.ι_comp_desc_assoc,
    CategoryTheory.Limits.Sigma.ι_comp_desc, cokernel.map, cokernel.π_desc_assoc,
    cokernel.π_desc, ι_comp_sigmaComparison_assoc]

/-- The relative unit respects the actual coproduct identifications on both chain models.
Source: Hatcher §2.1, naturality for disjoint unions and maps of pairs. -/
lemma c1a5_relative_unit_coproduct_naturality {I : Type}
    {A B : I → SSet.{0}} (f : ∀ i, A i ⟶ B i) :
    CategoryTheory.Limits.Sigma.map (fun i ↦ c1a5RelativeUnit (f i)) ≫
        (c1a5_relative_coproduct_iso c1a5SingularChains f).hom =
      (c1a5_relative_coproduct_iso c1a5Chains f).hom ≫
        c1a5RelativeUnit (CategoryTheory.Limits.Sigma.map f) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro i
  apply (cancel_epi (cokernel.π (c1a5Chains.map (f i)))).1
  simp only [CategoryTheory.Limits.Sigma.ι_map_assoc, Category.assoc]
  simp only [c1a5RelativeUnit, cokernel.map, cokernel.π_desc_assoc,
    cokernel.π_desc, Category.assoc]
  rw [c1a5_relative_coproduct_iso_projection]
  rw [← Category.assoc, c1a5_relative_coproduct_iso_projection_assoc]
  simp only [Category.assoc, cokernel.π_desc]
  simpa only [Category.assoc] using
    (congrArg (fun t ↦ t ≫ cokernel.π (c1a5SingularChains.map (CategoryTheory.Limits.Sigma.map f)))
      (c1a5Unit_naturality (CategoryTheory.Limits.Sigma.ι B i))).symm

/-- Relative unit comparison passes to finite coproducts of the actual pairs.
Source: Hatcher §2.1, relative homology of disjoint unions. -/
lemma c1a5_relative_unit_finite_coproduct {I : Type} [Finite I]
    {A B : I → SSet.{0}} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, QuasiIso (c1a5RelativeUnit (f i))) :
    QuasiIso (c1a5RelativeUnit (CategoryTheory.Limits.Sigma.map f)) := by
  have hsum := c1a5_finite_coproduct_comparison (fun i ↦ c1a5RelativeUnit (f i)) hf
  have hcomp : QuasiIso ((c1a5_relative_coproduct_iso c1a5Chains f).hom ≫
      c1a5RelativeUnit (CategoryTheory.Limits.Sigma.map f)) := by
    rw [← c1a5_relative_unit_coproduct_naturality]
    infer_instance
  exact (quasiIso_iff_comp_left (c1a5_relative_coproduct_iso c1a5Chains f).hom
    (c1a5RelativeUnit (CategoryTheory.Limits.Sigma.map f))).1 hcomp

end HodgeLean.Foundations.Program
