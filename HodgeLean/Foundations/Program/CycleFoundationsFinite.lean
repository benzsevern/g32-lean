import HodgeLean.Foundations.Program.CycleFoundationsDefs
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! Iterated products for varying abelian factors. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

def cfd_product : (r : ℕ) → (Fin r → Over (Spec ↧ℂ)) → Over (Spec ↧ℂ)
  | 0, _ => 𝟙_ _
  | r + 1, A => A 0 ⊗ cfd_product r (fun i => A i.succ)

instance cfd_product_grp : ∀ (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)], GrpObj (cfd_product r A)
  | 0, _, _ => inferInstanceAs (GrpObj (𝟙_ (Over (Spec ↧ℂ))))
  | r + 1, A, _ =>
    letI := cfd_product_grp r (fun i => A i.succ)
    inferInstanceAs (GrpObj (A 0 ⊗ cfd_product r (fun i => A i.succ)))

instance cfd_product_comm : ∀ (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (A i)] [∀ i, IsCommMonObj (A i)], IsCommMonObj (cfd_product r A)
  | 0, _, _, _ => inferInstanceAs (IsCommMonObj (𝟙_ (Over (Spec ↧ℂ))))
  | r + 1, A, _, _ =>
    letI := cfd_product_comm r (fun i => A i.succ)
    inferInstanceAs (IsCommMonObj (A 0 ⊗ cfd_product r (fun i => A i.succ)))

instance cfd_product_smooth : ∀ (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, Smooth (A i).hom], Smooth (cfd_product r A).hom
  | 0, _, _ => inferInstanceAs (Smooth (𝟙 (Spec ↧ℂ)))
  | r + 1, A, _ => by
    letI := cfd_product_smooth r (fun i => A i.succ)
    change Smooth (Limits.pullback.fst (A 0).hom (cfd_product r (fun i => A i.succ)).hom ≫ (A 0).hom)
    infer_instance

instance cfd_product_integral : ∀ (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom], IsIntegral (cfd_product r A).left
  | 0, _, _, _, _ => inferInstanceAs (IsIntegral (Spec ↧ℂ))
  | r + 1, A, _, _, _ => by
    letI := cfd_product_integral r (fun i => A i.succ)
    exact gagam_product_isIntegral (A 0) (cfd_product r (fun i => A i.succ))

instance cfd_product_projective : ∀ (r : ℕ) (A : Fin r → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (A i).left] [∀ i, Smooth (A i).hom]
    [∀ i, IsProjective (A i).hom], IsProjective (cfd_product r A).hom
  | 0, _, _, _, _ => HodgeLean.Foundations.isProjective_specComplex_id
  | r + 1, A, _, _, _ => by
    letI := cfd_product_projective r (fun i => A i.succ)
    exact gagam_product_projective (A 0) (cfd_product r (fun i => A i.succ))

def cfd_proj : ∀ (r : ℕ) (A : Fin r → Over (Spec ↧ℂ)) (i : Fin r), cfd_product r A ⟶ A i
  | 0, _, i => i.elim0
  | r + 1, A, i => Fin.cases (fst (A 0) (cfd_product r (fun j => A j.succ)))
      (fun j => snd (A 0) (cfd_product r (fun k => A k.succ)) ≫ cfd_proj r (fun k => A k.succ) j) i

theorem cfd_product_limit (r : ℕ) (A : Fin r → Over (Spec ↧ℂ)) :
    Nonempty (Limits.IsLimit (Limits.Fan.mk (cfd_product r A) (cfd_proj r A))) := by
  induction r with
  | zero =>
    exact ⟨Limits.IsLimit.mk (fun s => SemiCartesianMonoidalCategory.toUnit s.pt)
      (fun s j => j.as.elim0) (fun _ _ _ => SemiCartesianMonoidalCategory.toUnit_unique _ _)⟩
  | succ r ih =>
    obtain ⟨ih⟩ := ih (fun i => A i.succ)
    refine ⟨(extendFanIsLimit A ih
      (tensorProductIsBinaryProduct (A 0) (cfd_product r (fun i => A i.succ)))).ofIsoLimit
      (Limits.Cone.ext (Iso.refl _) ?_)⟩
    rintro ⟨j⟩
    refine Fin.cases ?_ (fun i => ?_) j <;> exact (Category.id_comp _).symm

end HodgeLean.Foundations.Program
