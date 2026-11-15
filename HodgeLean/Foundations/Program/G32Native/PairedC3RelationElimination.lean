import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Global elimination of an invertible relation coefficient -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
variable {L M : C}

/-- Eliminate the first coefficient of a relation when it is an
isomorphism. This is a global categorical operation on the actual maps. -/
def pairedC3RelationProjection (r : L ⟶ L ⊞ M) [IsIso (r ≫ biprod.fst)] :
    L ⊞ M ⟶ M :=
  biprod.desc (-(inv (r ≫ biprod.fst) ≫ r ≫ biprod.snd)) (𝟙 M)

/-- The elimination projection kills the original relation. -/
theorem paired_c3_relation_projection_zero (r : L ⟶ L ⊞ M)
    [IsIso (r ≫ biprod.fst)] : r ≫ pairedC3RelationProjection r = 0 := by
  have hr : r = biprod.lift (r ≫ biprod.fst) (r ≫ biprod.snd) := by
    apply biprod.hom_ext <;> simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd]
  dsimp only [pairedC3RelationProjection]
  conv_lhs => lhs; rw [hr]
  rw [biprod.lift_desc, Preadditive.comp_neg,
    IsIso.hom_inv_id_assoc, Category.comp_id, neg_add_cancel]

/-- The remaining summand is the cokernel of the retained relation,
with its actual elimination projection. -/
def pairedC3RelationProjectionIsCokernel (r : L ⟶ L ⊞ M)
    [IsIso (r ≫ biprod.fst)] :
    IsColimit (CokernelCofork.ofπ (pairedC3RelationProjection r)
      (paired_c3_relation_projection_zero r)) := by
  refine CokernelCofork.IsColimit.ofπ _ _ (fun g _ => biprod.inr ≫ g) ?_ ?_
  · intro Z g hg
    apply biprod.hom_ext'
    · have hr : r = biprod.lift (r ≫ biprod.fst) (r ≫ biprod.snd) := by
        apply biprod.hom_ext <;> simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd]
      have hgr : (r ≫ biprod.fst) ≫ biprod.inl ≫ g +
          (r ≫ biprod.snd) ≫ biprod.inr ≫ g = 0 := by
        rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
          ← biprod.lift_eq, ← hr]
        exact hg
      have hh := congrArg (fun f => inv (r ≫ biprod.fst) ≫ f) hgr
      simp only [Preadditive.comp_add,
        IsIso.inv_hom_id_assoc, comp_zero] at hh
      dsimp only [pairedC3RelationProjection]
      rw [biprod.inl_desc_assoc, Preadditive.neg_comp]
      simpa only [Category.assoc, Preadditive.neg_comp] using
        (eq_neg_of_add_eq_zero_left hh).symm
    · simp only [pairedC3RelationProjection, biprod.inr_desc_assoc, Category.id_comp]
  · intro Z g hg m hm
    have h := congrArg (fun f => biprod.inr ≫ f) hm
    simpa only [pairedC3RelationProjection, biprod.inr_desc_assoc,
      Category.assoc, Category.id_comp] using h

/-- A single invertible coefficient determines the actual cokernel
object globally, without choosing local bundle frames. -/
def pairedC3RelationCokernelIso (r : L ⟶ L ⊞ M)
    [IsIso (r ≫ biprod.fst)] [HasCokernel r] : cokernel r ≅ M :=
  (cokernelIsCokernel r).coconePointUniqueUpToIso
    (pairedC3RelationProjectionIsCokernel r)

/-- The global identification retains the original cokernel projection.
The minus sign in the elimination row is therefore fixed. -/
theorem paired_c3_relation_cokernel_projection (r : L ⟶ L ⊞ M)
    [IsIso (r ≫ biprod.fst)] [HasCokernel r] :
    cokernel.π r ≫ (pairedC3RelationCokernelIso r).hom =
      pairedC3RelationProjection r :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel r) (pairedC3RelationProjectionIsCokernel r)
    WalkingParallelPair.one

#print axioms paired_c3_relation_cokernel_projection
#print axioms pairedC3RelationProjection
#print axioms paired_c3_relation_projection_zero
#print axioms pairedC3RelationProjectionIsCokernel
#print axioms pairedC3RelationCokernelIso
end HodgeLean.Foundations.Program.G32Native
