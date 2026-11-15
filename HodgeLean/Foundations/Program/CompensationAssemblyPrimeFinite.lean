import HodgeLean.Foundations.Program.CompensationAssemblyProjectionDimension
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cq_projection_prime_fiber_eq
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) = 3) :
    {q : (A ⊗ Y).left | q ∈ closure {x} ∧ (fst A Y).left q = (fst A Y).left x} = {x} := by
  have hdeg := (cq_projection_prime_degree_pos_iff A Y hA hY x hx).mpr himage
  have hh := (a1p_degree_pos_iff (fst A Y) x).mp hdeg
  have hxheight := cq_projection_prime_height A Y hA hY x hx
  ext q
  constructor
  · rintro ⟨hq, hf⟩
    apply Set.mem_singleton_iff.mpr
    have hqx : q ≤ x := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hq)
    have hbound := cq_height_image_le (fst A Y) q
    rw [hf, hh] at hbound
    have heqh : Order.height q = Order.height x :=
      le_antisymm (Order.height_mono hqx) hbound
    by_contra hne
    have hlt : Order.height q < Order.height x :=
      Order.height_strictMono
        (lt_of_le_not_ge hqx (fun h => hne
          ((Scheme.le_iff_specializes.mp h).antisymm (Scheme.le_iff_specializes.mp hqx)).eq))
        (by rw [heqh, hxheight]; exact ENat.natCast_lt_top 3)
    exact (ne_of_lt hlt) heqh
  · intro hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact ⟨subset_closure (Set.mem_singleton _), rfl⟩

theorem cq_projection_prime_finite_neighborhood
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) = 3) :
    ∃ U : A.left.Opens, (fst A Y).left x ∈ U ∧
      IsFinite ((cycleComponentι (A ⊗ Y).left x ≫ (fst A Y).left) ∣_ U) := by
  let inc := cycleComponentι (A ⊗ Y).left x
  let f := inc ≫ (fst A Y).left
  letI : IsProper (fst A Y).left :=
    inferInstanceAs (IsProper (Limits.pullback.fst A.hom Y.hom))
  letI : IsProper f := inferInstanceAs (IsProper (inc ≫ (fst A Y).left))
  have hi (q : cycleComponent (A ⊗ Y).left x) : inc q ∈ closure {x} := by
    rw [← range_cycleComponentι (A ⊗ Y).left x]
    exact ⟨q, rfl⟩
  have hfin : (f ⁻¹' {(fst A Y).left x}).Finite := by
    apply Set.Finite.of_finite_image (f := inc) _ inc.isClosedEmbedding.injective.injOn
    apply (Set.finite_singleton x).subset
    rintro _ ⟨q, hq, rfl⟩
    apply (Set.ext_iff.mp (cq_projection_prime_fiber_eq A Y hA hY x hx himage) (inc q)).mp
    exact ⟨hi q, hq⟩
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton f _ hfin

end HodgeLean.Foundations.Program
