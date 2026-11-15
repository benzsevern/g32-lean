import HodgeLean.Foundations.Program.CompensationAssemblyProjectionDimension

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cfd_product_dimension (a d : ℕ)
    (hA : TopologicalSpace.dim A.left = a) (hY : TopologicalSpace.dim Y.left = d) :
    TopologicalSpace.dim (A ⊗ Y).left = a + d := by
  letI : SmoothOfRelativeDimension a A.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
    rwa [hA] at h
  letI : SmoothOfRelativeDimension d Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  letI : SmoothOfRelativeDimension d (fst A Y).left :=
    inferInstanceAs (SmoothOfRelativeDimension d (Limits.pullback.fst A.hom Y.hom))
  letI : SmoothOfRelativeDimension (a + d) (A ⊗ Y).hom := by
    have h : SmoothOfRelativeDimension (d + a) ((fst A Y).left ≫ A.hom) := inferInstance
    rwa [Over.w (fst A Y), Nat.add_comm d a] at h
  exact SmoothOfRelativeDimension.dim_eq (f := (A ⊗ Y).hom) (a + d)

theorem cfd_projection_image_coheight_ge (d s q : ℕ)
    (hY : TopologicalSpace.dim Y.left = d) (hs : s = q + d)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s) :
    (q : ℕ∞) ≤ Order.coheight ((fst A Y).left x) := by
  let a := TopologicalSpace.dim A.left
  have hsource := cq_point_height_add_coheight (A ⊗ Y) (a + d)
    (cfd_product_dimension A Y a d rfl hY) x
  rw [hx, hs, Nat.cast_add, Nat.cast_add, ← add_assoc] at hsource
  have hxq : Order.height x + (q : ℕ∞) = a :=
    ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top d) hsource
  have hfinite : Order.height x ≠ ⊤ := by
    intro ht
    rw [ht, top_add] at hxq
    exact (ENat.natCast_ne_top a) hxq.symm
  have hbase := cq_point_height_add_coheight A a rfl ((fst A Y).left x)
  have hle : Order.height x + (q : ℕ∞) ≤
      Order.height x + Order.coheight ((fst A Y).left x) := by
    calc
      Order.height x + (q : ℕ∞) = a := hxq
      _ = Order.height ((fst A Y).left x) + Order.coheight ((fst A Y).left x) := hbase.symm
      _ ≤ _ := add_le_add (cq_height_image_le (fst A Y) x) le_rfl
  exact (ENat.add_le_add_iff_left hfinite).mp hle

end HodgeLean.Foundations.Program
