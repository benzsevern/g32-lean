import HodgeLean.Foundations.Program.CompensationAssemblyProjectionUnique
import HodgeLean.Adapters.KleimanExpectedCoheight

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

variable (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cq_projection_product_dimension
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2) :
    TopologicalSpace.dim (A ⊗ Y).left = 8 := by
  letI : SmoothOfRelativeDimension 6 A.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
    rwa [hA] at h
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  letI : SmoothOfRelativeDimension 2 (fst A Y).left :=
    inferInstanceAs (SmoothOfRelativeDimension 2 (Limits.pullback.fst A.hom Y.hom))
  letI : SmoothOfRelativeDimension 8 (A ⊗ Y).hom := by
    have h : SmoothOfRelativeDimension (2 + 6) ((fst A Y).left ≫ A.hom) :=
      inferInstanceAs (SmoothOfRelativeDimension (2 + 6) ((fst A Y).left ≫ A.hom))
    rwa [Over.w (fst A Y)] at h
  exact SmoothOfRelativeDimension.dim_eq (f := (A ⊗ Y).hom) 8

theorem cq_point_height_add_coheight
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (d : ℕ) (hd : TopologicalSpace.dim X.left = d) (x : X.left) :
    Order.height x + Order.coheight x = d := by
  letI : SmoothOfRelativeDimension d X.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := X.hom)
    rwa [hd] at h
  refine hc9k8_height_add_coheight_of_integral X.hom d (fun U hU hne => ?_) x
  exact hc9k8_ringKrullDim_affineOpen X.hom d
    (fun z hz => SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
      (f := X.hom) z hz) U hU hne

theorem cq_projection_prime_height
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5) : Order.height x = 3 := by
  have h := cq_point_height_add_coheight (A ⊗ Y) 8
    (cq_projection_product_dimension A Y hA hY) x
  rw [hx] at h
  exact ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top 5)
    (show Order.height x + (5 : ℕ∞) = (3 : ℕ∞) + 5 from h)

theorem cq_projection_prime_degree_pos_iff
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5) :
    0 < a1p_degree (fst A Y).left x ↔ Order.coheight ((fst A Y).left x) = 3 := by
  have hxheight := cq_projection_prime_height A Y hA hY x hx
  have himage := cq_point_height_add_coheight A 6 hA ((fst A Y).left x)
  rw [a1p_degree_pos_iff]
  constructor
  · intro h
    rw [h, hxheight] at himage
    exact ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top 3)
      (show (3 : ℕ∞) + Order.coheight ((fst A Y).left x) = (3 : ℕ∞) + 3 from himage)
  · intro h
    rw [h] at himage
    have hheight : Order.height ((fst A Y).left x) = 3 :=
      ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top 3)
        (show Order.height ((fst A Y).left x) + (3 : ℕ∞) = (3 : ℕ∞) + 3 from himage)
    exact hheight.trans hxheight.symm

theorem cq_projection_prime_degree_eq_zero
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) ≠ 3) :
    a1p_degree (fst A Y).left x = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact himage ((cq_projection_prime_degree_pos_iff A Y hA hY x hx).mp hpos)

theorem cq_height_image_le {X Z : Over (Spec ↧ℂ)} (f : X ⟶ Z)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom] (x : X.left) :
    Order.height (f.left x) ≤ Order.height x := by
  letI : Algebra ℂ (X.left.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
  letI : Algebra ℂ (Z.left.residueField (f.left x)) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Z.hom.appTop ≫
      Z.left.Γevaluation (f.left x)).hom.toAlgebra
  letI : Algebra (Z.left.residueField (f.left x)) (X.left.residueField x) :=
    (f.left.residueFieldMap x).hom.toAlgebra
  letI : IsScalarTower ℂ (Z.left.residueField (f.left x)) (X.left.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = f.left.residueFieldMap x (Z.left.Γevaluation (f.left x) (Z.hom.appTop _))
    rw [Scheme.Γevaluation_naturality_apply]
    change _ = X.left.Γevaluation x ((Z.hom.appTop ≫ f.left.appTop) _)
    rw [← Scheme.Hom.comp_appTop, Over.w f]
    rfl
  obtain ⟨-, n, hn, htr⟩ := a1d_height_eq_trdeg x
  obtain ⟨-, m, hm, htr'⟩ := a1d_height_eq_trdeg (f.left x)
  have hadd := trdeg_add_eq ℂ (Z.left.residueField (f.left x)) (A := X.left.residueField x)
  rw [htr, htr'] at hadd
  have hle : (m : Cardinal) ≤ (n : Cardinal) := le_self_add.trans hadd.le
  have hmn : m ≤ n := by exact_mod_cast hle
  rw [hn, hm]
  exact_mod_cast hmn

theorem cq_projection_image_coheight_ge_three
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5) :
    (3 : ℕ∞) ≤ Order.coheight ((fst A Y).left x) := by
  have hheight := cq_height_image_le (fst A Y) x
  rw [cq_projection_prime_height A Y hA hY x hx] at hheight
  have hsum := cq_point_height_add_coheight A 6 hA ((fst A Y).left x)
  have hle : (3 : ℕ∞) + 3 ≤ (3 : ℕ∞) + Order.coheight ((fst A Y).left x) := by
    calc
      (3 : ℕ∞) + 3 = Order.height ((fst A Y).left x) +
          Order.coheight ((fst A Y).left x) := hsum.symm
      _ ≤ (3 : ℕ∞) + Order.coheight ((fst A Y).left x) := add_le_add hheight le_rfl
  exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top 3)).mp hle

end HodgeLean.Foundations.Program
