import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialRowZero
import HodgeLean.Foundations.Program.G32Native.PairedConormalComparedProjectionDetection
import HodgeLean.Foundations.Program.G32Native.PairedConormalOriginalLinearForms
import HodgeLean.Foundations.Program.G32Native.PairedConormalDistinguishedCoordinate
import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialRelationNonzero
import HodgeLean.Foundations.NormalPresentation.Defs

/-! # Common zeros of the actual homogeneous relation rows -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.NormalPresentation
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pointwise nonvanishing of the actual original relation rules out every
nonzero common homogeneous zero of its specified original linear rows. -/
theorem conormal_actual_relation_rows_common_zero (k : ℕ)
    (b : idealModule (s2e_hyperplaneIdeal k) ⟶
      (SheafOfModules.free (Fin k) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules))
    (hrel : ∀ x : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))),
      (Scheme.Modules.pullback x.left).map (relation
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (s2e_hyperplaneIdeal k).subschemeι.toRingCatSheafHom)) b) ≠ 0)
    (p : Fin k → homogeneousSubmodule (Fin (k + 1)) ℂ 1)
    (hp : ∀ (t : Fin k) (j : Fin (k + 1)),
      conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k)
        (conormalOriginalIdealRow k k b t) (conormalNativeCoordinateOpen ℂ k j)
        (ProjSpace.coordinateRatioSection ℂ k j 0) (conormal_native_hyperplane_coordinate_mem ℂ k j) =
          ProjSpace.homogeneousRatioSection ℂ k 1 (p t) j)
    (v : CoordinateSpace k) (h0 : v 0 = 0) (ht : ∀ t : Fin k, eval v (p t).val = 0) : v = 0 := by
  classical
  by_contra hv
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  let f := (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
  let F := Scheme.Modules.pullback f
  let x := conormalPolynomialChartComplexPoint v i hi
  let G := Scheme.Modules.pullback x.left
  let a0 := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (s2e_hyperplaneIdeal k).subschemeι.toRingCatSheafHom)
  let r := relation a0 b
  let a := (conormalHyperplanePolynomialIdealIso k).inv ≫ F.map r
  let n0 := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (conormalNativeHyperplaneIdeal ℂ k).subschemeι.toRingCatSheafHom)
  have hr0 : r ≫ biprod.fst = a0 := biprod.lift_fst a0 b
  have hrsnd : r ≫ biprod.snd = b := biprod.lift_snd a0 b
  have he0 : a ≫ (F.map biprod.fst ≫ (pullbackUnit f).hom) = n0 := by
    calc
      _ = (conormalHyperplanePolynomialIdealIso k).inv ≫ F.map (r ≫ biprod.fst) ≫
          (pullbackUnit f).hom := by simp only [a, CategoryTheory.Functor.map_comp, Category.assoc]
      _ = (conormalHyperplanePolynomialIdealIso k).inv ≫ F.map a0 ≫
          (pullbackUnit f).hom := by rw [hr0]
      _ = n0 := conormalHyperplanePolynomialIdealIso_inv_inclusion k
  have hei (t : Fin k) : a ≫ (F.map (biprod.snd ≫
      i1_freeSheafProjection (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) k t) ≫
        (pullbackUnit f).hom) = conormalOriginalIdealRow k k b t := by
    have hr : r ≫ (biprod.snd ≫
        i1_freeSheafProjection (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) k t) =
        b ≫ i1_freeSheafProjection (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) k t := by
      rw [← Category.assoc, hrsnd]
    calc
      _ = (conormalHyperplanePolynomialIdealIso k).inv ≫ F.map (r ≫ (biprod.snd ≫
          i1_freeSheafProjection (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) k t)) ≫
            (pullbackUnit f).hom := by simp only [a, CategoryTheory.Functor.map_comp, Category.assoc]
      _ = _ := by rw [hr]; rfl
  have hn0 : G.map n0 = 0 := by
    apply (conormal_polynomial_ideal_row_pullback_zero_iff k n0
      (conormalCoordinatePolynomial ℂ k 0)
      (conormal_native_hyperplane_inclusion_numerator k) v i hi).mpr
    simpa only [conormalCoordinatePolynomial, eval_X] using h0
  have hni (t : Fin k) : G.map (conormalOriginalIdealRow k k b t) = 0 :=
    (conormal_polynomial_ideal_row_pullback_zero_iff k (conormalOriginalIdealRow k k b t)
      (p t) (hp t) v i hi).mpr (ht t)
  have hne := conormal_polynomial_ideal_relation_pullback_ne_zero k r hrel x
  apply hne
  apply conormal_compared_unit_free_projections_detect_zero f x.left k (G.map a)
  · have hh := (congrArg (fun z => G.map z) he0).trans hn0
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc, F, G] using hh
  · intro t
    have hh := (congrArg (fun z => G.map z) (hei t)).trans (hni t)
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc, F, G] using hh

end HodgeLean.Foundations.Program.G32Native
