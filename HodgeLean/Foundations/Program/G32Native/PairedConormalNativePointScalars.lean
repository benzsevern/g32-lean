import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeRowZero
import HodgeLean.Foundations.Program.G32Native.PairedConormalPointRelationScalars

/-! # Literal point scalars of normalized native ideal rows -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual normalized native ideal frame specialized at the supplied point. -/
def conormalNativeIdealPointFrame (k : ℕ) (i : Fin (k + 1))
    (x : ComplexPoint (conormalPolynomialModelOver k))
    (hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1) :=
  i1_localModuleSectionSpecialization (Q := conormalPolynomialModelOver k)
    (idealModule (conormalNativeHyperplaneIdeal ℂ k)) (conormalNativeCoordinateOpen ℂ k i).1
    (conormalNativeHyperplaneNormalizedPullbackFrame k i).hom x hx

/-- Normalization stays invertible in the actual point pullback. -/
theorem conormalNativeIdealPointFrame_isIso (k : ℕ) (i : Fin (k + 1))
    (x : ComplexPoint (conormalPolynomialModelOver k))
    (hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1) :
    IsIso (conormalNativeIdealPointFrame k i x hx) :=
  conormal_local_section_specialization_isIso (Q := conormalPolynomialModelOver k)
    (idealModule (conormalNativeHyperplaneIdeal ℂ k)) (conormalNativeCoordinateOpen ℂ k i).1
    (conormalNativeHyperplaneNormalizedPullbackFrame k i).hom x hx

/-- The original row's specialized scalar is its literal regular coefficient
at the supplied point, retaining the normalized ideal frame. -/
theorem conormal_native_ideal_row_point_scalar (k : ℕ) (i : Fin (k + 1))
    (φ : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf)
    (x : ComplexPoint (conormalPolynomialModelOver k))
    (hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (conormalNativeIdealPointFrame k i x hx ≫
          (Scheme.Modules.pullback x.left).map φ ≫ (pullbackUnit x.left).hom))
          (1 : Γ(Spec ↧ℂ, ⊤))) =
      Point.evaluate (conormalNativeCoordinateOpen ℂ k i).1
        (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k) φ
          (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
          (conormal_native_hyperplane_coordinate_mem ℂ k i)) x := by
  let U := conormalNativeCoordinateOpen ℂ k i
  let s := (conormalNativeHyperplaneNormalizedPullbackFrame k i).hom
  have hsc := conormal_local_unit_section_scalar (Q := conormalPolynomialModelOver k) U.1
    (s ≫ (Scheme.Modules.pullback U.1.ι).map φ) x hx
  have hcoef := conormal_native_normalized_frame_scalar k i φ
  simp only [Category.assoc] at hsc
  rw [hcoef] at hsc
  dsimp only [U] at hsc
  have hcancel := (conormalNativeCoordinateOpen ℂ k i).1.topIso.inv_hom_id_apply
    (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k) φ
      (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
      (conormal_native_hyperplane_coordinate_mem ℂ k i))
  have hsc' := hsc.trans (congrArg (fun r => Point.evaluate U.1 r x) hcancel)
  rw [i1_localModuleSectionSpecialization_naturality] at hsc'
  exact hsc'

/-- The distinguished coordinate of the actual relation vector is the
actual coefficient value of its distinguished ideal row. -/
theorem conormal_native_point_relation_vector_fst (k : ℕ) (i : Fin (k + 1))
    (a : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf)
    (b : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.free
        (R := (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf) (Fin k))
    (x : ComplexPoint (conormalPolynomialModelOver k))
    (hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1) :
    (conormalPointRelationVector k a b x.left (conormalNativeIdealPointFrame k i x hx)).1 =
      Point.evaluate (conormalNativeCoordinateOpen ℂ k i).1
        (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k) a
          (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
          (conormal_native_hyperplane_coordinate_mem ℂ k i)) x := by
  rw [conormal_point_relation_vector_fst]
  exact conormal_native_ideal_row_point_scalar k i a x hx

/-- Every tail coordinate of the actual relation vector retains its
original row's coefficient, with no sign or scalar normalization omitted. -/
theorem conormal_native_point_relation_vector_row (k : ℕ) (i : Fin (k + 1))
    (a : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf)
    (b : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.free
        (R := (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf) (Fin k))
    (x : ComplexPoint (conormalPolynomialModelOver k))
    (hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1) (t : Fin k) :
    (conormalPointRelationVector k a b x.left (conormalNativeIdealPointFrame k i x hx)).2 t =
      Point.evaluate (conormalNativeCoordinateOpen ℂ k i).1
        (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k)
          (b ≫ i1_freeSheafProjection
            (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)) k t)
          (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
          (conormal_native_hyperplane_coordinate_mem ℂ k i)) x := by
  rw [conormal_point_relation_vector_row]
  exact conormal_native_ideal_row_point_scalar k i
    (b ≫ i1_freeSheafProjection
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)) k t) x hx

/-- The entire normalized point relation retains the exact ordered list
of regular coefficient values from its actual sheaf rows. -/
theorem conormal_native_point_relation_vector (k : ℕ) (i : Fin (k + 1))
    (a : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf)
    (b : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.free
        (R := (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf) (Fin k))
    (x : ComplexPoint (conormalPolynomialModelOver k))
    (hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1) :
    conormalPointRelationVector k a b x.left (conormalNativeIdealPointFrame k i x hx) =
      (Point.evaluate (conormalNativeCoordinateOpen ℂ k i).1
        (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k) a
          (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
          (conormal_native_hyperplane_coordinate_mem ℂ k i)) x,
       fun t => Point.evaluate (conormalNativeCoordinateOpen ℂ k i).1
        (conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k)
          (b ≫ i1_freeSheafProjection
            (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)) k t)
          (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
          (conormal_native_hyperplane_coordinate_mem ℂ k i)) x) := by
  apply Prod.ext
  · exact conormal_native_point_relation_vector_fst k i a b x hx
  · funext t
    exact conormal_native_point_relation_vector_row k i a b x hx t

/-- A regular coefficient is continuous on the analytic points of its own open. -/
theorem conormal_regularEvaluation_open_continuous {Q : Over (Spec ↧ℂ)}
    (U : Q.left.Opens) (r : Γ(Q.left, U)) :
    Continuous (fun x : ↥(Point.overOpen U : Set (ComplexPoint Q)) =>
      Point.evaluate U r x.1) := by
  apply continuous_def.mpr
  intro O hO
  have h := Point.isOpen_overOpen_inter_preimage (X := Q) U r O hO
  convert h.preimage continuous_subtype_val using 1
  ext x
  exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩

/-- The actual normalized relation column varies continuously on its chart,
using the original row values rather than a separately selected point frame. -/
theorem conormal_native_point_relation_vector_continuous (k : ℕ) (i : Fin (k + 1))
    (a : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf)
    (b : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.free
        (R := (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf) (Fin k)) :
    Continuous (fun x : ↥(Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1 :
        Set (ComplexPoint (conormalPolynomialModelOver k))) =>
      conormalPointRelationVector k a b x.1.left (conormalNativeIdealPointFrame k i x.1 x.2)) := by
  have h := fun x : ↥(Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1 :
      Set (ComplexPoint (conormalPolynomialModelOver k))) =>
    conormal_native_point_relation_vector k i a b x.1 x.2
  simp_rw [h]
  exact (conormal_regularEvaluation_open_continuous _ _).prodMk
    (continuous_pi (fun _ => conormal_regularEvaluation_open_continuous _ _))

#print axioms conormalNativeIdealPointFrame
#print axioms conormalNativeIdealPointFrame_isIso
#print axioms conormal_native_ideal_row_point_scalar
#print axioms conormal_native_point_relation_vector_fst
#print axioms conormal_native_point_relation_vector_row
#print axioms conormal_native_point_relation_vector
#print axioms conormal_regularEvaluation_open_continuous
#print axioms conormal_native_point_relation_vector_continuous
end HodgeLean.Foundations.Program.G32Native
