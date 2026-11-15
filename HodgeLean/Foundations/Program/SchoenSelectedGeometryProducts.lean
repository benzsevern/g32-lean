import HodgeLean.Foundations.Program.SchoenSelectedGeometryCurveInverse
import HodgeLean.Foundations.SegreProjective
import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Adapters.AbelianPower

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open MonoidalCategory CartesianMonoidalCategory
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Split a finite tuple into its first entry and its remaining entries.
Source: the product topology and the recursion principle for `Fin`. -/
def s0_tuple_succ_homeomorph (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    (Fin (n + 1) → Y) ≃ₜ Y × (Fin n → Y) where
  toFun f := (f 0, fun i ↦ f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by ext i; exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv p := by cases p; rfl
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi (fun i ↦ continuous_apply i.succ))
  continuous_invFun := continuous_pi (fun i ↦ Fin.cases continuous_fst
    (fun j ↦ (continuous_apply j).comp continuous_snd) i)

#print axioms s0_tuple_succ_homeomorph
/-- Complex points of an iterated scheme product are tuples with the product topology.
Source: preservation of products by representable points and `complexPointProdHomeomorph`. -/
def s0_power_point_homeomorph (A : Over (Spec ↧ℂ)) :
    (n : ℕ) → ComplexPoint (g3_power A n) ≃ₜ (Fin n → ComplexPoint A)
  | 0 => by
      letI : Unique (ComplexPoint (g3_power A 0)) :=
        { default := 𝟙 _
          uniq := fun p ↦ by
            apply CostructuredArrow.hom_ext
            have h : p.left ≫ 𝟙 (Spec ↧ℂ) = 𝟙 (Spec ↧ℂ) := p.w
            change p.left = 𝟙 (Spec ↧ℂ)
            exact (Category.comp_id (obj := Scheme.{0}) p.left).symm.trans h }
      exact Homeomorph.homeomorphOfUnique _ _
  | n + 1 => (complexPointProdHomeomorph A (g3_power A n)).trans
      ((Homeomorph.refl _).prodCongr (s0_power_point_homeomorph A n) |>.trans
        (s0_tuple_succ_homeomorph (ComplexPoint A) n).symm)

#print axioms s0_power_point_homeomorph
end HodgeLean.Foundations.Program
