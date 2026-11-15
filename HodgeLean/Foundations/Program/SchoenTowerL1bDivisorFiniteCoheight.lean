import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Properties
import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Discrete fibers prevent a locally quasi-finite map from collapsing a strict specialization. -/
theorem s2v_l1b_divisor_quasi_finite_strictMono
    {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f] : StrictMono f := by
  intro x y hxy
  have hmono : f x ≤ f y := (show y ⤳ x from hxy.le).map f.continuous
  refine lt_iff_le_not_ge.mpr ⟨hmono, ?_⟩
  intro hrev
  have he : f x = f y := inseparable_iff_eq.mp
    (inseparable_iff_specializes_and.mpr ⟨hrev, hmono⟩)
  let F := f ⁻¹' {f x}
  letI : DiscreteTopology F :=
    isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton (f x))
  let xF : F := ⟨x, rfl⟩
  let yF : F := ⟨y, he.symm⟩
  have hspec : yF ⤳ xF := (subtype_specializes_iff _ _).mpr hxy.le
  exact hxy.ne (congrArg Subtype.val hspec.eq).symm

/-- The codimension of a point cannot increase under a locally quasi-finite source lift. -/
theorem s2v_l1b_divisor_quasi_finite_coheight_le
    {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) :
    Order.coheight x ≤ Order.coheight (f x) :=
  Order.coheight_le_coheight_apply_of_strictMono f
    (s2v_l1b_divisor_quasi_finite_strictMono f) x

/-- A point over a codimension-one point under a dominant quasi-finite map also has codimension one. -/
theorem s2v_l1b_divisor_quasi_finite_coheight_one
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyQuasiFinite f] [IsDominant f]
    (x : X) (hy : Order.coheight (f x) = 1) : Order.coheight x = 1 := by
  have hle := s2v_l1b_divisor_quasi_finite_coheight_le f x
  rw [hy] at hle
  have hne : Order.coheight x ≠ 0 := by
    intro hx
    have hxg := eq_genericPoint_of_coheight_zero x hx
    have hfg : f x = genericPoint Y := by
      rw [hxg, s2_dominant_genericPoint f]
    have hgy : Order.coheight (genericPoint Y) = 0 :=
      Order.coheight_eq_zero.mpr (fun y _ => genericPoint_specializes y)
    rw [hfg, hgy] at hy
    exact zero_ne_one hy
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

end HodgeLean.Foundations.Program
