import HodgeLean.Foundations.Program.SchoenSelectedGeometryQuasiFiniteDimension
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A specializing scheme map lifts every descending chain from its image. -/
theorem s2e_height_image_le_of_specializing
    {X Y : Scheme} (f : X ⟶ Y) (hf : SpecializingMap f) (x : X) :
    Order.height (f x) ≤ Order.height x := by
  refine Order.height_le_iff'.mpr ?_
  intro p hp
  induction p using RelSeries.inductionOn' generalizing x with
  | singleton y => simp
  | snoc p y hy ih =>
    simp only [RelSeries.last_snoc] at hp
    change p.last < y at hy
    obtain ⟨x', hx', he⟩ := hf (by
      rw [← hp]
      exact Scheme.le_iff_specializes.mp hy.le)
    have hlt : x' < x := by
      refine ⟨Scheme.le_iff_specializes.mpr hx', ?_⟩
      intro hback
      have hxx : x = x' :=
        (hx'.antisymm (Scheme.le_iff_specializes.mp hback)).eq
      subst x'
      exact hy.ne (he.symm.trans hp.symm)
    have hlen := ih x' he.symm
    have hadd : (p.length : ℕ∞) + 1 ≤ Order.height x' + 1 :=
      add_le_add hlen le_rfl
    simpa only [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one] using
      hadd.trans (Order.height_add_one_le hlt)

/-- A finite surjective morphism preserves global Krull dimension when the
target is integral. -/
theorem s2e_finite_surjective_krull_dimension
    {X Y : Scheme.{0}} [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  apply le_antisymm (s0_quasiFinite_krull_dimension_le f)
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim Y,
    Scheme.topologicalKrullDim_eq_orderKrullDim X, ← Order.height_top_eq_krullDim]
  obtain ⟨x, hx⟩ := f.surjective (⊤ : Y)
  calc
    (Order.height (⊤ : Y) : WithBot ℕ∞) = Order.height (f x) := by rw [hx]
    _ ≤ Order.height x := WithBot.coe_le_coe.mpr
      (s2e_height_image_le_of_specializing f f.isClosedMap.specializingMap x)
    _ ≤ Order.krullDim X := Order.height_le_krullDim x

end HodgeLean.Foundations.Program
