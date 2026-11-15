import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Foundations.Program.SchoenSumZeroAction
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientTopology
import HodgeLean.Foundations.Program.SchoenCycleC2IsoPointHelpers

/-! Topology of the retained map from its original orbit-fibre interface. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The original multiplication convention also supplies the reverse convention
because the specified character quotient embeds in a cyclic group. -/
theorem s4_q3_action_reverse_mul (S : g32p_Supplier)
    (Y : Over (Spec ↧ℂ)) (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (hamul : ∀ u v, a (u * v) = a u ≫ a v) :
    ∀ u v, a (u * v) = a v ≫ a u := by
  intro u v
  have hcomm : u * v = v * u := e.injective (by
    rw [map_mul, map_mul, mul_comm])
  rw [hcomm, hamul]

/-- The retained surjection is open on complex points using only its original
orbit fibres and invariant coordinate maps. -/
theorem s4_q3_retained_pointMap_isOpenMap (S : g32p_Supplier)
    (Y : Over (Spec ↧ℂ)) (N : ℕ)
    [IsIntegral (g3_power Y N).left] [Smooth (g3_power Y N).hom]
    [IsProjective (g3_power Y N).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y N ⟶ W)
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)),
      (∑ i, v i) = 0 → s2_action S Y a e N v σ ≫ q = q)
    (hqfib : ∀ x y : ComplexPoint (g3_power Y N),
      Point.map q x = Point.map q y →
        ∃ (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)),
          (∑ i, v i) = 0 ∧ Point.map (s2_action S Y a e N v σ) x = y) :
    IsOpenMap (Point.map q) := by
  let I := {v : Fin N → ZMod S.m // (∑ i, v i) = 0} × Equiv.Perm (Fin N)
  let A : I → (ComplexPoint (g3_power Y N) ≃ₜ ComplexPoint (g3_power Y N)) :=
    fun t => s2e_pointHomeomorphOfIso
      (s2_coordinateActionIso S Y a e ha1 (s4_q3_action_reverse_mul S Y a e hamul)
        N t.1.1 t.2)
  apply s2e_orbit_quotient_isOpenMap I A (Point.map q)
    (Topology.IsQuotientMap.of_surjective_continuous hqsurj (Point.continuous_map q))
  · intro t x
    change Point.map q (Point.map (s2_action S Y a e N t.1.1 t.2) x) = Point.map q x
    rw [← Point.map_comp_apply, hqinv _ _ t.1.2]
  · intro x y hxy
    obtain ⟨v, σ, hv, hxy⟩ := hqfib x y hxy
    exact ⟨(⟨v, hv⟩, σ), hxy⟩

end HodgeLean.Foundations.Program
