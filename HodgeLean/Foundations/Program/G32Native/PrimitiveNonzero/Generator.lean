import HodgeLean.Foundations.Program.SchoenTowerI1bTranslations
import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers
import HodgeLean.Foundations.Curves.CubicGrpObj

/-! # Period of the specified residual generator -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero

/-- The delta translation gives the specified generator its degree period. -/
theorem generator_period
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral W.left] [IsProjective W.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (N : ℕ) (hN : 0 < N) (q : g3_power Y N ⟶ W)
    (hqsurj : Function.Surjective (Point.map q))
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e N (s2_delta S N hN 1) 1 ≫ q) :
    End.of d ^ S.m = 1 := by
  suffices he : (End.of d ^ S.m).asHom = 𝟙 W from congrArg End.of he
  apply HodgeLean.Foundations.Curves.complexPoint_hom_ext
  intro z
  obtain ⟨x, rfl⟩ := hqsurj z
  have hdelta : s2_delta S N hN (S.m : ZMod S.m) = 0 := by
    funext i
    simp only [ZMod.natCast_self, s2_delta, ite_self, Pi.zero_apply]
  have h := s2v_residual_generator_iterate S Y W a e ha1 hamul N hN q d hgenerator S.m x
  rw [s2e_c1_point_map_power, hdelta,
    (s2_coordinateAction_laws S Y a e ha1 hamul N).1] at h
  simpa only [Point.map, Category.comp_id] using h

#print axioms generator_period
end HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero
