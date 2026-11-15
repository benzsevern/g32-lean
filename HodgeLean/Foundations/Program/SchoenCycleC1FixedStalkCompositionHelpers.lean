import HodgeLean.Foundations.Program.SchoenCycleC1ActualLocalActionHelpers

/-! # Composition of the actual fixed-point stalk actions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Fixed-point stalk pullback under an actual scheme identity is the
identity of the specified stalk. -/
theorem s2e_c1_fixed_stalk_pullback_id
    (X : Scheme) (p : X) :
    s2e_fixed_point_stalkPullback X (𝟙 X) p (by simp) = RingHom.id _ := by
  exact (Scheme.FixedPointStalk.pullback_laws X p).1

/-- Actual fixed-point stalk pullbacks retain contravariant composition,
with the point transports compared through the actual rational function field. -/
theorem s2e_c1_fixed_stalk_pullback_comp
    (X : Scheme) [IsIntegral X] (u v : X ⟶ X) [IsIso u] [IsIso v]
    (p : X) (hu : u p = p) (hv : v p = p) :
    s2e_fixed_point_stalkPullback X (u ≫ v) p (by change v (u p) = p; rw [hu, hv]) =
      (s2e_fixed_point_stalkPullback X u p hu).comp
        (s2e_fixed_point_stalkPullback X v p hv) := by
  exact (Scheme.FixedPointStalk.pullback_laws X p).2 u v hu hv

end HodgeLean.Foundations.Program
