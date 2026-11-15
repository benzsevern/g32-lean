import HodgeLean.Foundations.Program.G32Native.PrimitiveRank
import HodgeLean.Foundations.Program.SchoenTransferQ2cApplications

/-! # The literal singular primitive kernel on the retained quotient -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Program.G32Native.TowerOrbit
attribute [local irreducible] cupProductOf homPullback

/-- The actual quotient primitive middle-degree kernel has rank at most the cyclotomic degree. -/
theorem quotient_primitive_rank_bound
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (N k : ℕ) (hN : N = 2 * k) (hk : 0 < k) (hNpos : 0 < N)
    [IsIntegral (g3_power Y N).left] [Smooth (g3_power Y N).hom]
    [IsProjective (g3_power Y N).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (coords : V ≃ₗ[ℚ] (Fin (2 * k) → cyc_Field S.m))
    (F : V →ₗ[ℚ] HQ Y 1) (hf : Function.Injective F)
    (himage : LinearMap.range F = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (F v) =
        F (cyc_scalar coords (g32p_fieldValue S u) v))
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y N ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)),
      ∑ i, v i = 0 → s2_action S Y a e N v σ ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y N ⟶ T),
      (∀ (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)),
        ∑ i, v i = 0 → s2_action S Y a e N v σ ≫ f = f) →
      ∃! g : W ⟶ T, q ≫ g = f)
    (d : W ⟶ W)
    (hd : q ≫ d = s2_action S Y a e N (s2_delta S N hNpos 1) 1 ≫ q) :
    Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (s2e_pullback ℚ d (2 * k)) (Polynomial.cyclotomic S.m ℚ))) ≤
      Nat.totient S.m := by
  subst N
  have hmulf (u v : S.H ⧸ S.χ.ker) : a (u * v) = a u ≫ a v := by
    have hc : u * v = v * u := e.injective (by rw [map_mul, map_mul, mul_comm])
    rw [hc]
    exact hamul v u
  obtain ⟨_, _, hi, _⟩ := Q2.q2c_invariant_range_application S Y a e ha1 hamul
    (2 * k) W q hqsurj hqinv hquot (2 * k)
  let K := LinearMap.ker
    (Polynomial.aeval (s2e_pullback ℚ d (2 * k)) (Polynomial.cyclotomic S.m ℚ))
  let U := s4_invariantPrimitive S Y a e (2 * k) hNpos
  have hle : K.map (s4_quotientPullback q (2 * k)) ≤ U :=
    s4_quotient_primitive_image_le S Y (2 * k) hNpos a e W q hqinv d hd.symm
  letI : Module.Finite ℚ (HQ (g3_power Y (2 * k)) (2 * k)) :=
    (finbetti_finiteBetti (g3_power Y (2 * k))).finite (2 * k)
  calc
    Module.finrank ℚ K = Module.finrank ℚ (K.map (s4_quotientPullback q (2 * k))) :=
      (Submodule.equivMapOfInjective (s4_quotientPullback q (2 * k)) hi K).finrank_eq
    _ ≤ Module.finrank ℚ U := Submodule.finrank_mono hle
    _ ≤ Nat.totient S.m :=
      primitive_invariant_rank_bound S Y hdim k hk a e he ha1 hmulf coords F hf himage hscalar

#print axioms quotient_primitive_rank_bound
/-- The literal rational cohomology of the retained quotient is finite dimensional. -/
theorem quotient_cohomology_finite
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (N : ℕ) [IsIntegral (g3_power Y N).left] [Smooth (g3_power Y N).hom]
    [IsProjective (g3_power Y N).hom]
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y N ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)),
      ∑ i, v i = 0 → s2_action S Y a e N v σ ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y N ⟶ T),
      (∀ (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)),
        ∑ i, v i = 0 → s2_action S Y a e N v σ ≫ f = f) →
      ∃! g : W ⟶ T, q ≫ g = f) (n : ℕ) :
    Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) n) := by
  have hi := (Q2.q2c_invariant_range_application S Y a e ha1 hamul N W q hqsurj hqinv hquot n).2.2.1
  letI : Module.Finite ℚ (HQ (g3_power Y N) n) :=
    (finbetti_finiteBetti (g3_power Y N)).finite n
  exact Module.Finite.of_injective (s4_quotientPullback q n) hi

#print axioms quotient_cohomology_finite
end HodgeLean.Foundations.Program.G32Native.TowerOrbit
