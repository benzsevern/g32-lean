import HodgeLean.Foundations.Program.SchoenTransferE1
import HodgeLean.Foundations.Program.SchoenTransferSubmoduleBaseChange
import HodgeLean.Foundations.Program.SchoenTransferBaseChangeRange

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

variable (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (hh : 0 < h)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))

/-- Every retained deck-permutation equation holds on the scalar-extended primitive subspace.
Source: Schoen (1988), Lemmas 1.1–1.2, pp. 5–6; extension of scalars. -/
theorem s4_primitive_baseChange_action_fixed
    {z : ℂ ⊗[ℚ] HQ (g3_power Y h) h}
    (hz : z ∈ (s4_invariantPrimitive S Y a e h hh).baseChange ℂ)
    (v : Fin h → ZMod S.m) (hv : ∑ i, v i = 0) (σ : Equiv.Perm (Fin h)) :
    (homPullback (s2_action S Y a e h v σ) h).baseChange ℂ z = z := by
  apply s4_baseChange_fixed (s4_invariantPrimitive S Y a e h hh) _ _ hz
  intro x hx
  have hk := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx.2 ⟨v, hv⟩) σ
  change homPullback (s2_action S Y a e h v σ) h x - x = 0 at hk
  exact sub_eq_zero.mp hk

/-- The literal residual cyclotomic polynomial annihilates the scalar-extended primitive subspace.
Source: Schoen (1988), Lemma 1.1, p. 5; extension of scalars. -/
theorem s4_primitive_baseChange_polynomial_zero
    {z : ℂ ⊗[ℚ] HQ (g3_power Y h) h}
    (hz : z ∈ (s4_invariantPrimitive S Y a e h hh).baseChange ℂ) :
    (Polynomial.aeval
      (homPullback (s2_action S Y a e h (s2_delta S h hh 1) 1) h)
      (Polynomial.cyclotomic S.m ℚ)).baseChange ℂ z = 0 := by
  apply s4_baseChange_annihilates (s4_invariantPrimitive S Y a e h hh) _ _ hz
  intro x hx
  exact hx.1

/-- Every scalar-extended primitive invariant class has an actual all-degree-one tensor preimage.
Source: Schoen (1988), Lemma 1.1, p. 5; the checked curve-power Künneth identification. -/
theorem s4_primitive_baseChange_oneCup_range
    (hdim : TopologicalSpace.dim Y.left = 1)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    {z : ℂ ⊗[ℚ] HQ (g3_power Y h) h}
    (hz : z ∈ (s4_invariantPrimitive S Y a e h hh).baseChange ℂ) :
    z ∈ LinearMap.range ((s4_e1_oneCup Y h).baseChange ℂ) := by
  rw [s4_baseChange_range]
  exact s4_baseChange_le (L := ℂ)
    (s4_e1_primitive_degree_one S Y hdim h hh a e ha1 hamul) hz

end HodgeLean.Foundations.Program
