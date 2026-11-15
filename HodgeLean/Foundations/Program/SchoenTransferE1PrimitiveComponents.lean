import HodgeLean.Foundations.Program.SchoenTransferE1KunnethAction
import HodgeLean.Foundations.Program.SchoenTransferE1CoordinateAction
import HodgeLean.Foundations.Program.SchoenTransferE1PolynomialTransport
import HodgeLean.Foundations.Program.SchoenTransferE1DegreeSupport
import HodgeLean.Foundations.Program.SchoenTransferE1KunnethComponents

/-! Rational elimination of the other multidegrees in the actual primitive part. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An inverse Künneth component other than all degree one vanishes on the
supplied primitive invariant part.
Source: Schoen (1988), Lemma 1.1, p. 5; the sum-zero coordinate action. -/
theorem s4_e1_primitive_other_component_zero
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (hh : 0 < h)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (hK : Function.Bijective (s4_e1_kunneth Y h h))
    (d : {d : Fin h → ℕ // ∑ i, d i = h}) (hd : d.val ≠ fun _ => 1)
    (x : HQ (g3_power Y h) h) (hx : x ∈ s4_invariantPrimitive S Y a e h hh) :
    DirectSum.component ℚ _ _ d
      ((LinearEquiv.ofBijective (s4_e1_kunneth Y h h) hK).symm x) = 0 := by
  classical
  let E := LinearEquiv.ofBijective (s4_e1_kunneth Y h h) hK
  let p := (DirectSum.component ℚ _ (fun d : {d : Fin h → ℕ // ∑ i, d i = h} =>
    s4_e1_tensor Y h d.val) d).comp E.symm.toLinearMap
  let r := s2_delta S h hh 1
  let b (v : Fin h → ZMod S.m) (i : Fin h) := a (e.symm (.ofAdd (v i)))
  let u (v : Fin h → ZMod S.m) := s2_action S Y a e h v 1
  have hu (v : Fin h → ZMod S.m) (i : Fin h) :
      u v ≫ g3_proj Y h i = g3_proj Y h i ≫ b v i :=
    s4_e1_action_projection S Y a e h v 1 i
  have hpull (v : Fin h → ZMod S.m) (y : HQ (g3_power Y h) h) :
      p (homPullback (u v) h y) = s4_e1_tensorPullback Y h d.val (b v) (p y) :=
    s4_e1_kunneth_inverse_component Y h (u v) (b v) (hu v) h hK d y
  have hfixed (v : Fin h → ZMod S.m) (hv : ∑ i, v i = 0) :
      homPullback (u v) h x = x := by
    have hi := (Submodule.mem_iInf _).mp hx.2 ⟨v, hv⟩
    have hk := (Submodule.mem_iInf _).mp hi (1 : Equiv.Perm (Fin h))
    change homPullback (u v) h x - x = 0 at hk
    exact sub_eq_zero.mp hk
  obtain ⟨j, hj⟩ := (s4_e1_multidegree_one_or_zero h d.val d.property).resolve_left hd
  let v : Fin h → ZMod S.m := r - Pi.single j 1
  have hr : ∑ i, r i = 1 := by
    simp only [r, s2_delta]
    simp
  have hv : ∑ i, v i = 0 := by
    simp only [v, Pi.sub_apply, Finset.sum_sub_distrib, hr]
    simp
  have hbc : s4_e1_tensorPullback Y h d.val (b r) =
      s4_e1_tensorPullback Y h d.val (b v) := by
    apply s4_e1_tensorPullback_congr_active
    intro i hi
    have hij : i ≠ j := by
      intro he
      exact hi (he ▸ hj)
    have hvri : v i = r i := by simp [v, hij]
    simp only [b, hvri]
  have hres : s4_e1_tensorPullback Y h d.val (b r) (p x) = p x := by
    rw [hbc, ← hpull, hfixed v hv]
  exact s4_e1_fixed_primitive_component_eq_zero p
    (homPullback (u r) h) (s4_e1_tensorPullback Y h d.val (b r))
    (hpull r) S.m S.three_le x hres hx.1

/-- Bijectivity of the specified Künneth map gives the actual all-degree-one
image for the supplied primitive invariant part.
Source: Schoen (1988), Lemma 1.1, p. 5, and Lemma 1.2, pp. 5–6. -/
theorem s4_e1_primitive_degree_one_of_kunneth
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (hh : 0 < h)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (hK : Function.Bijective (s4_e1_kunneth Y h h)) :
    s4_invariantPrimitive S Y a e h hh ≤ LinearMap.range (s4_e1_oneCup Y h) := by
  classical
  intro x hx
  let I := {d : Fin h → ℕ // ∑ i, d i = h}
  let d0 : I := ⟨fun _ => 1, s4_e1_sum_one h⟩
  let E := LinearEquiv.ofBijective (s4_e1_kunneth Y h h) hK
  let z := E.symm x
  have hz : z = DirectSum.lof ℚ I _ d0 (DirectSum.component ℚ I _ d0 z) := by
    apply DirectSum.ext_component ℚ
    intro d
    by_cases hd : d = d0
    · subst d
      rw [DirectSum.component.lof_self]
    · have hdv : d.val ≠ fun _ => 1 := by
        intro he
        exact hd (Subtype.ext he)
      rw [s4_e1_primitive_other_component_zero S Y h hh a e hK d hdv x hx,
        DirectSum.component.of, dif_neg (Ne.symm hd)]
  refine ⟨s4_e1_oneTensorEquiv Y h (DirectSum.component ℚ I _ d0 z), ?_⟩
  rw [s4_e1_oneCup_kunneth_factor]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  change s4_e1_kunneth Y h h
    (DirectSum.lof ℚ I _ d0 (DirectSum.component ℚ I _ d0 z)) = x
  rw [← hz]
  exact E.apply_symm_apply x

#print axioms s4_e1_primitive_degree_one_of_kunneth
#print axioms s4_e1_primitive_other_component_zero
end HodgeLean.Foundations.Program
