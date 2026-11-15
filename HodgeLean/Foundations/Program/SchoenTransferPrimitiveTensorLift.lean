import HodgeLean.Foundations.Program.SchoenTransferPrimitiveBaseChange
import HodgeLean.Foundations.Program.SchoenTransferCurveTensorActions
import HodgeLean.Foundations.Program.SchoenTransferEqualCoordinateOperators
import HodgeLean.Foundations.Program.SchoenTransferPolynomialIntertwining

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Polynomial
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

variable (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) (hh : 0 < h)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)

include hdim ha1 hamul in
/-- Every primitive invariant class has a preimage in the actual complex tensor carrier.
Source: Schoen (1988), Lemma 1.1, p. 5; scalar extension of the ordered Künneth map. -/
theorem s4_primitive_complex_tensor_preimage
    {z : ℂ ⊗[ℚ] HQ (g3_power Y h) h}
    (hz : z ∈ (s4_invariantPrimitive S Y a e h hh).baseChange ℂ) :
    ∃ y, s4_complexOneCup Y h y = z := by
  letI := (finbetti_finiteBetti Y).finite 1
  obtain ⟨w, hw⟩ := s4_primitive_baseChange_oneCup_range S Y h hh a e hdim ha1 hamul hz
  refine ⟨s4_tensorBaseChangeEquiv (L := ℂ) (I := Fin h) (Module.finBasis ℚ (HQ Y 1)) w, ?_⟩
  exact (LinearMap.congr_fun (s4_complexOneCup_scalarExtension Y h
    (Module.finBasis ℚ (HQ Y 1))) w).trans hw

include hdim ha1 hamul in
/-- A primitive invariant tensor preimage has equal coordinate actions and the alternating law.
Source: Schoen (1988), Lemmas 1.1–1.2, pp. 5–6. -/
theorem s4_primitive_complex_tensor_equations
    {y : ⨂[ℂ] i : Fin h, ℂ ⊗[ℚ] HQ Y 1}
    (hy : s4_complexOneCup Y h y ∈ (s4_invariantPrimitive S Y a e h hh).baseChange ℂ) :
    (∀ i j : Fin h,
      s4_tensorCoordinate ((homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ) i y =
      s4_tensorCoordinate ((homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ) j y) ∧
    (∀ σ : Equiv.Perm (Fin h), s4_tensorPermutation h σ y = σ.sign • y) := by
  let ρ := (Module.End.baseChangeHom ℚ ℂ (HQ (g3_power Y h) h)).toMonoidHom.comp
    (s4_e1_deckPullbackRepresentation S Y a e ha1 hamul h h)
  have hfixed (v : Fin h → ZMod S.m) (hv : ∑ i, v i = 0) :
      ρ (.ofAdd v) (s4_complexOneCup Y h y) = s4_complexOneCup Y h y :=
    s4_primitive_baseChange_action_fixed S Y h hh a e hy v hv 1
  have hi := s4_complexOneCup_injective Y hdim h
  constructor
  · intro i j
    apply hi
    have he := s4_equal_coordinate_operators (1 : ZMod S.m) ρ
      (s4_complexOneCup Y h y) hfixed i j
    change (homPullback (s2_action S Y a e h (Pi.single i 1) 1) h).baseChange ℂ
      (s4_complexOneCup Y h y) =
      (homPullback (s2_action S Y a e h (Pi.single j 1) 1) h).baseChange ℂ
        (s4_complexOneCup Y h y) at he
    change ((homPullback (s2_action S Y a e h (Pi.single i 1) 1) h).baseChange ℂ ∘ₗ
      s4_complexOneCup Y h) y =
      ((homPullback (s2_action S Y a e h (Pi.single j 1) 1) h).baseChange ℂ ∘ₗ
        s4_complexOneCup Y h) y at he
    rw [s4_curve_tensor_coordinate_action S Y a e ha1 h i,
      s4_curve_tensor_coordinate_action S Y a e ha1 h j] at he
    exact he
  · intro σ
    apply hi
    have hp := s4_primitive_baseChange_action_fixed S Y h hh a e hy 0 (by simp) σ
    rw [s4_zero_deck_permutation S Y a e ha1 h σ] at hp
    have hc := LinearMap.congr_fun (s4_complexOneCup_permutation_action Y h σ) y
    simp only [LinearMap.comp_apply, s4_linearMap_unit_apply] at hc
    have hs := congrArg (fun w => σ.sign • w) (hc.symm.trans hp)
    simp only [smul_smul, Int.units_mul_self, one_smul] at hs
    simpa only [Units.smul_def, map_zsmul] using hs

include hdim ha1 hamul in
/-- The residual polynomial equation transports to a coordinate of the complex tensor preimage.
Source: Schoen (1988), Lemma 1.1, p. 5; polynomial naturality. -/
theorem s4_primitive_complex_tensor_polynomial
    {y : ⨂[ℂ] i : Fin h, ℂ ⊗[ℚ] HQ Y 1}
    (hy : s4_complexOneCup Y h y ∈ (s4_invariantPrimitive S Y a e h hh).baseChange ℂ) :
    Polynomial.aeval
      (s4_tensorCoordinate ((homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ)
        (⟨0, hh⟩ : Fin h))
      ((Polynomial.cyclotomic S.m ℚ).map (algebraMap ℚ ℂ)) y = 0 := by
  have hi := s4_complexOneCup_injective Y hdim h
  have hp := s4_primitive_baseChange_polynomial_zero S Y h hh a e hy
  have hd : s2_delta S h hh 1 = Pi.single (⟨0, hh⟩ : Fin h) 1 := by
    ext i
    simp only [s2_delta, Pi.single_apply]
  rw [baseChange_aeval, hd] at hp
  apply hi
  rw [map_zero, s4_polynomial_intertwines (s4_complexOneCup Y h) _
    ((homPullback (s2_action S Y a e h (Pi.single (⟨0, hh⟩ : Fin h) 1) 1) h).baseChange ℂ)
    (fun x => (LinearMap.congr_fun (s4_curve_tensor_coordinate_action S Y a e ha1 h
      (⟨0, hh⟩ : Fin h)) x).symm)]
  exact hp

end HodgeLean.Foundations.Program
