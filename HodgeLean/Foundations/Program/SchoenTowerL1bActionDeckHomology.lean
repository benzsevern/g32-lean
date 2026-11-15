import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneRelative
import HodgeLean.Foundations.Program.SchoenTowerL1bActionWindingGenerator

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A logarithmic lift's deck coefficient computes the image of the
canonical one-turn homology class. -/
theorem s2v_l1b_action_deck_winding_class
    (H : C({z : ℂ // z ≠ 0}, {z : ℂ // z ≠ 0}))
    (L : ℂ → ℂ) (hL : Continuous L)
    (he : ∀ z : ℂ, Complex.exp (L z) =
      (H ⟨Complex.exp z, Complex.exp_ne_zero z⟩).val)
    (k : ℤ) (hk : ∀ z, L (z + 2 * Real.pi * Complex.I) =
      L z + (k : ℂ) * (2 * Real.pi * Complex.I)) :
    homologyMap ℤ 1 (TopCat.ofHom H)
      (((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
        (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1))) =
    k • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1)) := by
  let p := H.comp (s2v_l1b_action_windingCircleMap 0 1)
  let K : ℝ → ℂ := fun s => L ((s : ℂ) * (2 * Real.pi * Complex.I))
  have hK : Continuous K := hL.comp (Complex.continuous_ofReal.mul continuous_const)
  have hp (s : ℝ) : Complex.exp (K s) = (p (s : UnitAddCircle)).val := by
    rw [he]
    change (H ⟨Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I)), _⟩).val =
      (H (s2v_l1b_action_windingCircleMap 0 1 (s : UnitAddCircle))).val
    apply congrArg (fun a : {z : ℂ // z ≠ 0} => (H a).val)
    apply Subtype.ext
    simp only [s2v_l1b_action_windingCircleMap_coe, zero_add, Int.cast_one, one_mul]
  have hd (s : ℝ) : K (s + 1) = K s + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    change L (((s + 1 : ℝ) : ℂ) * _) = _
    rw [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul]
    exact hk _
  rw [b6m_homologyMap_loopCycle]
  exact PuncturedPlane.loopClass_of_lift p K hK hp k hd

/-- A punctured-plane map with a logarithmic lift acts on every integral
H₁ class by its deck coefficient. -/
theorem s2v_l1b_action_deck_homology
    (H : C({z : ℂ // z ≠ 0}, {z : ℂ // z ≠ 0}))
    (L : ℂ → ℂ) (hL : Continuous L)
    (he : ∀ z : ℂ, Complex.exp (L z) =
      (H ⟨Complex.exp z, Complex.exp_ne_zero z⟩).val)
    (k : ℤ) (hk : ∀ z, L (z + 2 * Real.pi * Complex.I) =
      L z + (k : ℂ) * (2 * Real.pi * Complex.I))
    (a : Homology ℤ (TopCat.of {z : ℂ // z ≠ 0}) 1) :
    homologyMap ℤ 1 (TopCat.ofHom H) a = k • a := by
  obtain ⟨n, rfl⟩ := s2v_l1b_action_winding_class_smul_surjective a
  rw [map_zsmul, s2v_l1b_action_deck_winding_class H L hL he k hk,
    smul_comm]

/-- The logarithmic deck coefficient of a plane point-complement pair map
is its coefficient on the integral local class. -/
theorem s2v_l1b_action_deck_local_sign
    (F : pointComplementPair (0 : ℂ) ⟶ pointComplementPair (0 : ℂ))
    (L : ℂ → ℂ) (hL : Continuous L)
    (he : ∀ z : ℂ, Complex.exp (L z) =
      (F.left ⟨Complex.exp z, Complex.exp_ne_zero z⟩).val)
    (k : ℤ) (hk : ∀ z, L (z + 2 * Real.pi * Complex.I) =
      L z + (k : ℂ) * (2 * Real.pi * Complex.I))
    (ε : ℤ) (horient : relativeHomologyMap ℤ 2 F (b6m_surfaceLocalClass ℤ (0 : ℂ)) =
      ε • b6m_surfaceLocalClass ℤ (0 : ℂ)) :
    k = ε := by
  let p := s2v_l1b_action_windingCircleMap 0 1
  let K : ℝ → ℂ := fun s => L ((s : ℂ) * (2 * Real.pi * Complex.I))
  apply PuncturedPlane.relativeDegree_of_lift (𝟙 _) F
    (by change Function.Injective (homologyMap ℤ 1 (𝟙 _))
        rw [homologyMap_id]
        exact Function.injective_id)
    p (by change homologyMap ℤ 1 (𝟙 _) _ = _
          rw [homologyMap_id]
          rfl)
    K (hL.comp (Complex.continuous_ofReal.mul continuous_const)) ?_ k ?_
    (b6m_surfaceLocalClass ℤ (0 : ℂ)) ?_ ε horient
  · intro s
    rw [he]
    apply congrArg (fun a : {z : ℂ // z ≠ 0} => (F.left a).val)
    apply Subtype.ext
    change Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I)) =
      (s2v_l1b_action_windingCircleMap 0 1 (s : UnitAddCircle)).val
    rw [s2v_l1b_action_windingCircleMap_coe, zero_add, Int.cast_one, one_mul]
  · intro s
    change L (((s + 1 : ℝ) : ℂ) * _) = _
    rw [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul]
    exact hk _
  · rw [relativeHomologyMap_id]
    rfl

end HodgeLean.Foundations.Program
