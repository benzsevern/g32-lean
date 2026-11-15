import HodgeLean.Foundations.Program.SchoenTransferE1TensorAction

/-! The actual coordinate action on the full multidegree direct sum. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Apply the ordered tensor coordinate pullback on every total-degree summand.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the Künneth map. -/
def s4_e1_multidegreePullback
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h n : ℕ) (b : Fin h → (Y ⟶ Y)) :
    Module.End ℚ (⨁ d : {d : Fin h → ℕ // ∑ i, d i = n}, s4_e1_tensor Y h d.val) :=
  DirectSum.lmap (fun d => s4_e1_tensorPullback Y h d.val b)

/-- The specified full Künneth map intertwines actual geometric coordinate
pullback with the direct sum of its actual tensor coordinate operators.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the external cup product. -/
theorem s4_e1_kunneth_coordinate_intertwines
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (u : g3_power Y h ⟶ g3_power Y h) (b : Fin h → (Y ⟶ Y))
    (hu : ∀ i, u ≫ g3_proj Y h i = g3_proj Y h i ≫ b i) (n : ℕ) :
    (homPullback u n).comp (s4_e1_kunneth Y h n) =
      (s4_e1_kunneth Y h n).comp (s4_e1_multidegreePullback Y h n b) := by
  apply DirectSum.linearMap_ext ℚ
  intro d
  rcases d with ⟨d, hd⟩
  subst n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, s4_e1_multidegreePullback,
    DirectSum.lmap_lof, s4_e1_kunneth, DirectSum.toModule_lof]
  change homPullback u (∑ i, d i)
    (s4_e1_orderedCup Y (g3_power Y h) h d (g3_proj Y h) x) =
    s4_e1_orderedCup Y (g3_power Y h) h d (g3_proj Y h)
      (s4_e1_tensorPullback Y h d b x)
  exact LinearMap.congr_fun
    (s4_e1_orderedCup_coordinate_tensor Y (g3_power Y h) u h d (g3_proj Y h) b hu) x

/-- Bijectivity transports coordinate equivariance to the inverse of the
specified Künneth comparison.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the Künneth comparison. -/
theorem s4_e1_kunneth_inverse_coordinate
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (u : g3_power Y h ⟶ g3_power Y h) (b : Fin h → (Y ⟶ Y))
    (hu : ∀ i, u ≫ g3_proj Y h i = g3_proj Y h i ≫ b i) (n : ℕ)
    (hK : Function.Bijective (s4_e1_kunneth Y h n)) (x : HQ (g3_power Y h) n) :
    (LinearEquiv.ofBijective (s4_e1_kunneth Y h n) hK).symm (homPullback u n x) =
      s4_e1_multidegreePullback Y h n b
        ((LinearEquiv.ofBijective (s4_e1_kunneth Y h n) hK).symm x) := by
  let E := LinearEquiv.ofBijective (s4_e1_kunneth Y h n) hK
  change E.symm (homPullback u n x) = s4_e1_multidegreePullback Y h n b (E.symm x)
  apply E.injective
  rw [E.apply_symm_apply]
  have he := LinearMap.congr_fun
    (s4_e1_kunneth_coordinate_intertwines Y h u b hu n) (E.symm x)
  change homPullback u n (E (E.symm x)) =
    E (s4_e1_multidegreePullback Y h n b (E.symm x)) at he
  rw [E.apply_symm_apply] at he
  exact he

/-- Each actual inverse Künneth component intertwines with its coordinate tensor operator.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the multidegree components. -/
theorem s4_e1_kunneth_inverse_component
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (u : g3_power Y h ⟶ g3_power Y h) (b : Fin h → (Y ⟶ Y))
    (hu : ∀ i, u ≫ g3_proj Y h i = g3_proj Y h i ≫ b i) (n : ℕ)
    (hK : Function.Bijective (s4_e1_kunneth Y h n))
    (d : {d : Fin h → ℕ // ∑ i, d i = n}) (x : HQ (g3_power Y h) n) :
    DirectSum.component ℚ _ _ d
      ((LinearEquiv.ofBijective (s4_e1_kunneth Y h n) hK).symm (homPullback u n x)) =
      s4_e1_tensorPullback Y h d.val b
        (DirectSum.component ℚ _ _ d
          ((LinearEquiv.ofBijective (s4_e1_kunneth Y h n) hK).symm x)) := by
  rw [s4_e1_kunneth_inverse_coordinate Y h u b hu n hK x]
  rfl

#print axioms s4_e1_kunneth_inverse_coordinate
#print axioms s4_e1_kunneth_inverse_component
#print axioms s4_e1_multidegreePullback
#print axioms s4_e1_kunneth_coordinate_intertwines
end HodgeLean.Foundations.Program
