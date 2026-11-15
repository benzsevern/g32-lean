import HodgeLean.Foundations.Program.SchoenTransferE1CurveAction

/-! Coordinate pullbacks on the actual recursively ordered tensor spaces. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Tensor the specified coordinate pullbacks in their recursive order.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the external cup product. -/
def s4_e1_tensorPullback
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    (h : ℕ) → (d : Fin h → ℕ) → (Fin h → (Y ⟶ Y)) →
      Module.End ℚ (s4_e1_tensor Y h d)
  | 0, _, _ => LinearMap.id
  | h + 1, d, b => TensorProduct.map (homPullback (b 0) (d 0))
      (s4_e1_tensorPullback Y h (Fin.tail d) (Fin.tail b))

/-- Tensoring identity coordinate operators gives the identity operator.
Source: functoriality of tensor products. -/
theorem s4_e1_tensorPullback_of_identity
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (d : Fin h → ℕ) (b : Fin h → (Y ⟶ Y))
    (hb : ∀ i, homPullback (b i) (d i) = LinearMap.id) :
    s4_e1_tensorPullback Y h d b = LinearMap.id := by
  induction h with
  | zero => rfl
  | succ h ih =>
      change TensorProduct.map (homPullback (b 0) (d 0))
        (s4_e1_tensorPullback Y h (Fin.tail d) (Fin.tail b)) = _
      rw [hb 0, ih (Fin.tail d) (Fin.tail b) (fun i => hb i.succ)]
      exact TensorProduct.map_id

/-- Coordinate maps supported on degree-zero factors act identically on the
ordered multidegree tensor.
Source: Hatcher, Algebraic Topology, §3.2; constants in degree zero. -/
theorem s4_e1_tensorPullback_degree_zero_support
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (d : Fin h → ℕ) (b : Fin h → (Y ⟶ Y))
    (hb : ∀ i, d i ≠ 0 → b i = 𝟙 Y) :
    s4_e1_tensorPullback Y h d b = LinearMap.id := by
  apply s4_e1_tensorPullback_of_identity
  intro i
  by_cases hd : d i = 0
  · rw [hd]
    exact s4_e1_degree_zero_action Y (b i)
  · rw [hb i hd, spec_homPullback_id]

set_option backward.isDefEq.respectTransparency false in
/-- Applying the coordinate operators inside the tensor gives the actual ordered
cup with those coordinate maps composed on the right.
Source: Hatcher, Algebraic Topology, §3.2, cup naturality and multilinearity. -/
theorem s4_e1_orderedCup_tensorPullback
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (h : ℕ) (d : Fin h → ℕ) (f : Fin h → (T ⟶ Y)) (b : Fin h → (Y ⟶ Y)) :
    s4_e1_orderedCup Y T h d (fun i => f i ≫ b i) =
      (s4_e1_orderedCup Y T h d f).comp (s4_e1_tensorPullback Y h d b) := by
  induction h with
  | zero => rfl
  | succ h ih =>
      apply TensorProduct.ext'
      intro x y
      simp only [s4_e1_orderedCup, s4_e1_tensorPullback, s4_e1_tensor, ModuleCat.of,
        LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul,
        LinearMap.compl₁₂_apply, spec_homPullback_comp]
      have ht := LinearMap.congr_fun (ih (Fin.tail d) (Fin.tail f) (Fin.tail b)) y
      simp only [LinearMap.comp_apply] at ht
      erw [ht]

set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback preserves ordered cups on any smooth projective source.
Source: Hatcher, Algebraic Topology, §3.2, naturality of cup products. -/
theorem s4_e1_orderedCup_pullback
    (Y T U : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    [IsIntegral U.left] [Smooth U.hom] [IsProjective U.hom]
    (u : U ⟶ T) (h : ℕ) (d : Fin h → ℕ) (f : Fin h → (T ⟶ Y)) :
    (homPullback u (∑ i, d i)).comp (s4_e1_orderedCup Y T h d f) =
      s4_e1_orderedCup Y U h d (fun i => u ≫ f i) := by
  induction h with
  | zero =>
      change (homPullback u 0).comp
        (LinearMap.toSpanSingleton ℚ (HQ T 0) (cupUnit T)) =
        LinearMap.toSpanSingleton ℚ (HQ U 0) (cupUnit U)
      apply LinearMap.ext
      intro q
      change homPullback u 0 (q • cupUnit T) = q • cupUnit U
      rw [map_smul, spec_homPullback_unit]
  | succ h ih =>
      dsimp only [s4_e1_tensor]
      simp only [s4_e1_orderedCup]
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change homPullback u _ ((cupProductOf T).cup _
        (homPullback (f 0) _ x) (s4_e1_orderedCup Y T h _ _ y)) = _
      rw [spec_homPullback_cup]
      have ht := LinearMap.congr_fun (ih (Fin.tail d) (Fin.tail f)) y
      simp only [LinearMap.comp_apply] at ht
      rw [ht]
      simp only [spec_homPullback_comp, LinearMap.comp_apply]
      rfl

/-- The actual coordinate square intertwines geometric pullback with the
ordered tensor coordinate operators.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the external cup product. -/
theorem s4_e1_orderedCup_coordinate_tensor
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (u : T ⟶ T) (h : ℕ) (d : Fin h → ℕ)
    (f : Fin h → (T ⟶ Y)) (b : Fin h → (Y ⟶ Y))
    (hu : ∀ i, u ≫ f i = f i ≫ b i) :
    (homPullback u (∑ i, d i)).comp (s4_e1_orderedCup Y T h d f) =
      (s4_e1_orderedCup Y T h d f).comp (s4_e1_tensorPullback Y h d b) := by
  rw [s4_e1_orderedCup_pullback]
  simp only [hu]
  exact s4_e1_orderedCup_tensorPullback Y T h d f b

/-- Coordinate maps supported on degree-zero factors fix the actual ordered cup image.
Source: Hatcher, Algebraic Topology, §3.2, constants and naturality of cup products. -/
theorem s4_e1_orderedCup_degree_zero_support
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (u : T ⟶ T) (h : ℕ) (d : Fin h → ℕ)
    (f : Fin h → (T ⟶ Y)) (b : Fin h → (Y ⟶ Y))
    (hu : ∀ i, u ≫ f i = f i ≫ b i)
    (hb : ∀ i, d i ≠ 0 → b i = 𝟙 Y) :
    (homPullback u (∑ i, d i)).comp (s4_e1_orderedCup Y T h d f) =
      s4_e1_orderedCup Y T h d f := by
  rw [s4_e1_orderedCup_coordinate_tensor Y T u h d f b hu,
    s4_e1_tensorPullback_degree_zero_support Y h d b hb, LinearMap.comp_id]

/-- Equal coordinate pullback operators give equal ordered tensor operators.
Source: functoriality of tensor products. -/
theorem s4_e1_tensorPullback_congr
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (d : Fin h → ℕ) (b c : Fin h → (Y ⟶ Y))
    (hb : ∀ i, homPullback (b i) (d i) = homPullback (c i) (d i)) :
    s4_e1_tensorPullback Y h d b = s4_e1_tensorPullback Y h d c := by
  induction h with
  | zero => rfl
  | succ h ih =>
      change TensorProduct.map (homPullback (b 0) (d 0))
        (s4_e1_tensorPullback Y h (Fin.tail d) (Fin.tail b)) =
        TensorProduct.map (homPullback (c 0) (d 0))
          (s4_e1_tensorPullback Y h (Fin.tail d) (Fin.tail c))
      rw [hb 0, ih (Fin.tail d) (Fin.tail b) (Fin.tail c) (fun i => hb i.succ)]

/-- The ordered tensor operator depends only on coordinate maps at positive-degree factors.
Source: Hatcher, Algebraic Topology, §3.2; constants in degree zero. -/
theorem s4_e1_tensorPullback_congr_active
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (d : Fin h → ℕ) (b c : Fin h → (Y ⟶ Y))
    (hb : ∀ i, d i ≠ 0 → b i = c i) :
    s4_e1_tensorPullback Y h d b = s4_e1_tensorPullback Y h d c := by
  apply s4_e1_tensorPullback_congr
  intro i
  by_cases hd : d i = 0
  · rw [hd, s4_e1_degree_zero_action Y (b i), s4_e1_degree_zero_action Y (c i)]
  · rw [hb i hd]

#print axioms s4_e1_tensorPullback_congr
#print axioms s4_e1_tensorPullback_congr_active
#print axioms s4_e1_orderedCup_coordinate_tensor
#print axioms s4_e1_orderedCup_degree_zero_support
#print axioms s4_e1_orderedCup_tensorPullback
#print axioms s4_e1_tensorPullback
#print axioms s4_e1_tensorPullback_of_identity
#print axioms s4_e1_tensorPullback_degree_zero_support
end HodgeLean.Foundations.Program
