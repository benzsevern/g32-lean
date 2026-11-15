import HodgeLean.Foundations.QuotientDuality.PersistenceWeights
import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence
import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers
import Mathlib.CategoryTheory.Conj

/-! The eigenvalue of the literal weighted inverse-deck expression. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
open scoped TensorProduct
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_weighted_tensor_inverse
    {V : Type} [AddCommGroup V] [Module ℚ V] (T : Module.End ℚ V)
    (m : ℕ) [NeZero m] (hT : T ^ m = 1) (ζ : ℂ) (hζ : ζ ^ m = 1) (c : V) :
    let v := s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
      (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ) ((T ^ (m - t.val)) c))
    ζ • T.baseChange ℂ v = v := by
  have hp : T.baseChange ℂ ^ m = 1 := by
    rw [← LinearMap.baseChange_pow, hT, LinearMap.baseChange_one]
  have h := persistence_inverse_weight_sum (T.baseChange ℂ) m hp ζ hζ
    (TensorProduct.tmul ℚ (1 : ℂ) c)
  simpa only [s2e_weightedSum, ← LinearMap.baseChange_pow, LinearMap.baseChange_tmul] using h

lemma persistence_scheme_pullback_comp (R : Type) [CommRing R]
    {X Y Z : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    s2e_pullback R (f ≫ g) n = (s2e_pullback R f n).comp (s2e_pullback R g n) := by
  change cohomologyMap R n
    ((TopCat.ofHom (Point.continuousMap f)) ≫ (TopCat.ofHom (Point.continuousMap g))) = _
  exact cohomologyMap_comp R n _ _

lemma persistence_scheme_pullback_power (R : Type) [CommRing R]
    (W : Over (Spec ↧ℂ)) (d : W ⟶ W) (n m : ℕ) :
    s2e_pullback R ((End.of d ^ m).asHom) n = (s2e_pullback R d n) ^ m := by
  induction m with
  | zero => exact cohomologyMap_id R _ n
  | succ m ih =>
    rw [pow_succ]
    change s2e_pullback R (d ≫ (End.of d ^ m).asHom) n = _
    rw [persistence_scheme_pullback_comp, ih, pow_succ']
    rfl

lemma persistence_weighted_deck_inverse
    (W : Over (Spec ↧ℂ)) (d : W ⟶ W) (m : ℕ) [NeZero m]
    (hd : End.of d ^ m = 1) (n : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (cl : Cohomology ℚ (TopCat.of (ComplexPoint W)) n) :
    let v := s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
      (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
        (s2e_pullback ℚ ((End.of d ^ (m - t.val)).asHom) n cl))
    ζ • (s2e_pullback ℚ d n).baseChange ℂ v = v := by
  have hp : (s2e_pullback ℚ d n) ^ m = 1 := by
    rw [← persistence_scheme_pullback_power, hd]
    exact cohomologyMap_id ℚ _ n
  simp_rw [persistence_scheme_pullback_power]
  exact persistence_weighted_tensor_inverse (s2e_pullback ℚ d n) m hp ζ hζ.pow_eq_one cl

lemma persistence_weighted_deck_no_forward_lift
    {X W : Over (Spec ↧ℂ)} (d₀ : X ⟶ X) (d : W ⟶ W) (f : W ⟶ X)
    (hf : d ≫ f = f ≫ d₀) (m : ℕ) [NeZero m] (hm : 3 ≤ m)
    (hd : End.of d ^ m = 1) (n : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (cl : Cohomology ℚ (TopCat.of (ComplexPoint W)) n)
    (hnonzero : s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
      (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
        (s2e_pullback ℚ ((End.of d ^ (m - t.val)).asHom) n cl)) ≠ 0) :
    let v := s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
      (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
        (s2e_pullback ℚ ((End.of d ^ (m - t.val)).asHom) n cl))
    ¬ ∃ u : ℂ ⊗[ℚ] Cohomology ℚ (TopCat.of (ComplexPoint X)) n,
      (s2e_pullback ℚ d₀ n).baseChange ℂ u = ζ • u ∧
      (s2e_pullback ℚ f n).baseChange ℂ u = v := by
  apply persistence_opposite_eigen_no_preimage
    ((s2e_pullback ℚ d₀ n).baseChange ℂ) ((s2e_pullback ℚ d n).baseChange ℂ)
    ((s2e_pullback ℚ f n).baseChange ℂ) ?_ m hm ζ hζ _ hnonzero
    (persistence_weighted_deck_inverse W d m hd n ζ hζ cl)
  intro u
  have h := congrArg (fun t => (s2e_pullback ℚ t n).baseChange ℂ) hf
  simp only [persistence_scheme_pullback_comp, LinearMap.baseChange_comp] at h
  exact LinearMap.congr_fun h u

lemma persistence_tower_weighted_no_forward_lift
    {r : ℕ} (V : Fin (r + 1) → Over (Spec ↧ℂ)) (X W : Over (Spec ↧ℂ))
    (e₀ : V 0 ⟶ X) (w : ∀ i : Fin r, V i.succ ⟶ V i.castSucc)
    (d : ∀ i, V i ⟶ V i) (d₀ : X ⟶ X)
    (h₀ : d 0 ≫ e₀ = e₀ ≫ d₀)
    (hw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (e : V (Fin.last r) ≅ W) (m : ℕ) [NeZero m] (hm : 3 ≤ m)
    (hd : End.of (d (Fin.last r)) ^ m = 1)
    (n : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (cl : Cohomology ℚ (TopCat.of (ComplexPoint W)) n)
    (hnonzero : let δ := e.inv ≫ d (Fin.last r) ≫ e.hom
      s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
        (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
          (s2e_pullback ℚ ((End.of δ ^ (m - t.val)).asHom) n cl)) ≠ 0) :
    let δ := e.inv ≫ d (Fin.last r) ≫ e.hom
    let v := s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
      (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
        (s2e_pullback ℚ ((End.of δ ^ (m - t.val)).asHom) n cl))
    let φ := e.inv ≫ s2e_towerTotalMap V e₀ w (Fin.last r)
    ¬ ∃ u : ℂ ⊗[ℚ] Cohomology ℚ (TopCat.of (ComplexPoint X)) n,
      (s2e_pullback ℚ d₀ n).baseChange ℂ u = ζ • u ∧
      (s2e_pullback ℚ φ n).baseChange ℂ u = v := by
  have hδ : End.of (e.inv ≫ d (Fin.last r) ≫ e.hom) ^ m = 1 := by
    have h := congrArg e.conj hd
    rw [map_pow, map_one] at h
    exact h
  have hφ : (e.inv ≫ d (Fin.last r) ≫ e.hom) ≫
      (e.inv ≫ s2e_towerTotalMap V e₀ w (Fin.last r)) =
      (e.inv ≫ s2e_towerTotalMap V e₀ w (Fin.last r)) ≫ d₀ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [s2e_towerTotalMap_equivariant V e₀ w d d₀ h₀ hw]
  exact persistence_weighted_deck_no_forward_lift d₀ _ _ hφ m hm hδ n ζ hζ cl hnonzero

end HodgeLean.Foundations.QuotientDuality
