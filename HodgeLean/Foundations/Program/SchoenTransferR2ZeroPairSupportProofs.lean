import HodgeLean.Foundations.Program.SchoenTransferR2Checks
import HodgeLean.Foundations.WitnessSelection.ReselectionProofs

/-! # S4 retained geometric transfer statements

Implications from the explicit native supplier, tower and S2 witnesses.
The five B21 projections retain their types. The additional slice/basis and
zero-pair retention statements expose the dependent transport that the
stage-two witness-selection library must supply.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option maxRecDepth 1000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program
open HodgeLean.WitnessSelection

/-- Contract R2.4: retained native geometry and its literal maps.
Source: Schoen (1988), Lemmas 2.3–2.6 and Theorem 2.0, pp. 13–18;
docs/notes/native-inputs/s4-chain-contract.md, R2 row 4.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_zero_pair_support_aux
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (T : Type*) [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : Fin (0 : ℕ) → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = marks i)
    (h : ℕ) (hh : 0 < h + 1)
    (q : g3_power Y (h + 1) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q = q)
    (hq : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ A),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W ⟶ A, q ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ A),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ A, γ ≫ u = f)
    (β : W ⟶ B) [IsFinite β.left] (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β) (horder : End.of d ^ S.m = 1)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)
:
    Etale β.left ∧ Smooth W.hom := by
  obtain ⟨het, hsm⟩ := HodgeLean.WitnessSelection.initial_cover_smooth_open
    S Y Z W B a e ha1 hamul hinj p hp hpsurj hporbit T (Fin 0) eY hpointAction
    marks hbranch h hh q hqsurj hqinv hq γ hγsurj hγinv hγ β hβ d hd horder
    hgenerator ⊤ (fun i => Fin.elim0 i)
  haveI : Etale (β.left ∣_ (⊤ : B.left.Opens)) := het
  haveI : IsIso (β.left ⁻¹ᵁ (⊤ : B.left.Opens)).ι := by
    simp only [TopologicalSpace.Opens.map_top]
    rw [← Scheme.topIso_hom]
    infer_instance
  have he : Etale ((β.left ⁻¹ᵁ (⊤ : B.left.Opens)).ι ≫ β.left) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso (@Etale) _ _).mp he,
    (MorphismProperty.cancel_left_of_respectsIso (@Smooth) _ _).mp hsm⟩

example := HodgeLean.Foundations.Program.R2Checks.s4_chain_ramified_zero_pair_support_example

open scoped TensorProduct


end HodgeLean.Foundations.Program
