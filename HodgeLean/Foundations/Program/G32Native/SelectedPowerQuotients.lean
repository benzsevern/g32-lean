import HodgeLean.Foundations.Program.SchoenTowerA2
import HodgeLean.Foundations.Program.SchoenProjectiveActionQuotient
import HodgeLean.Foundations.Program.SchoenSumZeroActionFinite
import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Foundations.SegreProjective

/-! Quotients for the retained selected curve action, without changing its coordinates.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The selected zero-sum action has a projective quotient with descent to every target.
Source: SchoenProjectiveActionQuotient.s2_finiteAction_projectiveQuotient;
SchoenSumZeroProperQuotient.s2_sumZero_normalProperQuotient.
-/
theorem g32n_selected_projective_power_quotient (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (h : ℕ) :
    ∃ (W : Over (Spec ↧ℂ)) (q : g3_power Y h ⟶ W),
      IsIntegral W.left ∧ IsProjective W.hom ∧ zmtiso_IsNormal W.left ∧ IsFinite q.left ∧
      Function.Surjective (Point.map q) ∧
      (∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
        ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ q = q) ∧
      (∀ x y : ComplexPoint (g3_power Y h), Point.map q x = Point.map q y ↔
        ∃ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
          ∑ i, v i = 0 ∧ Point.map (s2_action S Y a e h v σ) x = y) ∧
      (∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y h ⟶ T),
        (∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
          ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ f = f) →
        ∃! d : W ⟶ T, q ≫ d = f) := by
  letI := spec_g3b_geometricallyIntegral Y
  let G := s2_sumZeroActionGroup S Y a e ha1 hamul h
  let : Finite G := s2_sumZeroActionGroup_finite S Y a e ha1 hamul h
  let ρ : G →* Aut (g3_power Y h) := G.subtype
  let gOf (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h))
      (hv : ∑ i, v i = 0) : G :=
    ⟨Aut.of (s2_coordinateActionIso S Y a e ha1 hamul h v σ), v, σ, hv, rfl⟩
  obtain ⟨W, q, hW, hproper, hfinite, hsurj, hinv, horbit, hdesc, hnormal⟩ :=
    s2_finiteAction_projectiveQuotient (g3_power Y h) G ρ
  refine ⟨W, q, hW, hproper, (hnormal inferInstance), hfinite, hsurj, ?_, ?_, ?_⟩
  · intro v σ hv
    exact hinv (gOf v σ hv)
  · intro x y
    constructor
    · intro hxy
      obtain ⟨g, hg⟩ := (horbit x y).mp hxy
      obtain ⟨v, σ, hv, hrep⟩ := g.property
      refine ⟨v, σ, hv, ?_⟩
      change Point.map g.val.asIso.hom x = y at hg
      rw [hrep] at hg
      exact hg
    · rintro ⟨v, σ, hv, hxy⟩
      exact (horbit x y).mpr ⟨gOf v σ hv, hxy⟩
  · intro T f hf
    apply hdesc T f
    intro g
    obtain ⟨v, σ, hv, hrep⟩ := g.property
    change g.val.asIso.hom ≫ f = f
    rw [hrep]
    exact hf v σ hv

#print axioms g32n_selected_projective_power_quotient


/-- The two quotient outputs in the native telescope for the supplied curves and degree.
Source: SchoenTransferJ2NativeInput.lean:42–51,93–110;
SchoenTowerA2.s2_symmetric_power; g32n_selected_projective_power_quotient.
HC no distance; AV milestone no distance.
-/
theorem g32n_selected_power_quotients (S : g32p_Supplier)
    (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) :
∃ (W₀ B₀ : Over (Spec ↧ℂ)),
∃ inst7 : IsIntegral W₀.left,
    let := inst7
∃ inst8 : IsProjective W₀.hom,
    let := inst8
∃ inst9 : IsIntegral B₀.left,
    let := inst9
∃ inst10 : Smooth B₀.hom,
    let := inst10
∃ inst11 : IsProjective B₀.hom,
    let := inst11
∃ (q₀ : g3_power Y (h + 1) ⟶ W₀),
∃ inst17 : IsFinite q₀.left,
    let := inst17
∃ (hqsurj : Function.Surjective (Point.map q₀)),
∃ (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀),
∃ (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f),
∃ (γ : g3_power Z (h + 1) ⟶ B₀),
∃ inst18 : IsFinite γ.left,
    let := inst18
∃ (hγsurj : Function.Surjective (Point.map γ)),
∃ (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ),
(∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f) := by
  obtain ⟨W, q, hWi, hWp, _, hqf, hqs, hqi, _, hqd⟩ :=
    g32n_selected_projective_power_quotient S Y a e ha1 hamul (h + 1)
  obtain ⟨B, γ, hBi, hBs, hBp, _, hγf, hγs, hγi, _, hγd⟩ :=
    s2_symmetric_power Z hdimZ (h + 1)
  exact ⟨W, B, hWi, hWp, hBi, hBs, hBp, q, hqf, hqs, hqi, hqd,
    γ, hγf, hγs, hγi, hγd⟩

#print axioms g32n_selected_power_quotients

end HodgeLean.Foundations.Program
