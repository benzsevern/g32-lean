import HodgeLean.Foundations.Program.SchoenProperActionQuotient
import HodgeLean.Foundations.Program.SchoenSumZeroActionFinite
import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Foundations.SegreProjective

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The prescribed zero-sum and permutation action has an actual finite proper quotient, including its retained complex-point fibres and categorical property. -/
theorem s2_sumZero_normalProperQuotient (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (h : ℕ) :
    ∃ (W : Over (Spec ↧ℂ)) (q : g3_power Y h ⟶ W),
      IsIntegral W.left ∧ IsProper W.hom ∧ zmtiso_IsNormal W.left ∧ IsFinite q.left ∧
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
  letI : Finite G := s2_sumZeroActionGroup_finite S Y a e ha1 hamul h
  let ρ : G →* Aut (g3_power Y h) := G.subtype
  let gOf (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h))
      (hv : ∑ i, v i = 0) : G :=
    ⟨Aut.of (s2_coordinateActionIso S Y a e ha1 hamul h v σ), v, σ, hv, rfl⟩
  obtain ⟨W, q, hW, hproper, hfinite, hsurj, hinv, horbit, hdesc, hnormal⟩ :=
    s2_finiteAction_properQuotient (g3_power Y h) G ρ
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

end HodgeLean.Foundations.Program
