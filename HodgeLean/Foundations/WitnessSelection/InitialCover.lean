import HodgeLean.Foundations.Program.SchoenCycleC1InitialUnmarkedEtale
import HodgeLean.Foundations.Program.SchoenTransferOrbitSupport
import HodgeLean.Foundations.Program.SchoenTransferSmooth

/-! # The original quotient cover on its unmarked open

Smoothness is established on the original cover before pushing any cycle.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.WitnessSelection

/-- The actual initial quotient is etale off its marked branch divisors and
its inverse image is smooth over the complex base.
Source: Schoen (1988), p. 15;
SchoenCycleC1InitialUnmarkedEtale.lean:18–65. -/
theorem initial_cover_smooth_open
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
    (T I : Type*) [Finite I] [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : I → ComplexPoint Z)
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
    (U : B.left.Opens)
    (hU : ∀ i, ∀ b ∈ U, b ∉ (s2c_branchIdeal Z B h γ (marks i)).support) :
    Etale (β.left ∣_ U) ∧ Smooth ((β.left ⁻¹ᵁ U).ι ≫ W.hom) := by
  haveI := s2e_c1_initial_etale_over_unmarked_open S Y Z W B a e ha1 hamul hinj
    p hp hpsurj hporbit T I eY hpointAction marks hbranch h hh q hqsurj hqinv hq
    γ hγsurj hγinv hγ β hβ d hd horder hgenerator U hU
  refine ⟨inferInstance, ?_⟩
  have heq : (β.left ⁻¹ᵁ U).ι ≫ W.hom = (β.left ∣_ U) ≫ U.ι ≫ B.hom := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, β.w]
  rw [heq]
  infer_instance

/-- Retained base and deck equations place every actual residual generic image,
and every surviving prime of its rational pushforward, in the original smooth open.
Source: Schoen (1988), Lemmas 2.5–2.6, p. 18; Fulton, §1.4;
SchoenTransferOrbitSupport.lean:11,25. -/
theorem residual_generic_smooth
    {Q W W₀ B : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth B.hom]
    (ι : Q ⟶ W) (d : W ⟶ W) (φ : W ⟶ W₀) [QuasiCompact φ.left]
    (β : W₀ ⟶ B) (κ : W ⟶ B) (hφ : φ ≫ β = κ) (hd : d ≫ κ = κ)
    (U : B.left.Opens) [Etale (β.left ∣_ U)]
    (hgeneric : κ.left (ι.left (genericPoint Q.left)) ∈ U)
    (m : ℕ) (a : Fin m → ℚ) :
    (∀ t : Fin m, φ.left ((ι ≫ (End.of d ^ t.val).asHom).left
      (genericPoint Q.left)) ∈ β.left ⁻¹ᵁ U) ∧
    (∀ x ∈ (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι d m a)).support,
      ∃ V : W₀.left.Opens, x ∈ V ∧ Smooth (V.ι ≫ W₀.hom)) := by
  have hpow : ∀ n : ℕ, (End.of d ^ n).asHom ≫ κ = κ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      change (d ≫ (End.of d ^ n).asHom) ≫ κ = κ
      rw [Category.assoc, ih, hd]
  have himage : ∀ t : Fin m, φ.left ((ι ≫ (End.of d ^ t.val).asHom).left
      (genericPoint Q.left)) ∈ β.left ⁻¹ᵁ U := by
    intro t
    change β.left (φ.left ((ι ≫ (End.of d ^ t.val).asHom).left
      (genericPoint Q.left))) ∈ U
    have heq : (ι ≫ (End.of d ^ t.val).asHom) ≫ φ ≫ β = ι ≫ κ := by
      rw [hφ, Category.assoc, hpow]
    have hp := congrArg (fun f : Q ⟶ B => f.left (genericPoint Q.left)) heq
    change β.left (φ.left ((ι ≫ (End.of d ^ t.val).asHom).left
      (genericPoint Q.left))) = κ.left (ι.left (genericPoint Q.left)) at hp
    rwa [hp]
  refine ⟨himage, ?_⟩
  intro x hx
  obtain ⟨t, rfl⟩ := s4_pushed_orbit_support ι d m a φ hx
  refine ⟨β.left ⁻¹ᵁ U, himage t, ?_⟩
  have heq : (β.left ⁻¹ᵁ U).ι ≫ W₀.hom = (β.left ∣_ U) ≫ U.ι ≫ B.hom := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, β.w]
  rw [heq]
  infer_instance

end HodgeLean.WitnessSelection
