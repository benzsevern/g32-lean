import HodgeLean.Foundations.WitnessSelection.InitialCover
import HodgeLean.Foundations.Program.G32Native.SelectedTowerGenericAvoidance

/-! # Initial paired slice on the unmarked étale open -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The retained quotient is étale on the paired branch complement containing
the generic image of the selected slice.
Source: Schoen (1988), p. 15; SGA 1, Exposé I, §§9–10. -/
theorem selected_initial_paired_etale_open
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

    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left]
    (k r : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (ℓ₀ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (σ : Fin (2 * r) ≃ I)
    (hpair : ∀ i : Fin r,
      (s2c_branchIdeal Z B h γ (marks (σ ⟨2 * i.val, by omega⟩))).comap
        (eQ.hom ≫ ℓ₀).left =
      (s2c_branchIdeal Z B h γ (marks (σ ⟨2 * i.val + 1, by omega⟩))).comap
        (eQ.hom ≫ ℓ₀).left)
    (hsingle : ∀ i : Fin r, Nonempty (s2c_subscheme Q
      ((s2c_branchIdeal Z B h γ (marks (σ ⟨2 * i.val, by omega⟩))).comap
        (eQ.hom ≫ ℓ₀).left) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ)))) :
    ∃ U : B.left.Opens,
      (eQ.hom ≫ ℓ₀).left (genericPoint Q.left) ∈ U ∧
      Etale (β.left ∣_ U) ∧
      Smooth ((β.left ⁻¹ᵁ U).ι ≫ W.hom) := by
  obtain ⟨U, hU, hgen⟩ := selected_paired_slice_generic_open Q k r hk eQ B ℓ₀
    (fun t => s2c_branchIdeal Z B h γ (marks (σ t))) hpair hsingle
  have hav : ∀ i, ∀ b ∈ U, b ∉ (s2c_branchIdeal Z B h γ (marks i)).support := by
    intro i b hb
    simpa only [σ.apply_symm_apply] using (hU b).mp hb (σ.symm i)
  obtain ⟨het, hsm⟩ := HodgeLean.WitnessSelection.initial_cover_smooth_open
    S Y Z W B a e ha1 hamul hinj p hp hpsurj hporbit T I eY hpointAction
    marks hbranch h hh q hqsurj hqinv hq γ hγsurj hγinv hγ β hβ
    d hd horder hgenerator U hav
  exact ⟨U, hgen, het, hsm⟩

#print axioms selected_initial_paired_etale_open
end HodgeLean.Foundations.Program.G32Native
