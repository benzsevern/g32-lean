import HodgeLean.Foundations.Program.SchoenSumZeroAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The subgroup of all retained coordinate translations and permutations. -/
def s2v_l1b_fullCoordinateGroup (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (n : ℕ) :
    Subgroup (Aut (g3_power Y n)) where
  carrier := {f | ∃ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
    f.asIso.hom = s2_action S Y a e n v τ}
  one_mem' := ⟨0, 1, (s2_coordinateAction_laws S Y a e ha1 hamul n).1.symm⟩
  mul_mem' := by
    rintro f g ⟨v, σ, hf⟩ ⟨w, τ, hg⟩
    refine ⟨(fun i => v i + w (σ.symm i)), σ * τ, ?_⟩
    change g.asIso.hom ≫ f.asIso.hom = _
    rw [hg, hf, (s2_coordinateAction_laws S Y a e ha1 hamul n).2]
  inv_mem' := by
    rintro f ⟨v, σ, hf⟩
    refine ⟨(fun i => -v (σ i)), σ⁻¹, ?_⟩
    have heq : f = Aut.of (s2_coordinateActionIso S Y a e ha1 hamul n v σ) := by
      apply Aut.ext
      apply Iso.ext
      exact hf
    subst f
    rfl

example (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (n : ℕ)
    (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)) :
    Aut.of (s2_coordinateActionIso S Y a e ha1 hamul n v τ) ∈
      s2v_l1b_fullCoordinateGroup S Y a e ha1 hamul n := ⟨v, τ, rfl⟩

/-- Only finitely many retained full coordinate automorphisms occur. -/
theorem s2v_l1b_fullCoordinateGroup_finite
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (n : ℕ) :
    Finite (s2v_l1b_fullCoordinateGroup S Y a e ha1 hamul n) := by
  let A : ((Fin n → ZMod S.m) × Equiv.Perm (Fin n)) →
      (g3_power Y n ⟶ g3_power Y n) := fun p => s2_action S Y a e n p.1 p.2
  letI : Finite (Set.range A) := (Set.finite_range A).to_subtype
  let F : s2v_l1b_fullCoordinateGroup S Y a e ha1 hamul n → Set.range A := fun g =>
    ⟨g.val.asIso.hom, by
      obtain ⟨v, τ, hg⟩ := g.property
      exact ⟨(v, τ), hg.symm⟩⟩
  apply Finite.of_injective F
  intro f g hfg
  apply Subtype.ext
  apply Aut.ext
  apply Iso.ext
  exact congrArg Subtype.val hfg

end HodgeLean.Foundations.Program
