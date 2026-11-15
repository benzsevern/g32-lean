import HodgeLean.Foundations.Program.SchoenSumZeroActionGroup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The actual zero-sum product action subgroup is finite, including nonfaithful actions. -/
theorem s2_sumZeroActionGroup_finite (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (h : ℕ) :
    Finite (s2_sumZeroActionGroup S Y a e ha1 hamul h) := by
  let A : ((Fin h → ZMod S.m) × Equiv.Perm (Fin h)) →
      (g3_power Y h ⟶ g3_power Y h) := fun p => s2_action S Y a e h p.1 p.2
  letI : Finite (Set.range A) := (Set.finite_range A).to_subtype
  let F : s2_sumZeroActionGroup S Y a e ha1 hamul h → Set.range A := fun g =>
    ⟨g.val.asIso.hom, by
      obtain ⟨v, σ, _, hg⟩ := g.property
      exact ⟨(v, σ), hg.symm⟩⟩
  apply Finite.of_injective F
  intro f g hfg
  apply Subtype.ext
  apply Aut.ext
  apply Iso.ext
  exact congrArg Subtype.val hfg

end HodgeLean.Foundations.Program
