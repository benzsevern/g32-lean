import HodgeLean.Foundations.Program.SchoenSumZeroProperQuotient

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every retained categorical zero-sum quotient has integrally closed actual local rings. -/
theorem s2_retainedQuotient_normal (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (h : ℕ)
    (W : Over (Spec ↧ℂ)) (q : g3_power Y h ⟶ W)
    (hqinv : ∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
      ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y h ⟶ T),
      (∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
        ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ f = f) →
      ∃! d : W ⟶ T, q ≫ d = f) :
    ∀ x : W.left, IsIntegrallyClosed (W.left.presheaf.stalk x) := by
  obtain ⟨W', q', _, _, hnormal, _, _, hqinv', _, hq'⟩ :=
    s2_sumZero_normalProperQuotient S Y a e ha1 hamul h
  obtain ⟨f, hf, _⟩ := hq W' q' hqinv'
  obtain ⟨g, hg, _⟩ := hq' W q hqinv
  have hfg : f ≫ g = 𝟙 W := by
    obtain ⟨u, _, hu⟩ := hq W q hqinv
    apply (hu (f ≫ g) ?_).trans (hu (𝟙 W) ?_).symm
    · rw [← Category.assoc, hf, hg]
    · exact Category.comp_id q
  have hgf : g ≫ f = 𝟙 W' := by
    obtain ⟨u, _, hu⟩ := hq' W' q' hqinv'
    apply (hu (g ≫ f) ?_).trans (hu (𝟙 W') ?_).symm
    · rw [← Category.assoc, hg, hf]
    · exact Category.comp_id q'
  let eW : W' ≅ W := ⟨g, f, hgf, hfg⟩
  let eS : W'.left ≅ W.left := (Over.forget (Spec ↧ℂ)).mapIso eW
  intro x
  let r := (asIso (eS.inv.stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨hdom, hnormal'⟩ := hnormal (eS.inv x)
  letI := hdom
  letI := hnormal'
  exact IsIntegrallyClosed.of_equiv r

end HodgeLean.Foundations.Program
