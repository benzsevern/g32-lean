import HodgeLean.Foundations.Program.SchoenTowerI1aGluedSource

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_glued_chart_preimage
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (hcover : (⨆ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}, U.1.1) = ⊤)
    (Q : Scheme)
    (ι : ∀ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1},
      (s2v_i1ahi_chartDiagram X G a).obj U ⟶ Q)
    (hoverlap : ∀ U V (p : (s2v_i1ahi_chartDiagram X G a).obj U)
      (q : (s2v_i1ahi_chartDiagram X G a).obj V),
      ι U p = ι V q → ∃ L, ∃ (f : L ⟶ U) (g : L ⟶ V), ∃ t,
        (s2v_i1ahi_chartDiagram X G a).map f t = p ∧
        (s2v_i1ahi_chartDiagram X G a).map g t = q)
    (q : X.left ⟶ Q)
    (hq : ∀ U, U.1.1.ι ≫ q = s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ≫ ι U)
    (U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}) :
    q ⁻¹' Set.range (ι U) = (U.1.1 : Set X.left) := by
  ext x
  constructor
  · rintro ⟨p, hp⟩
    have hx : x ∈ ⨆ V : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}, V.1.1 :=
      hcover.symm ▸ (show x ∈ (⊤ : X.left.Opens) from trivial)
    obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    let t : V.1.1.toScheme := ⟨x, hxV⟩
    have he : ι V (s2v_i1a_affineQuotientMap X G a V.1.1 V.2 t) = ι U p := by
      have hv := congrArg (fun f : V.1.1.toScheme ⟶ Q => f t) (hq V)
      exact hv.symm.trans hp.symm
    obtain ⟨L, f, g, r, hr, _⟩ := hoverlap V U _ p he
    have ht : s2v_i1a_affineQuotientMap X G a V.1.1 V.2 t ∈
        Set.range ((s2v_i1ahi_chartDiagram X G a).map f) := ⟨r, hr⟩
    change s2v_i1a_affineQuotientMap X G a V.1.1 V.2 t ∈
      Set.range (Spec.map (s2v_i1ahi_invariantRestriction X G a L.1.1 V.1.1
        (leOfHom f) L.2 V.2)) at ht
    rw [s2v_i1ahi_transition_range X G a ha1 hamul L.1.1 V.1.1 L.1.2
      (leOfHom f) L.2 V.2] at ht
    have hxL := (Set.ext_iff.mp (s2v_i1ahi_chart_saturated_preimage X G a ha1 hamul
      V.1.1 V.1.2 V.2 L.1.1 L.2) t).mp ht
    exact (leOfHom g : L.1.1 ≤ U.1.1) hxL
  · intro hx
    refine ⟨s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ⟨x, hx⟩, ?_⟩
    exact (congrArg (fun f : U.1.1.toScheme ⟶ Q => f ⟨x, hx⟩) (hq U)).symm

end HodgeLean.Foundations.Program
