import HodgeLean.Foundations.Program.SchoenTowerI1aChartGluing
import HodgeLean.Foundations.Program.SchoenTowerI1aOpenAssembly

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_glued_source_map
    (X : Over (Spec ↧ℂ)) [X.left.IsSeparated]
    (G : Type) (a : G → (X ⟶ X))
    (hcover : (⨆ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}, U.1.1) = ⊤)
    (Q : Scheme)
    (ι : ∀ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1},
      (s2v_i1ahi_chartDiagram X G a).obj U ⟶ Q)
    (hnat : ∀ U V (f : U ⟶ V), (s2v_i1ahi_chartDiagram X G a).map f ≫ ι V = ι U) :
    ∃! q : X.left ⟶ Q, ∀ U, U.1.1.ι ≫ q =
      s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ≫ ι U := by
  apply s2v_i1ahi_glue_open_factors (fun U => U.1.1) hcover
    (fun U => s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ≫ ι U)
  intro U V
  let L : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1} :=
    ⟨⟨U.1.1 ⊓ V.1.1, U.1.2.inf V.1.2⟩,
      fun g z hz => ⟨U.2 g hz.1, V.2 g hz.2⟩⟩
  let lu : L ⟶ U := homOfLE (show L.1.1 ≤ U.1.1 from inf_le_left)
  let lv : L ⟶ V := homOfLE (show L.1.1 ≤ V.1.1 from inf_le_right)
  have hu := s2v_i1ahi_chartDiagram_square X G a lu
  have hv := s2v_i1ahi_chartDiagram_square X G a lv
  change X.left.homOfLE (leOfHom lu) ≫ _ ≫ _ = X.left.homOfLE (leOfHom lv) ≫ _ ≫ _
  rw [← Category.assoc, ← hu, Category.assoc, hnat,
    ← Category.assoc, ← hv, Category.assoc, hnat]

lemma s2v_i1ahi_glued_source_invariant
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (hcover : (⨆ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}, U.1.1) = ⊤)
    (Q : Scheme)
    (ι : ∀ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1},
      (s2v_i1ahi_chartDiagram X G a).obj U ⟶ Q)
    (q : X.left ⟶ Q)
    (hq : ∀ U, U.1.1.ι ≫ q = s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ≫ ι U)
    (g : G) : (a g).left ≫ q = q := by
  apply (X.left.openCoverOfIsOpenCover
    (fun U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1} => U.1.1) hcover).hom_ext
  intro U
  change U.1.1.ι ≫ (a g).left ≫ q = U.1.1.ι ≫ q
  rw [← Scheme.Hom.resLE_comp_ι_assoc (a g).left (U.2 g), hq,
    ← Category.assoc, s2v_i1ahi_chart_quotient_invariant]

lemma s2v_i1ahi_glued_source_surjective
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (Q : Scheme)
    (ι : ∀ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1},
      (s2v_i1ahi_chartDiagram X G a).obj U ⟶ Q)
    (hj : ∀ z : Q, ∃ U p, ι U p = z)
    (q : X.left ⟶ Q)
    (hq : ∀ U, U.1.1.ι ≫ q = s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ≫ ι U) :
    Surjective q := by
  constructor
  intro z
  obtain ⟨U, p, rfl⟩ := hj z
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul U.1.1 U.1.2 U.2
  obtain ⟨x, rfl⟩ := (s2v_i1a_affineQuotientMap X G a U.1.1 U.2).surjective p
  refine ⟨U.1.1.ι x, ?_⟩
  exact congrArg (fun f : U.1.1.toScheme ⟶ Q => f x) (hq U)

end HodgeLean.Foundations.Program
