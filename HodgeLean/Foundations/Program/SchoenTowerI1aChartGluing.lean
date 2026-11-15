import HodgeLean.Foundations.Program.SchoenTowerI1aChartDiagram
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_chartDiagram_locallyDirected
    (X : Over (Spec ↧ℂ)) [X.left.IsSeparated]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g) :
    (s2v_i1ahi_chartDiagram X G a ⋙ Scheme.forget).IsLocallyDirected := by
  let F := s2v_i1ahi_chartDiagram X G a
  haveI {U V} (f : U ⟶ V) : IsOpenImmersion (F.map f) :=
    s2v_i1ahi_chartDiagram_openImmersion X G a ha1 hamul f
  constructor
  intro U V W f g p q hpq
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul U.1.1 U.1.2 U.2
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul V.1.1 V.1.2 V.2
  obtain ⟨x, rfl⟩ := (s2v_i1a_affineQuotientMap X G a U.1.1 U.2).surjective p
  obtain ⟨y, rfl⟩ := (s2v_i1a_affineQuotientMap X G a V.1.1 V.2).surjective q
  have hxy : s2v_i1a_affineQuotientMap X G a W.1.1 W.2
      (X.left.homOfLE (leOfHom f) x) =
      s2v_i1a_affineQuotientMap X G a W.1.1 W.2 (X.left.homOfLE (leOfHom g) y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      ← s2v_i1ahi_chartDiagram_square X G a f, ← s2v_i1ahi_chartDiagram_square X G a g]
    exact hpq
  have hxV : x.1 ∈ V.1.1 := by
    have ht : s2v_i1a_affineQuotientMap X G a W.1.1 W.2
        (X.left.homOfLE (leOfHom f) x) ∈
        s2v_i1a_affineQuotientMap X G a W.1.1 W.2 '' {z | W.1.1.ι z ∈ V.1.1} := by
      refine ⟨X.left.homOfLE (leOfHom g) y, ?_, hxy.symm⟩
      change (X.left.homOfLE (leOfHom g) y).1 ∈ V.1.1
      rw [Scheme.homOfLE_apply]
      exact y.property
    have hs := (Set.ext_iff.mp (s2v_i1ahi_chart_saturated_preimage X G a ha1 hamul
      W.1.1 W.1.2 W.2 V.1.1 V.2) (X.left.homOfLE (leOfHom f) x)).mp ht
    change (X.left.homOfLE (leOfHom f) x).1 ∈ V.1.1 at hs
    simpa only [Scheme.homOfLE_apply] using hs
  let L : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1} :=
    ⟨⟨U.1.1 ⊓ V.1.1, U.1.2.inf V.1.2⟩,
      fun g z hz => ⟨U.2 g hz.1, V.2 g hz.2⟩⟩
  let lu : L ⟶ U := homOfLE (show L.1.1 ≤ U.1.1 from inf_le_left)
  let lv : L ⟶ V := homOfLE (show L.1.1 ≤ V.1.1 from inf_le_right)
  let t : L.1.1.toScheme := ⟨x.1, x.property, hxV⟩
  let r := s2v_i1a_affineQuotientMap X G a L.1.1 L.2 t
  have hr : F.map lu r = s2v_i1a_affineQuotientMap X G a U.1.1 U.2 x := by
    change (s2v_i1a_affineQuotientMap X G a L.1.1 L.2 ≫ F.map lu) t = _
    rw [s2v_i1ahi_chartDiagram_square]
    change s2v_i1a_affineQuotientMap X G a U.1.1 U.2 (X.left.homOfLE inf_le_left t) = _
    congr 1
    exact Subtype.ext (Scheme.homOfLE_apply _ _)
  refine ⟨L, lu, lv, r, hr, ?_⟩
  apply (Scheme.Hom.isOpenEmbedding (F.map g)).injective
  change (F.map lv ≫ F.map g) r = _
  rw [← F.map_comp]
  have hc : lv ≫ g = lu ≫ f := Subsingleton.elim _ _
  rw [hc, F.map_comp]
  change F.map f (F.map lu r) = _
  rw [hr]
  exact hpq

/-- The actual invariant spectra glue with their canonical transition equations.
Source: SGA 1, Exposé V, §1; Mathlib, Scheme.IsLocallyDirected.openCover. -/
lemma s2v_i1ahi_glued_chart_scheme
    (X : Over (Spec ↧ℂ)) [X.left.IsSeparated]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g) :
    ∃ (Q : Scheme)
      (ι : ∀ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1},
        (s2v_i1ahi_chartDiagram X G a).obj U ⟶ Q),
      (∀ U, IsOpenImmersion (ι U)) ∧
      (∀ U V (f : U ⟶ V), (s2v_i1ahi_chartDiagram X G a).map f ≫ ι V = ι U) ∧
      (∀ z : Q, ∃ U p, ι U p = z) ∧
      ∀ U V (p : (s2v_i1ahi_chartDiagram X G a).obj U)
        (q : (s2v_i1ahi_chartDiagram X G a).obj V),
        ι U p = ι V q ↔ ∃ L, ∃ (f : L ⟶ U) (g : L ⟶ V), ∃ t,
          (s2v_i1ahi_chartDiagram X G a).map f t = p ∧
          (s2v_i1ahi_chartDiagram X G a).map g t = q := by
  let F := s2v_i1ahi_chartDiagram X G a
  haveI {U V} (f : U ⟶ V) : IsOpenImmersion (F.map f) :=
    s2v_i1ahi_chartDiagram_openImmersion X G a ha1 hamul f
  letI := s2v_i1ahi_chartDiagram_locallyDirected X G a ha1 hamul
  refine ⟨colimit F, colimit.ι F, fun U => inferInstance, ?_, ?_, ?_⟩
  · exact fun U V f => colimit.w F f
  · exact Scheme.IsLocallyDirected.ι_jointly_surjective F
  · exact fun U V p q => Scheme.IsLocallyDirected.ι_eq_ι_iff F

end HodgeLean.Foundations.Program
