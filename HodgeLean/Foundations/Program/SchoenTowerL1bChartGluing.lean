import HodgeLean.Foundations.Program.SchoenTowerL1bChartOverlap
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two schemes with a common open subscheme have a scheme gluing covered by their images. -/
theorem s2v_l1b_glue_pair (O A B : Scheme) (f : O ⟶ A) (g : O ⟶ B)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    ∃ (X : Scheme) (j₁ : A ⟶ X) (j₂ : B ⟶ X),
      IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
      f ≫ j₁ = g ≫ j₂ ∧
      (∀ x : X, (∃ a : A, j₁ a = x) ∨ ∃ b : B, j₂ b = x) ∧
      (∀ (T : Scheme) (a : A ⟶ T) (b : B ⟶ T), f ≫ a = g ≫ b →
        ∃! k : X ⟶ T, j₁ ≫ k = a ∧ j₂ ≫ k = b) := by
  let U : Bool → Scheme := fun b => if b then A else B
  let a : ∀ b, O ⟶ U b := fun b => by cases b; exact g; exact f
  let F := WidePushoutShape.wideSpan O U a
  have : ∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h) := by
    rintro i j (_ | b)
    · change IsOpenImmersion (F.map (𝟙 i))
      rw [F.map_id]
      infer_instance
    · cases b <;> dsimp [F, a, U] <;> infer_instance
  have : ∀ b, Mono ((F ⋙ Scheme.forget).map (WidePushoutShape.Hom.init b)) := by
    intro b
    apply (mono_iff_injective _).mpr
    cases b
    · exact g.isOpenEmbedding.injective
    · exact f.isOpenEmbedding.injective
  let X := colimit F
  let j₁ : A ⟶ X := colimit.ι F (.some true)
  let j₂ : B ⟶ X := colimit.ι F (.some false)
  refine ⟨X, j₁, j₂, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact (colimit.w F (WidePushoutShape.Hom.init true)).trans
      (colimit.w F (WidePushoutShape.Hom.init false)).symm
  · intro x
    obtain ⟨i, z, hz⟩ := (Scheme.IsLocallyDirected.openCover F).exists_eq x
    cases i with
    | none =>
        left
        refine ⟨f z, ?_⟩
        have h := congrArg (fun h : O ⟶ X => h z)
          (colimit.w F (WidePushoutShape.Hom.init true))
        exact h.trans hz
    | some b =>
        cases b
        · exact Or.inr ⟨z, hz⟩
        · exact Or.inl ⟨z, hz⟩

  · intro T a₁ a₂ hab
    let c : ∀ b, U b ⟶ T := fun b => by cases b; exact a₂; exact a₁
    let coc : Cocone F := WidePushoutShape.mkCocone (f ≫ a₁) c (by
      intro b
      cases b
      · exact hab.symm
      · rfl)
    refine ⟨colimit.desc F coc, ?_, ?_⟩
    · constructor
      · exact colimit.ι_desc coc (.some true)
      · exact colimit.ι_desc coc (.some false)
    · intro k hk
      apply colimit.hom_ext
      intro i
      rw [colimit.ι_desc]
      cases i with
      | none =>
          change colimit.ι F none ≫ k = f ≫ a₁
          rw [← colimit.w F (WidePushoutShape.Hom.init true), Category.assoc]
          exact congrArg (fun q => f ≫ q) hk.1
      | some b => cases b; exact hk.2; exact hk.1

/-- The two binomial charts glue over their coefficient spectrum and cover the resulting scheme. -/
theorem s2v_l1b_binomial_chart_scheme {R : Type*} [CommRing R] (u v : R) :
    ∃ (X : Scheme)
      (j₁ : Spec (CommRingCat.of (s2v_L1bChart u v)) ⟶ X)
      (j₂ : Spec (CommRingCat.of (s2v_L1bChart v u)) ⟶ X)
      (p : X ⟶ Spec (CommRingCat.of R)),
      IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
      (∀ x : X, (∃ a, j₁ a = x) ∨ ∃ b, j₂ b = x) ∧
      j₁ ≫ p = Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp
          Polynomial.C)) ∧
      j₂ ≫ p = Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp
          Polynomial.C)) := by
  let q₁ := Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})
  let q₂ := Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})
  let l₁ := algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
  let l₂ := algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u)
  obtain ⟨e, heC, _⟩ := s2v_l1b_overlap_equiv u v
  let eS := Scheme.Spec.mapIso e.toCommRingCatIso.op
  let f := Spec.map (CommRingCat.ofHom l₁)
  let g := eS.inv ≫ Spec.map (CommRingCat.ofHom l₂)
  have : IsOpenImmersion f := inferInstance
  have : IsOpenImmersion g := inferInstance
  obtain ⟨X, j₁, j₂, hj₁, hj₂, _, hcover, hmap⟩ := s2v_l1b_glue_pair _ _ _ f g
  let p₁ := Spec.map (CommRingCat.ofHom (q₁.comp Polynomial.C))
  let p₂ := Spec.map (CommRingCat.ofHom (q₂.comp Polynomial.C))
  have hbase : f ≫ p₁ = g ≫ p₂ := by
    apply (cancel_epi eS.hom).mp
    change eS.hom ≫ (f ≫ p₁) = eS.hom ≫ ((eS.inv ≫ _) ≫ p₂)
    rw [Category.assoc eS.inv, eS.hom_inv_id_assoc]
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom l₁) ≫ Spec.map (CommRingCat.ofHom (q₁.comp Polynomial.C))) =
      Spec.map (CommRingCat.ofHom l₂) ≫ Spec.map (CommRingCat.ofHom (q₂.comp Polynomial.C))
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact heC
  obtain ⟨p, hp, _⟩ := hmap _ p₁ p₂ hbase
  exact ⟨X, j₁, j₂, p, hj₁, hj₂, hcover, hp⟩

end HodgeLean.Foundations.Program
