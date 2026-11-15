import HodgeLean.Foundations.Program.SchoenTowerL1bChartGluing

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual gluing of two open charts retains their exact intersection and its mapping property. -/
theorem two_open_chart_gluing (O A B : Scheme) (f : O ⟶ A) (g : O ⟶ B)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    ∃ (M : Scheme) (j₁ : A ⟶ M) (j₂ : B ⟶ M),
      IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
      f ≫ j₁ = g ≫ j₂ ∧
      (∀ x : M, (∃ a, j₁ a = x) ∨ ∃ b, j₂ b = x) ∧
      (∀ a b, j₁ a = j₂ b ↔ ∃ o, f o = a ∧ g o = b) ∧
      (∀ (T : Scheme) (a : A ⟶ T) (b : B ⟶ T), f ≫ a = g ≫ b →
        ∃! k : M ⟶ T, j₁ ≫ k = a ∧ j₂ ≫ k = b) := by
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
  let M := colimit F
  let j₁ : A ⟶ M := colimit.ι F (.some true)
  let j₂ : B ⟶ M := colimit.ι F (.some false)
  have hglue : f ≫ j₁ = g ≫ j₂ :=
    (colimit.w F (WidePushoutShape.Hom.init true)).trans
      (colimit.w F (WidePushoutShape.Hom.init false)).symm
  refine ⟨M, j₁, j₂, inferInstance, inferInstance, hglue, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨i, z, hz⟩ := (Scheme.IsLocallyDirected.openCover F).exists_eq x
    cases i with
    | none =>
      left
      refine ⟨f z, ?_⟩
      exact (congrArg (fun h : O ⟶ M => h z)
        (colimit.w F (WidePushoutShape.Hom.init true))).trans hz
    | some b => cases b; exact Or.inr ⟨z, hz⟩; exact Or.inl ⟨z, hz⟩
  · intro x y
    constructor
    · intro he
      obtain ⟨i, fi, fj, z, hx, hy⟩ :=
        (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp he
      cases i with
      | none =>
        cases fi
        cases fj
        exact ⟨z, hx, hy⟩
      | some b => cases b <;> cases fi <;> cases fj
    · rintro ⟨z, rfl, rfl⟩
      exact congrArg (fun h : O ⟶ M => h z) hglue
  · intro T a₁ a₂ hab
    let c : ∀ b, U b ⟶ T := fun b => by cases b; exact a₂; exact a₁
    let coc : Cocone F := WidePushoutShape.mkCocone (f ≫ a₁) c (by
      intro b
      cases b
      · exact hab.symm
      · rfl)
    refine ⟨colimit.desc F coc, ?_, ?_⟩
    · exact ⟨colimit.ι_desc coc (.some true), colimit.ι_desc coc (.some false)⟩
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

end AlgebraicGeometry.RamifiedNormalization.StageFour
