import HodgeLean.Foundations.Program.SchoenTowerL1bModelAffineLift

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The specified section map on an affine neighborhood represents its actual base morphism. -/
theorem s2v_l1b_spec_actual_section_map {R : Type} [CommRing R]
    {T : Scheme} (f : T ⟶ Spec (CommRingCat.of R)) (V : T.affineOpens) :
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      f.appLE ⊤ V.1 (by intro a ha; trivial)) = V.2.fromSpec ≫ f := by
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) V.2 _

/-- The affine lifts descend uniquely over every source with the specified local ideal freeness. -/
theorem s2v_l1b_model_source_lift {R : Type} [CommRing R]
    (u v : R) (M : Scheme)
    (j₁ : Spec (CommRingCat.of (s2v_L1bChart u v)) ⟶ M)
    (j₂ : Spec (CommRingCat.of (s2v_L1bChart v u)) ⟶ M)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (π : M ⟶ Spec (CommRingCat.of R))
    (hcover : ∀ z : M, (∃ a, j₁ a = z) ∨ ∃ a, j₂ a = z)
    (hp₁ : j₁ ≫ π = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp
        Polynomial.C)))
    (hp₂ : j₂ ≫ π = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp
        Polynomial.C)))
    (htransition :
      let ε := Classical.choose (s2v_l1b_overlap_equiv u v)
      Spec.map (CommRingCat.ofHom
        (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))) ≫ j₁ =
      Spec.map (CommRingCat.ofHom ε.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u))) ≫ j₂)

    (T : Scheme) (f : T ⟶ Spec (CommRingCat.of R))
    (hlocal : ∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
      let g := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V.1
        (by intro a ha; trivial)).hom
      Nonempty ((Ideal.span {g u, g v}) ≃ₗ[Γ(T, V)] Γ(T, V))) :
    ∃! k : T ⟶ M, k ≫ π = f := by
  choose V hV eV using hlocal
  let g (z : T) : R →+* Γ(T, V z) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (V z).1
      (by intro a ha; trivial)).hom
  let e (z : T) : (Ideal.span {g z u, g z v}) ≃ₗ[Γ(T, V z)] Γ(T, V z) :=
    Classical.choice (eV z)
  have hu (z : T) : g z u ∈ Ideal.span {g z u, g z v} :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hv (z : T) : g z v ∈ Ideal.span {g z u, g z v} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers T
    (fun z => Spec Γ(T, V z)) (fun z => (V z).2.fromSpec) (by
      intro z
      have hz : z ∈ Set.range (V z).2.fromSpec := by
        rw [IsAffineOpen.range_fromSpec]
        exact hV z
      obtain ⟨a, ha⟩ := hz
      exact ⟨z, a, ha⟩)
  have hg (z : T) : Spec.map (CommRingCat.ofHom (g z)) = 𝒰.f z ≫ f :=
    s2v_l1b_spec_actual_section_map f (V z)
  apply s2v_l1b_source_cover_lift π f 𝒰
  · intro z
    rw [← hg]
    exact s2v_l1b_model_affine_lift u v (g z) _ (hu z) (hv z) rfl (e z)
      M j₁ j₂ π hcover hp₁ hp₂ htransition
  · intro a b k l hk hl
    apply s2v_l1b_model_flat_hom_ext u v (g a) _ (hu a) (hv a) rfl (e a)
      M j₁ j₂ π hcover hp₁ hp₂ htransition _ (pullback.fst (𝒰.f a) (𝒰.f b))
    · rw [hg, ← Category.assoc]
      exact hk
    · rw [hg, ← Category.assoc]
      exact hl

end HodgeLean.Foundations.Program
