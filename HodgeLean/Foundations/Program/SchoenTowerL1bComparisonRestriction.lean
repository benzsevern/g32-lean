import Mathlib.Analysis.Complex.Basic
import HodgeLean.Foundations.Program.SchoenTowerL1bModelIdeal
import Mathlib.AlgebraicGeometry.Morphisms.Flat

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Flat extension preserves a trivialized ideal as an ideal in the target ring. -/
theorem s2v_l1b_ideal_trivialization_flat {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (I : Ideal A) (t : I ≃ₗ[A] A) :
    Nonempty ((I.map (algebraMap A B)) ≃ₗ[B] B) := by
  let g := (t.symm 1).val
  have hI : I = Ideal.span {g} := by
    apply le_antisymm
    · intro a ha
      exact Ideal.mem_span_singleton'.mpr
        ⟨t ⟨a, ha⟩, (s2v_l1b_trivialization_generator I t).2 ⟨a, ha⟩ |>.symm⟩
    · exact Ideal.span_le.mpr (by
        intro a ha
        obtain rfl := Set.mem_singleton_iff.mp ha
        exact (t.symm 1).property)
  rw [hI, Ideal.map_span, Set.image_singleton]
  obtain ⟨e, _⟩ := s2v_l1b_regular_principal_trivialization
    (algebraMap A B g) (s2v_l1b_trivialization_generator_flat I t)
  exact ⟨e⟩

/-- Flat scheme pullback preserves local ideal-module trivializations. -/
theorem s2v_l1b_local_trivialization_flat {X Y : Scheme} (f : X ⟶ Y) [Flat f]
    (I : Y.IdealSheafData)
    (hI : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty ((I.ideal U) ≃ₗ[Γ(Y, U)] Γ(Y, U))) :
    ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(X, V)] Γ(X, V)) := by
  intro x
  obtain ⟨U, hx, ⟨t⟩⟩ := hI (f x)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ U.1 from hx)
  refine ⟨⟨V, hV⟩, hxV, ?_⟩
  rw [s2v_l1b_comap_ideal_affine_charts f I U ⟨V, hV⟩ hVU]
  let a := (f.appLE U.1 V hVU).hom
  letI := a.toAlgebra
  letI : Module.Flat Γ(Y, U) Γ(X, V) := f.flat_appLE U.2 hV hVU
  exact s2v_l1b_ideal_trivialization_flat (I.ideal U) t

/-- The retained mapping property also gives unique lifts of scheme morphisms. -/
theorem s2v_l1b_blowup_scheme_lift
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ z : T.left, ∃ V : T.left.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (T : Scheme) (f : T ⟶ B.left)
    (hf : ∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
      Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) :
    ∃! k : T ⟶ X.left, k ≫ p.left = f := by
  let T' : Over (Spec ↧ℂ) := Over.mk (f ≫ B.hom)
  let f' : T' ⟶ B := Over.homMk f
  obtain ⟨k, hk, huniq⟩ := hblowup T' f' hf
  refine ⟨k.left, congrArg (fun a => a.left) hk, ?_⟩
  intro l hl
  let l' : T' ⟶ X := Over.homMk l (by
    change l ≫ X.hom = f ≫ B.hom
    rw [← Over.w p, ← Category.assoc, hl])
  have h : l' ≫ p = f' := Over.OverMorphism.ext hl
  exact congrArg (fun a => a.left) (huniq l' h)

/-- The ideal mapping property restricts to the entire inverse image of a base open. -/
theorem s2v_l1b_blowup_open_lift
    {B X : Scheme} (p : X ⟶ B) (I : B.IdealSheafData)
    (hX : ∀ (T : Scheme) (f : T ⟶ B),
      (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.Opens) (T : Scheme) (f : T ⟶ U.toScheme)
    (hf : ∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
      Nonempty (((I.comap (f ≫ U.ι)).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) :
    ∃! k : T ⟶ (p ⁻¹ᵁ U).toScheme, k ≫ (p ∣_ U) = f := by
  obtain ⟨k, hk, huniq⟩ := hX T (f ≫ U.ι) hf
  have hr : Set.range k ⊆ Set.range (p ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨k z, ?_⟩, rfl⟩
    change p (k z) ∈ U
    have he := congrArg (fun a : T ⟶ B => a z) hk
    exact he ▸ (f z).property
  let l := IsOpenImmersion.lift (p ⁻¹ᵁ U).ι k hr
  have hl : l ≫ (p ∣_ U) = f := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      IsOpenImmersion.lift_fac, hk]
  refine ⟨l, hl, ?_⟩
  intro a ha
  apply (cancel_mono (p ⁻¹ᵁ U).ι).mp
  rw [IsOpenImmersion.lift_fac]
  apply huniq
  rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, ha]

/-- The affine spectrum parametrization has its canonical coefficient map on sections. -/
theorem s2v_l1b_fromSpec_appLE {B : Scheme} (U : B.affineOpens) :
    U.2.fromSpec.appLE U.1 ⊤ (by intro x hx; exact U.2.fromSpec_preimage_self.ge hx) =
      (Scheme.ΓSpecIso Γ(B, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp]
  simp

/-- The retained centre ideal on its affine spectrum has the canonical two section generators. -/
theorem s2v_l1b_centre_fromSpec {B : Scheme} (I : B.IdealSheafData)
    (U : B.affineOpens) (u v : Γ(B, U)) (hI : I.ideal U = Ideal.span {u, v}) :
    (I.comap U.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso Γ(B, U)).inv.hom u,
        (Scheme.ΓSpecIso Γ(B, U)).inv.hom v} := by
  rw [s2v_l1b_comap_ideal_affine_charts U.2.fromSpec I U
    ⟨⊤, isAffineOpen_top _⟩ U.2.fromSpec_preimage_self.ge,
    hI, s2v_l1b_fromSpec_appLE, Ideal.map_span, Set.image_pair]

/-- Affine source ideals over a coefficient spectrum use the specified canonical section map. -/
theorem s2v_l1b_spectrum_pair_pullback {R : Type} [CommRing R]
    (I : (Spec (CommRingCat.of R)).IdealSheafData) (u v : R)
    (hI : I.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u,
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom v})
    {T : Scheme} (f : T ⟶ Spec (CommRingCat.of R)) (V : T.affineOpens) :
    (I.comap f).ideal V =
      let g := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        f.appLE ⊤ V.1 (by intro a ha; trivial)).hom
      Ideal.span {g u, g v} := by
  rw [s2v_l1b_comap_ideal_affine_charts f I ⟨⊤, isAffineOpen_top _⟩ V
    (by intro a ha; trivial), hI, Ideal.map_span, Set.image_pair]
  rfl

/-- Any model with the regular binomial chart cover has locally free centre ideal. -/
theorem s2v_l1b_given_model_invertible {R : Type} [CommRing R]
    (u v : R) (hv : IsRegular v)
    (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hu' : IsRegular u) (hv' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v))
    (I : (Spec (CommRingCat.of R)).IdealSheafData)
    (hI : I.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u,
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom v})
    (M : Scheme)
    (j₁ : Spec (CommRingCat.of (s2v_L1bChart u v)) ⟶ M) [IsOpenImmersion j₁]
    (j₂ : Spec (CommRingCat.of (s2v_L1bChart v u)) ⟶ M) [IsOpenImmersion j₂]
    (p : M ⟶ Spec (CommRingCat.of R))
    (hcover : ∀ x : M, (∃ a, j₁ a = x) ∨ ∃ a, j₂ a = x)
    (hp₁ : j₁ ≫ p = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp Polynomial.C)))
    (hp₂ : j₂ ≫ p = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp Polynomial.C))) :
    ∀ x : M, ∃ U : M.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap p).ideal U) ≃ₗ[Γ(M, U)] Γ(M, U)) := by
  have h₁ : Nonempty ((((I.comap p).comap j₁).ideal ⟨⊤, isAffineOpen_top _⟩)
      ≃ₗ[Γ(Spec (CommRingCat.of (s2v_L1bChart u v)), ⊤)]
        Γ(Spec (CommRingCat.of (s2v_L1bChart u v)), ⊤)) := by
    rw [← Scheme.IdealSheafData.comap_comp, hp₁]
    exact s2v_l1b_chart_spectrum_trivialization u v hv hu I hI
  have h₂ : Nonempty ((((I.comap p).comap j₂).ideal ⟨⊤, isAffineOpen_top _⟩)
      ≃ₗ[Γ(Spec (CommRingCat.of (s2v_L1bChart v u)), ⊤)]
        Γ(Spec (CommRingCat.of (s2v_L1bChart v u)), ⊤)) := by
    rw [← Scheme.IdealSheafData.comap_comp, hp₂]
    apply s2v_l1b_chart_spectrum_trivialization v u hu' hv' I
    rw [hI, Set.pair_comm]
  intro x
  rcases hcover x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · refine ⟨⟨j₁ ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion j₁⟩,
      ⟨a, trivial, rfl⟩, ?_⟩
    exact s2v_l1b_open_image_trivialization j₁ (I.comap p) h₁
  · refine ⟨⟨j₂ ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion j₂⟩,
      ⟨a, trivial, rfl⟩, ?_⟩
    exact s2v_l1b_open_image_trivialization j₂ (I.comap p) h₂


/-- The affine-base restriction retains the ideal mapping property on all source schemes. -/
theorem s2v_l1b_blowup_affine_lift
    {B X : Scheme} (p : X ⟶ B) (I : B.IdealSheafData)
    (hX : ∀ (T : Scheme) (f : T ⟶ B),
      (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.affineOpens) (T : Scheme) (f : T ⟶ Spec Γ(B, U))
    (hf : ∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
      Nonempty ((((I.comap U.2.fromSpec).comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) :
    ∃! k : T ⟶ (p ⁻¹ᵁ U.1).toScheme,
      k ≫ (p ∣_ U.1) ≫ U.2.isoSpec.hom = f := by
  have hf' : ∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
      Nonempty (((I.comap ((f ≫ U.2.isoSpec.inv) ≫ U.1.ι)).ideal V)
        ≃ₗ[Γ(T, V)] Γ(T, V)) := by
    have he : I.comap ((f ≫ U.2.isoSpec.inv) ≫ U.1.ι) =
        (I.comap U.2.fromSpec).comap f := by
      rw [Category.assoc, ← IsAffineOpen.fromSpec, Scheme.IdealSheafData.comap_comp]
    rw [he]
    exact hf
  obtain ⟨k, hk, hu⟩ := s2v_l1b_blowup_open_lift p I hX U.1 T
    (f ≫ U.2.isoSpec.inv) hf'
  refine ⟨k, ?_, ?_⟩
  · dsimp only
    exact (Category.assoc k (p ∣_ U.1) U.2.isoSpec.hom).symm.trans
      ((congrArg (fun a => a ≫ U.2.isoSpec.hom) hk).trans (by simp))
  · intro l hl
    apply hu
    apply (cancel_mono U.2.isoSpec.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hl

/-- The entire inverse image has locally free centre ideal in affine-base coordinates. -/
theorem s2v_l1b_blowup_affine_trivialization
    {B X : Scheme} (p : X ⟶ B) (I : B.IdealSheafData)
    (hX : ∀ z : X, ∃ V : X.affineOpens, z ∈ V.1 ∧
      Nonempty (((I.comap p).ideal V) ≃ₗ[Γ(X, V)] Γ(X, V))) (U : B.affineOpens) :
    ∀ z : (p ⁻¹ᵁ U.1).toScheme,
      ∃ V : (p ⁻¹ᵁ U.1).toScheme.affineOpens, z ∈ V.1 ∧
        Nonempty ((((I.comap U.2.fromSpec).comap
          ((p ∣_ U.1) ≫ U.2.isoSpec.hom)).ideal V) ≃ₗ[Γ((p ⁻¹ᵁ U.1).toScheme, V)]
            Γ((p ⁻¹ᵁ U.1).toScheme, V)) := by
  have he : (I.comap U.2.fromSpec).comap ((p ∣_ U.1) ≫ U.2.isoSpec.hom) =
      (I.comap p).comap (p ⁻¹ᵁ U.1).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, Category.assoc,
      IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc, morphismRestrict_ι,
      Scheme.IdealSheafData.comap_comp]
  rw [he]
  exact s2v_l1b_local_trivialization_flat (p ⁻¹ᵁ U.1).ι (I.comap p) hX

end HodgeLean.Foundations.Program
