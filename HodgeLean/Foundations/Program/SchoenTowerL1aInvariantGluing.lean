import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantPresheaf
import HodgeLean.Foundations.Program.SchoenTowerL1aEqualizerLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Properties

/-! # Localization compatibility of invariant section diagrams

The actual localization maps on invariant rings needed for affine gluing over
the retained base. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- On a domain-valued affine inverse image, invariant sections localize at a pulled-back base section.
Source: Hartshorne, Algebraic Geometry, II.2, principal affine opens; Stacks Project, tag 04A9, invariant functions. -/
theorem s2v_l1a_fixedSections_localization_of_domain
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)
    (U : Y.affineOpens) [IsDomain Γ(X, f ⁻¹ᵁ U.1)] (d : Γ(Y, U.1)) :
    letI : Algebra (s2v_l1a_fixedSectionSubring f a ha U.1)
        (s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)) :=
      (s2v_l1a_fixedSectionRestriction f a ha U.1 (Y.basicOpen d) (Y.basicOpen_le d)).toAlgebra
    IsLocalization.Away (s2v_l1a_baseToFixedSections f a ha U.1 d)
      (s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)) := by
  let R := Γ(X, f ⁻¹ᵁ U.1)
  let A := Γ(X, f ⁻¹ᵁ Y.basicOpen d)
  let res : R ⟶ A := X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le d))).op
  let inst : Algebra R A := res.hom.toAlgebra
  let ρ (t : T) : R →+* R := (s2v_l1a_saturatedSectionEnd f a ha U.1 t).hom
  let σ (t : T) : A →+* A := (s2v_l1a_saturatedSectionEnd f a ha (Y.basicOpen d) t).hom
  let P := s2v_l1a_fixedSectionSubring f a ha U.1
  let Q := s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)
  let : Algebra P Q :=
    (s2v_l1a_fixedSectionRestriction f a ha U.1 (Y.basicOpen d) (Y.basicOpen_le d)).toAlgebra
  have hP (r : R) : r ∈ P ↔ ∀ t, ρ t r = r := s2v_l1a_mem_fixedSectionSubring f a ha U.1 r
  have hQ (s : A) : s ∈ Q ↔ ∀ t, σ t s = s :=
    s2v_l1a_mem_fixedSectionSubring f a ha (Y.basicOpen d) s
  let : IsLocalHom Q.subtype := s2v_l1a_invariant_subring_isLocalHom σ Q hQ
  have hlocal : IsLocalization.Away ((f.app U.1).hom d) A := by
    dsimp +instances [inst, res, A, R]
    rw! (castMode := .all) [f.preimage_basicOpen d]
    exact (U.2.preimage f).isLocalization_basicOpen _
  have hmap (t : T) : (σ t).comp (algebraMap R A) = (algebraMap R A).comp (ρ t) := by
    exact (congrArg CommRingCat.Hom.hom
      (s2v_l1a_saturatedSectionEnd_naturality f a ha U.1 (Y.basicOpen d)
        (Y.basicOpen_le d) t)).symm
  exact s2v_l1a_equalizer_subring_localization ρ σ P Q hP hQ (fun r => rfl)
    ((f.app U.1).hom d) (s2v_l1a_baseToFixedSections f a ha U.1 d).property hmap

/-- For a finite endomorphism family, invariant sections localize at a pulled-back base section.
Source: Hartshorne, Algebraic Geometry, II.2, principal affine opens; Stacks Project, tag 04A9, invariant functions. -/
theorem s2v_l1a_fixedSections_localization_of_finite_family
    {X Y : Scheme} {T : Type*} [Finite T] (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)
    (U : Y.affineOpens) (d : Γ(Y, U.1)) :
    letI : Algebra (s2v_l1a_fixedSectionSubring f a ha U.1)
        (s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)) :=
      (s2v_l1a_fixedSectionRestriction f a ha U.1 (Y.basicOpen d) (Y.basicOpen_le d)).toAlgebra
    IsLocalization.Away (s2v_l1a_baseToFixedSections f a ha U.1 d)
      (s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)) := by
  let R := Γ(X, f ⁻¹ᵁ U.1)
  let A := Γ(X, f ⁻¹ᵁ Y.basicOpen d)
  let res : R ⟶ A := X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le d))).op
  let inst : Algebra R A := res.hom.toAlgebra
  let ρ (t : T) : R →+* R := (s2v_l1a_saturatedSectionEnd f a ha U.1 t).hom
  let σ (t : T) : A →+* A := (s2v_l1a_saturatedSectionEnd f a ha (Y.basicOpen d) t).hom
  let P := s2v_l1a_fixedSectionSubring f a ha U.1
  let Q := s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)
  let : Algebra P Q :=
    (s2v_l1a_fixedSectionRestriction f a ha U.1 (Y.basicOpen d) (Y.basicOpen_le d)).toAlgebra
  have hP (r : R) : r ∈ P ↔ ∀ t, ρ t r = r := s2v_l1a_mem_fixedSectionSubring f a ha U.1 r
  have hQ (s : A) : s ∈ Q ↔ ∀ t, σ t s = s :=
    s2v_l1a_mem_fixedSectionSubring f a ha (Y.basicOpen d) s
  let : IsLocalHom Q.subtype := s2v_l1a_invariant_subring_isLocalHom σ Q hQ
  have hlocal : IsLocalization.Away ((f.app U.1).hom d) A := by
    dsimp +instances [inst, res, A, R]
    rw! (castMode := .all) [f.preimage_basicOpen d]
    exact (U.2.preimage f).isLocalization_basicOpen _
  have hmap (t : T) : (σ t).comp (algebraMap R A) = (algebraMap R A).comp (ρ t) := by
    exact (congrArg CommRingCat.Hom.hom
      (s2v_l1a_saturatedSectionEnd_naturality f a ha U.1 (Y.basicOpen d)
        (Y.basicOpen_le d) t)).symm
  exact s2v_l1a_finite_equalizer_subring_localization ρ σ P Q hP hQ (fun r => rfl)
    ((f.app U.1).hom d) (s2v_l1a_baseToFixedSections f a ha U.1 d).property hmap

/-- Invariant sections of an affine map from an integral scheme localize over every target affine open.
Source: Hartshorne, Algebraic Geometry, II.2, principal affine opens; Stacks Project, tag 04A9, invariant functions. -/
theorem s2v_l1a_fixedSections_localization
    {X Y : Scheme} [AlgebraicGeometry.IsIntegral X] {T : Type*} (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)
    (U : Y.affineOpens) (d : Γ(Y, U.1)) :
    letI : Algebra (s2v_l1a_fixedSectionSubring f a ha U.1)
        (s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)) :=
      (s2v_l1a_fixedSectionRestriction f a ha U.1 (Y.basicOpen d) (Y.basicOpen_le d)).toAlgebra
    IsLocalization.Away (s2v_l1a_baseToFixedSections f a ha U.1 d)
      (s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)) := by
  let P := s2v_l1a_fixedSectionSubring f a ha U.1
  let Q := s2v_l1a_fixedSectionSubring f a ha (Y.basicOpen d)
  let : Algebra P Q :=
    (s2v_l1a_fixedSectionRestriction f a ha U.1 (Y.basicOpen d) (Y.basicOpen_le d)).toAlgebra
  by_cases hV : (f ⁻¹ᵁ U.1 : Set X).Nonempty
  · obtain ⟨x, hx⟩ := hV
    let : Nonempty (f ⁻¹ᵁ U.1) := ⟨⟨x, hx⟩⟩
    exact s2v_l1a_fixedSections_localization_of_domain f a ha U d
  · have hV0 : f ⁻¹ᵁ U.1 = ⊥ :=
      TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.mp hV)
    have hW0 : f ⁻¹ᵁ Y.basicOpen d = ⊥ := by
      apply bot_unique
      exact (f.preimage_mono (Y.basicOpen_le d)).trans hV0.le
    let : Subsingleton Γ(X, f ⁻¹ᵁ U.1) := by rw [hV0]; infer_instance
    let : Subsingleton Γ(X, f ⁻¹ᵁ Y.basicOpen d) := by rw [hW0]; infer_instance
    apply IsLocalization.Away.mk
    · change IsUnit (algebraMap P Q (s2v_l1a_baseToFixedSections f a ha U.1 d))
      rw [Subsingleton.elim (algebraMap P Q (s2v_l1a_baseToFixedSections f a ha U.1 d)) (1 : Q)]
      exact isUnit_one
    · intro s
      exact ⟨0, 0, Subsingleton.elim _ _⟩
    · intro r s _
      exact ⟨0, Subsingleton.elim _ _⟩

/-- The invariant section algebra has the localization compatibility required for relative affine gluing.
Source: Stacks Project, tags 04A9 and 01LH, invariant functions and relative affine gluing. -/
theorem s2v_l1a_fixedSectionStructureMap_coequifibered
    {X Y : Scheme} [AlgebraicGeometry.IsIntegral X] {T : Type*}
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    ((Scheme.AffineZariskiSite.toOpensFunctor Y).op.whiskerLeft
      (s2v_l1a_fixedSectionStructureMap f a ha)).Coequifibered := by
  apply Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr
  intro U d
  exact s2v_l1a_fixedSections_localization f a ha ⟨U.1, U.2⟩ d

/-- The invariant section algebra has the localization compatibility required for relative affine gluing.
Source: Stacks Project, tags 04A9 and 01LH, invariant functions and relative affine gluing. -/
theorem s2v_l1a_finite_fixedSectionStructureMap_coequifibered
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    ((Scheme.AffineZariskiSite.toOpensFunctor Y).op.whiskerLeft
      (s2v_l1a_fixedSectionStructureMap f a ha)).Coequifibered := by
  apply Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr
  intro U d
  exact s2v_l1a_fixedSections_localization_of_finite_family f a ha ⟨U.1, U.2⟩ d

end HodgeLean.Foundations.Program
