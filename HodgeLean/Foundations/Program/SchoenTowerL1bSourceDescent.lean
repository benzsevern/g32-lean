import HodgeLean.Foundations.Program.SchoenTowerL1bLocalMorphisms
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program
universe u

/-- Over a regular denominator, two affine chart morphisms with the same base map coincide. -/
theorem s2v_l1b_affine_chart_hom_ext {R A : Type u} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (hv : IsRegular (f v))
    (k l : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (s2v_L1bChart u v)))
    (hk : k ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {C u - Polynomial.X * C v})).comp C)) =
      Spec.map (CommRingCat.ofHom f))
    (hl : l ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {C u - Polynomial.X * C v})).comp C)) =
      Spec.map (CommRingCat.ofHom f)) : k = l := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective k
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective l
  rw [← Spec.map_comp] at hk hl
  have hφ := congrArg (fun h => h.hom) (Spec.map_injective hk)
  have hψ := congrArg (fun h => h.hom) (Spec.map_injective hl)
  have heq := s2v_l1b_chart_hom_ext_regular u v f hv φ.hom ψ.hom hφ hψ
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) heq

/-- Local lifts glue uniquely when lifts on each pairwise source intersection are unique. -/
theorem s2v_l1b_source_cover_lift {T X B : Scheme} (p : X ⟶ B) (f : T ⟶ B)
    (𝒰 : T.OpenCover)
    (hlocal : ∀ a, ∃! k : 𝒰.X a ⟶ X, k ≫ p = 𝒰.f a ≫ f)
    (hinter : ∀ a b (k l : pullback (𝒰.f a) (𝒰.f b) ⟶ X),
      k ≫ p = pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a ≫ f →
      l ≫ p = pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a ≫ f → k = l) :
    ∃! k : T ⟶ X, k ≫ p = f := by
  choose k hk huniq using hlocal
  have hcompat : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ k a =
      pullback.snd (𝒰.f a) (𝒰.f b) ≫ k b := by
    intro a b
    apply hinter a b
    · rw [Category.assoc, hk]
    · rw [Category.assoc, hk, ← Category.assoc, ← pullback.condition, Category.assoc]
  refine ⟨𝒰.glueMorphisms k hcompat, ?_, ?_⟩
  · apply 𝒰.hom_ext
    intro a
    rw [← Category.assoc, 𝒰.ι_glueMorphisms]
    exact hk a
  · intro l hl
    apply 𝒰.hom_ext
    intro a
    rw [𝒰.ι_glueMorphisms]
    apply huniq a
    rw [Category.assoc, hl]

/-- Inverting both ideal coefficients gives a unique affine morphism to the reciprocal overlap. -/
theorem s2v_l1b_affine_overlap_lift {R A D : Type u}
    [CommRing R] [CommRing A] [CommRing D] [Algebra A D] [Module.Flat A D]
    (u v : R) (f : R →+* A) (I : Ideal A)
    (hu : f u ∈ I) (hv : f v ∈ I) (e : I ≃ₗ[A] A)
    (huunit : IsUnit (algebraMap A D (e ⟨f u, hu⟩)))
    (hvunit : IsUnit (algebraMap A D (e ⟨f v, hv⟩))) :
    ∃! k : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of (s2v_L1bOverlap u v)),
      k ≫ Spec.map (CommRingCat.ofHom
        (((algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)).comp
          (Ideal.Quotient.mk (Ideal.span {C u - Polynomial.X * C v}))).comp C)) =
      Spec.map (CommRingCat.ofHom ((algebraMap A D).comp f)) := by
  obtain ⟨φ, hφ, huniq⟩ := s2v_l1b_overlap_lift_flat u v f I hu hv e huunit hvunit
  refine ⟨Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · dsimp only
    rw [← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) hφ
  · intro k hk
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective k
    rw [← Spec.map_comp] at hk
    have hψ := congrArg (fun h => h.hom) (Spec.map_injective hk)
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (huniq ψ.hom hψ)

end HodgeLean.Foundations.Program
