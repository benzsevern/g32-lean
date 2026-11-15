import HodgeLean.Foundations.Program.SchoenTowerL1bLocalLifts
import HodgeLean.Foundations.Program.SchoenTowerL1bAffineIdeal
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program
universe u

/-- A trivialized pulled back ideal gives a unique morphism into a binomial chart where its second
coefficient is invertible, after flat base change on the source. -/
theorem s2v_l1b_affine_chart_lift {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (u v : R) (f : R →+* A)
    (I : Ideal A) (hu : f u ∈ I) (hv : f v ∈ I) (e : I ≃ₗ[A] A)
    (hvunit : IsUnit (algebraMap A B (e ⟨f v, hv⟩))) :
    ∃! k : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (s2v_L1bChart u v)),
      k ≫ Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {C u - Polynomial.X * C v})).comp C)) =
      Spec.map (CommRingCat.ofHom ((algebraMap A B).comp f)) := by
  obtain ⟨φ, hφ, huniq⟩ := s2v_l1b_chart_lift_flat u v f I hu hv e hvunit
  refine ⟨Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · dsimp only
    rw [← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) hφ
  · intro k hk
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective k
    rw [← Spec.map_comp] at hk
    have hψ := Spec.map_injective hk
    have hψ' : ψ.hom.comp
        ((Ideal.Quotient.mk (Ideal.span {C u - Polynomial.X * C v})).comp C) =
          (algebraMap A B).comp f := congrArg (fun h => h.hom) hψ
    have heq := huniq ψ.hom hψ'
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) heq

/-- A trivialized actual pullback ideal supplies the coefficient cover and chart lifts for its
actual restricted section map. -/
theorem s2v_l1b_actual_local_chart_cover {X Y : Scheme} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (U : Y.affineOpens) (V : X.affineOpens)
    (h : V.1 ≤ f ⁻¹ᵁ U.1) (u v : Γ(Y, U))
    (hI : I.ideal U = Ideal.span {u, v})
    (e : (I.comap f).ideal V ≃ₗ[Γ(X, V)] Γ(X, V)) :
    let a := (f.appLE U.1 V.1 h).hom
    ∃ (hu : a u ∈ (I.comap f).ideal V) (hv : a v ∈ (I.comap f).ideal V),
      PrimeSpectrum.basicOpen (e ⟨a u, hu⟩) ⊔ PrimeSpectrum.basicOpen (e ⟨a v, hv⟩) = ⊤ ∧
      (∃! φ : s2v_L1bChart u v →+* Localization.Away (e ⟨a v, hv⟩),
        φ.comp ((Ideal.Quotient.mk (Ideal.span {C u - Polynomial.X * C v})).comp C) =
          (algebraMap Γ(X, V) (Localization.Away (e ⟨a v, hv⟩))).comp a) ∧
      (∃! ψ : s2v_L1bChart v u →+* Localization.Away (e ⟨a u, hu⟩),
        ψ.comp ((Ideal.Quotient.mk (Ideal.span {C v - Polynomial.X * C u})).comp C) =
          (algebraMap Γ(X, V) (Localization.Away (e ⟨a u, hu⟩))).comp a) := by
  dsimp only
  let a := (f.appLE U.1 V.1 h).hom
  have hJ : (I.comap f).ideal V = Ideal.span {a u, a v} := by
    rw [s2v_l1b_comap_ideal_affine_charts f I U V h, hI, Ideal.map_span, Set.image_pair]
  have hu : a u ∈ (I.comap f).ideal V := by
    rw [hJ]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hv : a v ∈ (I.comap f).ideal V := by
    rw [hJ]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact ⟨hu, hv, s2v_l1b_coefficient_local_chart_cover u v a _ hu hv hJ e⟩

end HodgeLean.Foundations.Program
