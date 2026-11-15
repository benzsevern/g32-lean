import HodgeLean.Foundations.Program.SchoenTowerL1bLocalLifts
import HodgeLean.Foundations.Program.SchoenTowerL1bAffineIdeal
import HodgeLean.Foundations.Program.SchoenTowerL1bChartRegularity

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- A ring isomorphism transports the regular principal presentation of an ideal. -/
theorem s2v_l1b_regular_pair_transport {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (u v s : A) (h : u = s * v) (hv : IsRegular v) :
    Nonempty ((Ideal.span {e u, e v}) ≃ₗ[B] B) := by
  have hev : IsRegular (e v) := by
    apply (Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr
    intro a b hab
    apply e.symm.injective
    apply hv.left
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hab
  have heq : Ideal.span {e u, e v} = Ideal.span {e v} := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | rfl
      · rw [h, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
      · exact Ideal.subset_span (Set.mem_singleton _)
    · exact Ideal.span_mono (by intro x hx; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mp hx)))
  rw [heq]
  obtain ⟨t, _⟩ := s2v_l1b_regular_principal_trivialization (e v) hev
  exact ⟨t⟩

/-- The binomial chart has an invertible actual pulled back centre ideal on its affine spectrum. -/
theorem s2v_l1b_chart_spectrum_trivialization {R : Type*} [CommRing R]
    (u v : R) (hv : IsRegular v)
    (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (I : (Spec (CommRingCat.of R)).IdealSheafData)
    (hI : I.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u,
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom v}) :
    let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    let f := Spec.map (CommRingCat.ofHom (q.comp C))
    Nonempty (((I.comap f).ideal ⟨⊤, isAffineOpen_top _⟩) ≃ₗ[Γ(Spec (CommRingCat.of (s2v_L1bChart u v)), ⊤)]
      Γ(Spec (CommRingCat.of (s2v_L1bChart u v)), ⊤)) := by
  dsimp only
  let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
  let f := Spec.map (CommRingCat.ofHom (q.comp C))
  let e := (Scheme.ΓSpecIso (CommRingCat.of (s2v_L1bChart u v))).symm.commRingCatIsoToRingEquiv
  have hn (a : R) :
      f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = e (q (C a)) := by
    have hh := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (q.comp C))
    exact (congrArg (fun k => k.hom a) hh).symm
  rw [s2v_l1b_affine_ideal_comap_pair f I _ _ hI, hn u, hn v]
  exact s2v_l1b_regular_pair_transport e (q (C u)) (q (C v)) (q X)
    (s2v_l1b_chart_relation u v) (s2v_l1b_chart_denominator_regular u v hv hu)

/-- An ideal module trivialization transports to the extended ideal along a ring isomorphism. -/
theorem s2v_l1b_ideal_trivialization_transport {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (t : I ≃ₗ[A] A) :
    Nonempty ((I.map e.toRingHom) ≃ₗ[B] B) := by
  let g : A := (t.symm 1).val
  obtain ⟨hg, hgen⟩ := s2v_l1b_trivialization_generator I t
  have hI : I = Ideal.span {g} := by
    apply le_antisymm
    · intro a ha
      exact Ideal.mem_span_singleton'.mpr ⟨t ⟨a, ha⟩, (hgen ⟨a, ha⟩).symm⟩
    · exact Ideal.span_le.mpr (by intro a ha; obtain rfl := Set.mem_singleton_iff.mp ha; exact (t.symm 1).property)
  rw [hI, Ideal.map_span, Set.image_singleton]
  have hp := s2v_l1b_regular_pair_transport e g g 1 (one_mul g).symm hg
  rw [Set.insert_eq_of_mem (Set.mem_singleton _)] at hp
  exact hp

/-- Freeness on an affine open immersion transports to its actual affine image. -/
theorem s2v_l1b_open_image_trivialization {A X : Scheme} [IsAffine A]
    (j : A ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData)
    (h : Nonempty (((I.comap j).ideal ⟨⊤, isAffineOpen_top A⟩) ≃ₗ[Γ(A, ⊤)] Γ(A, ⊤))) :
    Nonempty ((I.ideal ⟨j ''ᵁ ⊤, (isAffineOpen_top A).image_of_isOpenImmersion j⟩)
      ≃ₗ[Γ(X, j ''ᵁ ⊤)] Γ(X, j ''ᵁ ⊤)) := by
  obtain ⟨t⟩ := h
  let e := (j.appIso ⊤).symm.commRingCatIsoToRingEquiv
  have ht := s2v_l1b_ideal_trivialization_transport e _ t
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at ht
  change Nonempty (((I.ideal ⟨j ''ᵁ ⊤, _⟩).comap e.toRingHom).map e.toRingHom ≃ₗ[_] _) at ht
  obtain ⟨k⟩ := ht
  have heq := Ideal.map_comap_of_surjective e.toRingHom e.surjective
    (I.ideal ⟨j ''ᵁ ⊤, (isAffineOpen_top A).image_of_isOpenImmersion j⟩)
  exact ⟨(LinearEquiv.ofEq _ _ heq.symm).trans k⟩

/-- A chart presentation transports through a ring isomorphism with its exact polynomial kernel. -/
theorem s2v_l1b_chart_presentation_transport {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (e : s2v_L1bChart u v ≃+* A) :
    let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    Function.Surjective (eval₂RingHom (e.toRingHom.comp (q.comp C)) (e (q X))) ∧
      RingHom.ker (eval₂RingHom (e.toRingHom.comp (q.comp C)) (e (q X))) =
        Ideal.span {C u - X * C v} := by
  dsimp only
  let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
  have he : eval₂RingHom (e.toRingHom.comp (q.comp C)) (e (q X)) =
      e.toRingHom.comp q := by
    apply Polynomial.ringHom_ext
    · intro a
      exact eval₂_C _ _
    · exact eval₂_X _ _
  rw [he]
  exact ⟨e.surjective.comp Ideal.Quotient.mk_surjective,
    (RingHom.ker_comp_of_injective q e.injective).trans (Ideal.mk_ker)⟩

end HodgeLean.Foundations.Program
