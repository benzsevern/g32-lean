import HodgeLean.Foundations.Program.SchoenTowerL1bChartGluing
import HodgeLean.Foundations.Program.SchoenTowerL1bSourceDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bChartCoefficient

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The two binomial charts glue over their coefficient spectrum with the specified reciprocal transition. -/
theorem s2v_l1b_binomial_chart_scheme_transition {R : Type*} [CommRing R] (u v : R) :
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
          Polynomial.C)) ∧
      (let ε := Classical.choose (s2v_l1b_overlap_equiv u v)
       Spec.map (CommRingCat.ofHom
         (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))) ≫ j₁ =
       Spec.map (CommRingCat.ofHom ε.symm.toRingHom) ≫
         Spec.map (CommRingCat.ofHom
           (algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u))) ≫ j₂) := by
  let q₁ := Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})
  let q₂ := Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})
  let l₁ := algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
  let l₂ := algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u)
  let e := Classical.choose (s2v_l1b_overlap_equiv u v)
  have heC := (Classical.choose_spec (s2v_l1b_overlap_equiv u v)).1
  let eS := Scheme.Spec.mapIso e.toCommRingCatIso.op
  let f := Spec.map (CommRingCat.ofHom l₁)
  let g := eS.inv ≫ Spec.map (CommRingCat.ofHom l₂)
  have : IsOpenImmersion f := inferInstance
  have : IsOpenImmersion g := inferInstance
  obtain ⟨X, j₁, j₂, hj₁, hj₂, htransition, hcover, hmap⟩ := s2v_l1b_glue_pair _ _ _ f g
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
  exact ⟨X, j₁, j₂, p, hj₁, hj₂, hcover, hp.1, hp.2, htransition⟩


/-- Affine lifts to opposite charts agree in the model wherever both coefficients are units. -/
theorem s2v_l1b_affine_opposite_lifts_agree {R A D : Type}
    [CommRing R] [CommRing A] [CommRing D] [Algebra A D] [Module.Flat A D]
    (u v : R) (f : R →+* A) (I : Ideal A)
    (hu : f u ∈ I) (hv : f v ∈ I) (e : I ≃ₗ[A] A)
    (huunit : IsUnit (algebraMap A D (e ⟨f u, hu⟩)))
    (hvunit : IsUnit (algebraMap A D (e ⟨f v, hv⟩)))
    (M : Scheme)
    (j₁ : Spec (CommRingCat.of (s2v_L1bChart u v)) ⟶ M)
    (j₂ : Spec (CommRingCat.of (s2v_L1bChart v u)) ⟶ M)
    (htransition :
      let ε := Classical.choose (s2v_l1b_overlap_equiv u v)
      Spec.map (CommRingCat.ofHom
        (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))) ≫ j₁ =
      Spec.map (CommRingCat.ofHom ε.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u))) ≫ j₂)
    (k₁ : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of (s2v_L1bChart u v)))
    (k₂ : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of (s2v_L1bChart v u)))
    (hk₁ : k₁ ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp
        Polynomial.C)) = Spec.map (CommRingCat.ofHom ((algebraMap A D).comp f)))
    (hk₂ : k₂ ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp
        Polynomial.C)) = Spec.map (CommRingCat.ofHom ((algebraMap A D).comp f))) :
    k₁ ≫ j₁ = k₂ ≫ j₂ := by
  let q₁ := Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})
  let q₂ := Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})
  let l₁ := algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
  let l₂ := algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u)
  let ε := Classical.choose (s2v_l1b_overlap_equiv u v)
  have hε := (Classical.choose_spec (s2v_l1b_overlap_equiv u v)).1
  obtain ⟨φ, hφ, _⟩ := s2v_l1b_overlap_lift_flat u v f I hu hv e huunit hvunit
  let a₁ := Spec.map (CommRingCat.ofHom (φ.comp l₁))
  let a₂ := Spec.map (CommRingCat.ofHom ((φ.comp ε.symm.toRingHom).comp l₂))
  have ha₁ : a₁ = k₁ := by
    apply s2v_l1b_affine_chart_hom_ext u v ((algebraMap A D).comp f)
      (s2v_l1b_trivialization_element_flat I e ⟨f v, hv⟩ hvunit) _ _ _ hk₁
    rw [← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) hφ
  have ha₂ : a₂ = k₂ := by
    apply s2v_l1b_affine_chart_hom_ext v u ((algebraMap A D).comp f)
      (s2v_l1b_trivialization_element_flat I e ⟨f u, hu⟩ huunit) _ _ _ hk₂
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change φ (ε.symm (l₂ (q₂ (Polynomial.C a)))) = algebraMap A D (f a)
    have he : ε.symm (l₂ (q₂ (Polynomial.C a))) = l₁ (q₁ (Polynomial.C a)) := by
      rw [← hε a]
      exact ε.symm_apply_apply _
    rw [he]
    exact DFunLike.congr_fun hφ a
  rw [← ha₁, ← ha₂]
  change Spec.map (CommRingCat.ofHom (φ.comp l₁)) ≫ j₁ =
    Spec.map (CommRingCat.ofHom ((φ.comp ε.symm.toRingHom).comp l₂)) ≫ j₂
  change Spec.map (CommRingCat.ofHom l₁ ≫ CommRingCat.ofHom φ) ≫ j₁ =
    Spec.map (CommRingCat.ofHom l₂ ≫
      (CommRingCat.ofHom ε.symm.toRingHom ≫ CommRingCat.ofHom φ)) ≫ j₂
  rw [Spec.map_comp, Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun k => Spec.map (CommRingCat.ofHom φ) ≫ k) htransition

/-- A scheme map to a chart forces the denominator coefficient to be a unit. -/
theorem s2v_l1b_affine_chart_coefficient_unit {R A D : Type}
    [CommRing R] [CommRing A] [CommRing D] [Algebra A D] [Module.Flat A D]
    (u v : R) (f : R →+* A) (I : Ideal A)
    (hu : f u ∈ I) (hv : f v ∈ I) (hI : I = Ideal.span {f u, f v})
    (e : I ≃ₗ[A] A)
    (k : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of (s2v_L1bChart u v)))
    (hk : k ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp
        Polynomial.C)) = Spec.map (CommRingCat.ofHom ((algebraMap A D).comp f))) :
    IsUnit (algebraMap A D (e ⟨f v, hv⟩)) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective k
  rw [← Spec.map_comp] at hk
  exact s2v_l1b_chart_map_coefficient_unit u v f I hu hv hI e φ.hom
    (congrArg (fun h => h.hom) (Spec.map_injective hk))

end HodgeLean.Foundations.Program
