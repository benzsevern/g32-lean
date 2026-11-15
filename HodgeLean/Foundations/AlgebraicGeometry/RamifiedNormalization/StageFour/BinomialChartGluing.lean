import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.TwoChartGluing
import HodgeLean.Foundations.Program.SchoenTowerL1bOverlapDescent

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The two binomial chart images meet exactly along their reciprocal-coordinate overlap. -/
theorem binomial_model_chart_intersection {R : Type*} [CommRing R] (u v : R) :
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
           (algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u))) ≫ j₂) ∧
      (let ε := Classical.choose (s2v_l1b_overlap_equiv u v)
       ∀ a b, j₁ a = j₂ b ↔ ∃ z : Spec (CommRingCat.of (s2v_L1bOverlap u v)),
         Spec.map (CommRingCat.ofHom (algebraMap (s2v_L1bChart u v)
           (s2v_L1bOverlap u v))) z = a ∧
         (Spec.map (CommRingCat.ofHom ε.symm.toRingHom) ≫
           Spec.map (CommRingCat.ofHom (algebraMap (s2v_L1bChart v u)
             (s2v_L1bOverlap v u)))) z = b) := by
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
  obtain ⟨X, j₁, j₂, hj₁, hj₂, htransition, hcover, hintersection, hmap⟩ := two_open_chart_gluing _ _ _ f g
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
  exact ⟨X, j₁, j₂, p, hj₁, hj₂, hcover, hp.1, hp.2, htransition, hintersection⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
