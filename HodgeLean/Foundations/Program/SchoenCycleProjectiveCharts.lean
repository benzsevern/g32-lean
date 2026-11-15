import HodgeLean.Foundations.Program.SchoenCycleS2bDefs
import HodgeLean.Foundations.SegreProjectiveProofs
import HodgeLean.Foundations.Program.SchoenCycleS2
import Mathlib.RingTheory.TensorProduct.MvPolynomial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial HomogeneousLocalization
open scoped BigOperators TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Normalization of the integral chart, before extension to complex scalars.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; standard projective coordinates. -/
def s2e_integralChartHom {k : ℕ} (i : Fin (k + 1)) :
    Away (UniversalGrading k) (X i) →+* MvPolynomial {j : Fin (k + 1) // j ≠ i} (ULift ℤ) :=
  (Localization.awayLift
    (eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)) (X i)
    (by simp)).comp (algebraMap _ (Localization.Away (X i : UniversalRing k)))

/-- Integral normalized coordinates take the denominator to one.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_integralChartHom_coordinate {k : ℕ} (i j : Fin (k + 1)) :
    s2e_integralChartHom i (chartCoordinate i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  let F : UniversalRing k →+* MvPolynomial {j : Fin (k + 1) // j ≠ i} (ULift ℤ) :=
    eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)
  change (Localization.awayLift F (X i : UniversalRing k) (by simp [F]))
    (Localization.mk (X j) ⟨X i ^ 1, ⟨1, rfl⟩⟩) = _
  rw [Localization.awayLift_mk F (X i) (X j) 1 (by simp [F]) 1]
  simp [F]

/-- Integral chart maps are determined by the homogeneous coordinate ratios.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_integralChart_ext {k : ℕ} (i : Fin (k + 1)) {R : Type} [CommRing R]
    (f g : Away (UniversalGrading k) (X i) →+* R)
    (hc : ∀ j, f (chartCoordinate i j) = g (chartCoordinate i j)) : f = g := by
  have hb : ∀ a : UniversalGrading k 0,
      f (fromZeroRingHom (UniversalGrading k) (.powers (X i)) a) =
      g (fromZeroRingHom (UniversalGrading k) (.powers (X i)) a) := by
    intro a
    obtain ⟨c, rfl⟩ := (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) (ULift ℤ)).symm.surjective a
    have hcast : c = ((c.down : ℤ) : ULift ℤ) := by ext; rfl
    rw [hcast]
    change (f.comp ((fromZeroRingHom (UniversalGrading k) (.powers (X i))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) (ULift ℤ)).symm.toRingHom)) (c.down : ℤ) =
      (g.comp ((fromZeroRingHom (UniversalGrading k) (.powers (X i))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) (ULift ℤ)).symm.toRingHom)) (c.down : ℤ)
    rw [map_intCast, map_intCast]
  letI : Algebra (UniversalGrading k 0) R :=
    (f.comp (fromZeroRingHom (UniversalGrading k) (.powers (X i)))).toAlgebra
  let fa : Away (UniversalGrading k) (X i) →ₐ[UniversalGrading k 0] R :=
    { f with commutes' := fun _ => rfl }
  let ga : Away (UniversalGrading k) (X i) →ₐ[UniversalGrading k 0] R :=
    { g with commutes' := fun r => (hb r).symm }
  change fa.toRingHom = ga.toRingHom
  apply congrArg AlgHom.toRingHom
  apply AlgHom.ext_of_adjoin_eq_top
    (Away.adjoin_mk_prod_pow_eq_top (isHomogeneous_X (ULift ℤ) i)
      (Fin (k + 1)) (fun j => X j) (adjoin_coordinates_eq_top k)
      (fun _ => (1 : ℕ)) (fun j => isHomogeneous_X (ULift ℤ) j))
  rintro z ⟨a, ai, hai, _, rfl⟩
  have hai' : ∑ j, ai j = a := by simpa using hai
  rw [chartGenerator_eq_prod i ai hai']
  simp only [map_prod, map_pow]
  exact Finset.prod_congr rfl (fun j _ => congrArg (fun x : R => x ^ ai j) (hc j))

/-- The integral chart ring is a polynomial ring on the non-denominator coordinates.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_integralChartEquiv {k : ℕ} (i : Fin (k + 1)) :
    Away (UniversalGrading k) (X i) ≃+* MvPolynomial {j : Fin (k + 1) // j ≠ i} (ULift ℤ) := by
  let g : MvPolynomial {j : Fin (k + 1) // j ≠ i} (ULift ℤ) →+*
      Away (UniversalGrading k) (X i) :=
    eval₂Hom ((fromZeroRingHom (UniversalGrading k) (.powers (X i))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) (ULift ℤ)).symm.toRingHom)
      (fun j => chartCoordinate i j.val)
  refine RingEquiv.ofRingHom (s2e_integralChartHom i) g ?_ ?_
  · apply MvPolynomial.ringHom_ext
    · intro c
      have hcast : c = ((c.down : ℤ) : ULift ℤ) := by ext; rfl
      rw [hcast]
      simp only [RingHom.comp_apply, g, eval₂Hom_C, RingHom.coe_comp, Function.comp_apply,
        map_intCast]
    · intro j
      simp only [RingHom.comp_apply, g, eval₂Hom_X', s2e_integralChartHom_coordinate,
        dite_eq_right j.property, RingHom.id_apply]
  · apply s2e_integralChart_ext i
    intro j
    simp only [RingHom.comp_apply, s2e_integralChartHom_coordinate, RingHom.id_apply]
    split_ifs with hj
    · subst j
      rw [map_one, chartCoordinate_self]
    · exact eval₂Hom_X' _ _ _

/-- Scalar extension of the normalized integral chart.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_complexChartRingEquiv {k : ℕ} (i : Fin (k + 1)) :
    ℂ ⊗[ℤ] Away (UniversalGrading k) (X i) ≃ₐ[ℂ]
      MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ)
    ((s2e_integralChartEquiv i).trans
      (MvPolynomial.mapEquiv _ ULift.ringEquiv)).toIntAlgEquiv).trans
    (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ)

/-- The complex chart isomorphism retains the specified coordinate ratios.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_complexChartRingEquiv_coordinate {k : ℕ} (i j : Fin (k + 1)) :
    s2e_complexChartRingEquiv i (1 ⊗ₜ[ℤ] chartCoordinate i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  simp only [s2e_complexChartRingEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  change (1 : ℂ) • MvPolynomial.map (algebraMap ℤ ℂ)
    (MvPolynomial.map ULift.ringEquiv.toRingHom
      (s2e_integralChartHom i (chartCoordinate i j))) = _
  rw [one_smul, s2e_integralChartHom_coordinate]
  split_ifs <;> simp

/-- The frozen chart homomorphism evaluates each ratio in normalized coordinates.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chartHom_coordinate {k : ℕ} (i j : Fin (k + 1)) :
    s2e_s2b_chartHom i (chartCoordinate i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  classical
  simp only [s2e_s2b_chartHom, RingHom.comp_apply,
    chartAwayPolynomialHom_chartCoordinate]
  split_ifs with h <;> simp [h]

/-- The scalar-extended chart map agrees with the specified normalized chart map.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_complexChartRingEquiv_includeRight {k : ℕ} (i : Fin (k + 1)) :
    (s2e_complexChartRingEquiv i).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ)).toRingHom =
        s2e_s2b_chartHom i := by
  apply s2e_integralChart_ext i
  intro j
  exact (s2e_complexChartRingEquiv_coordinate i j).trans
    (s2e_chartHom_coordinate i j).symm

/-- The affine pullback chart has the normalized polynomial coordinates.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_projectiveChartIso {k : ℕ} (i : Fin (k + 1)) :
    Spec ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ) ≅
      pullback (terminal.from (Spec ↧ℂ))
        (terminal.from (Spec ↧(Away (UniversalGrading k) (X i)))) :=
  let e := terminalIsTerminal.uniqueUpToIso specZIsTerminal
  (Scheme.Spec.mapIso (s2e_complexChartRingEquiv i).toRingEquiv.toCommRingCatIso.op) ≪≫
    (pullbackSpecIso ℤ ℂ (Away (UniversalGrading k) (X i))).symm ≪≫
    (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) e.hom
      (specZIsTerminal.hom_ext _ _) (specZIsTerminal.hom_ext _ _))).symm


/-- The base-change chart isomorphism preserves the projection to the coefficient field.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_projectiveChartIso_fst {k : ℕ} (i : Fin (k + 1)) :
    (s2e_projectiveChartIso i).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (C : ℂ →+* _)) := by
  let e := terminalIsTerminal.uniqueUpToIso specZIsTerminal
  let u := pullback.map (terminal.from (Spec ↧ℂ))
    (terminal.from (Spec ↧(Away (UniversalGrading k) (X i))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Away (UniversalGrading k) (X i)))))
    (𝟙 _) (𝟙 _) e.hom (specZIsTerminal.hom_ext _ _) (specZIsTerminal.hom_ext _ _)
  have hu : inv u ≫ pullback.fst _ _ = pullback.fst _ _ := by
    apply (IsIso.inv_comp_eq u).mpr
    simp only [u, pullback.map, pullback.lift_fst, Category.comp_id]
  change Spec.map _ ≫ (pullbackSpecIso ℤ ℂ _).inv ≫ inv u ≫ pullback.fst _ _ = _
  rw [hu, pullbackSpecIso_inv_fst', ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (s2e_complexChartRingEquiv i).commutes

/-- The base-change chart isomorphism preserves the specified homogeneous-ratio map.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_projectiveChartIso_snd {k : ℕ} (i : Fin (k + 1)) :
    (s2e_projectiveChartIso i).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (s2e_s2b_chartHom i)) := by
  let e := terminalIsTerminal.uniqueUpToIso specZIsTerminal
  let u := pullback.map (terminal.from (Spec ↧ℂ))
    (terminal.from (Spec ↧(Away (UniversalGrading k) (X i))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Away (UniversalGrading k) (X i)))))
    (𝟙 _) (𝟙 _) e.hom (specZIsTerminal.hom_ext _ _) (specZIsTerminal.hom_ext _ _)
  have hu : inv u ≫ pullback.snd _ _ = pullback.snd _ _ := by
    apply (IsIso.inv_comp_eq u).mpr
    simp only [u, pullback.map, pullback.lift_snd, Category.comp_id]
  change Spec.map _ ≫ (pullbackSpecIso ℤ ℂ _).inv ≫ inv u ≫ pullback.snd _ _ = _
  rw [hu, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact s2e_complexChartRingEquiv_includeRight i

end HodgeLean.Foundations.Program
