import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Defs
import HodgeLean.Foundations.Curves.CubicSmooth

/-! # Independent symmetric curve tests

Affine spectra, insertion maps and coordinate ideals are tested without importing
any stage two interface. Numeric coordinates have explicit finite index types.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 50000

private instance affine_isAffine (n : ℕ) : IsAffine (affine n).left := by
  change IsAffine (Spec ↧(MvPolynomial (Fin n) ℂ)); infer_instance

private def point (n : ℕ) (a : Fin n → ℂ) : ComplexPoint (affine n) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (MvPolynomial.eval a))) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    ext r
    simp)

private theorem point_value (n : ℕ) (a : Fin n → ℂ) (i : Fin n) :
    coordinateValue n (point n a) i = a i := by
  change ((Spec.map (CommRingCat.ofHom (MvPolynomial.eval a))).appTop ≫
    (Scheme.ΓSpecIso ↧ℂ).hom)
      ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin n) ℂ)).inv (MvPolynomial.X i)) = a i
  rw [Scheme.ΓSpecIso_naturality]
  simp

private theorem points_ne : point 1 (fun _ => (0 : ℂ)) ≠ point 1 (fun _ => (1 : ℂ)) := by
  intro h
  have H := congrArg (fun p => coordinateValue 1 p (0 : Fin 1)) h
  rw [point_value, point_value] at H
  exact zero_ne_one H

-- Perturbing the retained projection changes a nonzero affine point.
private theorem retained_comparison_falsification :
    (point 1 (fun _ => (0 : ℂ))).left ≠ (point 1 (fun _ => (1 : ℂ))).left := by
  intro h
  exact points_ne (Over.OverMorphism.ext h)

example : coordinateValue 1 (point 1 (fun _ => (3 : ℂ))) (0 : Fin 1) = 3 :=
  point_value _ _ _

-- Relative coordinates cannot be truncated to a singleton in positive degree.
private theorem affine_positive_dimension_test :
    ¬ Subsingleton (ComplexPoint (affine 1)) := by
  intro h
  exact points_ne (h.elim _ _)

example : ¬ Subsingleton (ComplexPoint (affine 1)) := affine_positive_dimension_test

-- Degree one cannot replace degree zero's single point.
private theorem degree_zero_falsification :
    ¬ ∀ p q : ComplexPoint (affine 1), p = q := by
  intro h
  exact points_ne (h _ _)

example : ¬ ∀ p q : ComplexPoint (affine 1), p = q := degree_zero_falsification

private theorem coordinateIdeals_ne : coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (1 : Fin 2) := by
  intro h
  have H := congrArg (fun I => Scheme.IdealSheafData.equivOfIsAffine I) h
  change Scheme.IdealSheafData.equivOfIsAffine
      (Scheme.IdealSheafData.equivOfIsAffine.symm _) =
    Scheme.IdealSheafData.equivOfIsAffine
      (Scheme.IdealSheafData.equivOfIsAffine.symm _) at H
  simp only [Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply] at H
  let e := Scheme.ΓSpecIso ↧(MvPolynomial (Fin 2) ℂ)
  change Ideal.span {e.inv (MvPolynomial.X (0 : Fin 2))} =
    Ideal.span {e.inv (MvPolynomial.X (1 : Fin 2))} at H
  have hm : e.inv (MvPolynomial.X (0 : Fin 2)) ∈ Ideal.span
      {e.inv (MvPolynomial.X (1 : Fin 2))} := by
    rw [← H]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hm
  have he := congrArg (fun r => MvPolynomial.eval (![1, 0] : Fin 2 → ℂ) (e.hom r)) hq
  simp [e, map_mul] at he

-- Duplicating a branch cannot give two different coordinate hyperplanes.
private theorem branch_coordinates_falsification :
    ¬ ∃ I : (affine 2).left.IdealSheafData,
      I = coordinateIdeal 2 (0 : Fin 2) ∧ I = coordinateIdeal 2 (1 : Fin 2) := by
  rintro ⟨I, h0, h1⟩
  exact coordinateIdeals_ne (h0.symm.trans h1)

example : coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (1 : Fin 2) := coordinateIdeals_ne

private def L := affine 1
private def p : ComplexPoint L := point 1 (fun _ => (0 : ℂ))
private def q : ComplexPoint L := point 1 (fun _ => (1 : ℂ))

private theorem point_addition_positive :
    s2c_branchInsertion L 1 p ≫ g3_proj L 2 (1 : Fin 2) = g3_proj L 1 (0 : Fin 1) := by
  rw [s2c_branchInsertion, s2_check_lift_proj]
  rfl

private theorem point_addition_falsification : s2c_branchInsertion L 1 p ≠ s2c_branchInsertion L 1 q := by
  intro h
  have H := congrArg (fun f => s2_lift 1 (![q] : Fin 1 → ComplexPoint L) ≫ f ≫ g3_proj L 2 (0 : Fin 2)) h
  simp only [s2c_branchInsertion, s2_check_lift_proj, Fin.cases_zero] at H
  have ht : s2_lift 1 (![q] : Fin 1 → ComplexPoint L) ≫
      CartesianMonoidalCategory.toUnit (g3_power L 1) = 𝟙 _ := Subsingleton.elim _ _
  rw [← Category.assoc, ← Category.assoc, ht, Category.id_comp, Category.id_comp] at H
  exact points_ne H

example : s2c_branchInsertion L 1 p ≠ s2c_branchInsertion L 1 q := point_addition_falsification

-- The sum of two copies retains one ideal; distinctness is essential.
private theorem branch_intersections_falsification :
    coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (0 : Fin 2) ≠
      coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (1 : Fin 2) := by
  rw [sup_idem]
  intro h
  have hi : coordinateIdeal 2 (1 : Fin 2) ≤ coordinateIdeal 2 (0 : Fin 2) := by
    rw [h]; exact le_sup_right
  have H := Scheme.IdealSheafData.equivOfIsAffine.toOrderIso.monotone hi
  change Scheme.IdealSheafData.equivOfIsAffine
      (Scheme.IdealSheafData.equivOfIsAffine.symm _) ≤
    Scheme.IdealSheafData.equivOfIsAffine
      (Scheme.IdealSheafData.equivOfIsAffine.symm _) at H
  simp only [Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply] at H
  let e := Scheme.ΓSpecIso ↧(MvPolynomial (Fin 2) ℂ)
  change Ideal.span {e.inv (MvPolynomial.X (1 : Fin 2))} ≤
    Ideal.span {e.inv (MvPolynomial.X (0 : Fin 2))} at H
  have hy := H (Ideal.subset_span (Set.mem_singleton (e.inv (MvPolynomial.X (1 : Fin 2)))))
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hy
  have he := congrArg (fun s => MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) (e.hom s)) hr
  simp [e] at he

example : coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (0 : Fin 2) =
    coordinateIdeal 2 (0 : Fin 2) := sup_idem _

private theorem branch_support :
    ∃ x : (symmetricPower E 1).left,
      x ∈ (branchIdeal E 0 (Over.homMk finitePoint finitePoint_over)).support := by
  let b : ComplexPoint E := Over.homMk finitePoint finitePoint_over
  let f := s2c_branchInsertion E 0 b ≫ projection E 1
  let y : (g3_power E 0).left := by change Spec ↧ℂ; exact default
  exact ⟨f.left y, f.left.range_subset_ker_support ⟨_, rfl⟩⟩

private theorem excess_branches_falsification :
    Nonempty (branchIntersection E 0 2
      (fun _ => Over.homMk finitePoint finitePoint_over)).left := by
  let b : ComplexPoint E := Over.homMk finitePoint finitePoint_over
  have he : intersectionIdeal E 0 2 (fun _ => b) = branchIdeal E 0 b := by
    simp only [intersectionIdeal, iSup_const]
  obtain ⟨x, hx⟩ := branch_support
  have hm : x ∈ (intersectionIdeal E 0 2 (fun _ => b)).support := by rw [he]; exact hx
  change x ∈ ((intersectionIdeal E 0 2 (fun _ => b)).support : Set _) at hm
  rw [← Scheme.IdealSheafData.range_subschemeι] at hm
  obtain ⟨y, _⟩ := hm
  exact ⟨y⟩

example : Nonempty (branchIntersection E 0 2
    (fun _ => Over.homMk finitePoint finitePoint_over)).left := excess_branches_falsification

-- Repeated coordinates have a nontrivial stabilizer; they must not be excluded.
private theorem curve_coordinate_transport_falsification :
    ∃ z : Fin 2 → ComplexPoint (affine 1),
      z ∘ Equiv.swap (0 : Fin 2) 1 = z ∧ Equiv.swap (0 : Fin 2) 1 ≠ Equiv.refl _ := by
  refine ⟨fun _ => p, rfl, ?_⟩
  intro h
  have H := congrArg (fun σ : Equiv.Perm (Fin 2) => σ 0) h
  norm_num at H

example : coordinateValue 1 (point 1 (fun _ => (2 : ℂ))) 0 = 2 := point_value _ _ _

private theorem descendOne (T : Over (Spec ↧ℂ)) (f : g3_power E 1 ⟶ T) :
    ∃! d : symmetricPower E 1 ⟶ T, projection E 1 ≫ d = f := by
  apply s2_gluedQuotientOverDesc_arbitrary
  intro σ
  have hσ : σ = (1 : Equiv.Perm (Fin 1)) := Subsingleton.elim _ _
  subst σ
  rw [map_one]
  simp

private def oneIso : g3_power E 1 ≅ symmetricPower E 1 := by
  let d := Classical.choose (descendOne (g3_power E 1) (𝟙 _))
  have hd := (Classical.choose_spec (descendOne (g3_power E 1) (𝟙 _))).1
  refine ⟨projection E 1, d, hd, ?_⟩
  obtain ⟨k, hk, hu⟩ := descendOne (symmetricPower E 1) (projection E 1)
  apply (hu _ ?_).trans (hu (𝟙 _) (by simp)).symm
  rw [← Category.assoc, hd]
  simp

private def curveIso : g3_power E 1 ≅ E := MonoidalCategory.rightUnitor E

private theorem krull_dimension_positive :
    topologicalKrullDim (symmetricPower E 1).left = 1 := by
  let e := ((Over.forget (Spec ↧ℂ)).mapIso oneIso).symm ≪≫
    (Over.forget (Spec ↧ℂ)).mapIso curveIso
  change topologicalKrullDim ((Over.forget (Spec ↧ℂ)).obj (symmetricPower E 1)) = 1
  rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim]
  exact SmoothOfRelativeDimension.orderKrullDim_eq_complex (f := E.hom) (d := 1)

example : topologicalKrullDim (symmetricPower E 1).left = 1 := krull_dimension_positive

private theorem krull_dimension_falsification :
    topologicalKrullDim (symmetricPower E 1).left ≠ 2 := by
  rw [krull_dimension_positive]
  norm_num

private theorem smooth_dimension_falsification :
    topologicalKrullDim (symmetricPower E 1).left ≠ 0 := by
  rw [krull_dimension_positive]
  norm_num

example : topologicalKrullDim (symmetricPower E 1).left ≠ 0 := smooth_dimension_falsification

private theorem descendZero (T : Over (Spec ↧ℂ)) (f : g3_power E 0 ⟶ T) :
    ∃! d : symmetricPower E 0 ⟶ T, projection E 0 ≫ d = f := by
  apply s2_gluedQuotientOverDesc_arbitrary
  intro σ
  have hσ : σ = (1 : Equiv.Perm (Fin 0)) := Subsingleton.elim _ _
  subst σ
  rw [map_one]
  simp only [Aut.one_asIso, Iso.refl_hom, Category.id_comp]

private def zeroIso : g3_power E 0 ≅ symmetricPower E 0 := by
  let d := Classical.choose (descendZero (g3_power E 0) (𝟙 _))
  have hd := (Classical.choose_spec (descendZero (g3_power E 0) (𝟙 _))).1
  refine ⟨projection E 0, d, hd, ?_⟩
  obtain ⟨k, hk, hu⟩ := descendZero (symmetricPower E 0) (projection E 0)
  apply (hu _ ?_).trans (hu (𝟙 _) (by simp only [Category.comp_id])).symm
  rw [← Category.assoc, hd]
  exact Category.id_comp _

private theorem krull_dimension_zero :
    topologicalKrullDim (symmetricPower E 0).left = 0 := by
  let e := ((Over.forget (Spec ↧ℂ)).mapIso zeroIso).symm
  change topologicalKrullDim ((Over.forget (Spec ↧ℂ)).obj (symmetricPower E 0)) = 0
  rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  change topologicalKrullDim (PrimeSpectrum ℂ) = 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]

example : topologicalKrullDim (symmetricPower E 0).left = 0 := krull_dimension_zero

private def quotientCurveIso : symmetricPower E 1 ≅ E := oneIso.symm ≪≫ curveIso
private def quotientZ : (symmetricPower E 1).left.Opens := quotientCurveIso.hom.left ⁻¹ᵁ zChart
private def quotientY : (symmetricPower E 1).left.Opens := quotientCurveIso.hom.left ⁻¹ᵁ yChart

private theorem quotient_nonself_overlap : quotientZ ≠ quotientY := by
  intro h
  have H := congrArg (fun O => quotientCurveIso.inv.left ⁻¹ᵁ O) h
  change (quotientCurveIso.inv.left ≫ quotientCurveIso.hom.left) ⁻¹ᵁ zChart =
    (quotientCurveIso.inv.left ≫ quotientCurveIso.hom.left) ⁻¹ᵁ yChart at H
  have hi : quotientCurveIso.inv.left ≫ quotientCurveIso.hom.left = 𝟙 E.left :=
    congrArg (fun f : E ⟶ E => f.left) quotientCurveIso.inv_hom_id
  rw [hi, Scheme.Hom.id_preimage, Scheme.Hom.id_preimage] at H
  have H' := congrArg (fun O => finitePoint ⁻¹ᵁ O) H
  rw [finitePoint_zChart, finitePoint_yChart] at H'
  exact top_ne_bot H'

private theorem quotient_nonself_overlap_pullback :
    IsPullback ((symmetricPower E 1).left.homOfLE
        (show quotientZ ⊓ quotientY ≤ quotientZ from inf_le_left))
      ((symmetricPower E 1).left.homOfLE
        (show quotientZ ⊓ quotientY ≤ quotientY from inf_le_right))
      quotientZ.ι quotientY.ι := isPullback_opens_inf quotientZ quotientY

example : quotientZ ≠ quotientY := quotient_nonself_overlap

private def shift (a : ℂ) : affine 1 ⟶ affine 1 :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := ℂ) (fun i : Fin 1 => MvPolynomial.X i + MvPolynomial.C a)).toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext r
      simp)

private theorem shift_comp (a b : ℂ) : shift a ≫ shift b = shift (a+b) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change ((MvPolynomial.aeval (R := ℂ) (fun i : Fin 1 => MvPolynomial.X i + MvPolynomial.C a)).comp
    (MvPolynomial.aeval (R := ℂ) (fun i : Fin 1 => MvPolynomial.X i + MvPolynomial.C b))).toRingHom =
    (MvPolynomial.aeval (R := ℂ) (fun i : Fin 1 => MvPolynomial.X i + MvPolynomial.C (a+b))).toRingHom
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  ring

private theorem shift_ne (a b : ℂ) (h : a ≠ b) : shift a ≠ shift b := by
  intro H
  have H' := Spec.map_injective (congrArg (fun f : affine 1 ⟶ affine 1 => f.left) H)
  have he := congrArg (fun f : CommRingCat.of (MvPolynomial (Fin 1) ℂ) ⟶
      CommRingCat.of (MvPolynomial (Fin 1) ℂ) =>
        MvPolynomial.eval (fun _ => (0 : ℂ)) (f (MvPolynomial.X (0 : Fin 1)))) H'
  apply h
  simpa [shift] using he

private theorem corrupted_cocycle_falsification :
    shift (1 : ℂ) ≫ shift (1 : ℂ) ≠ shift (3 : ℂ) := by
  rw [shift_comp]
  exact shift_ne _ _ (by norm_num)

example : shift (1 : ℂ) ≫ shift (2 : ℂ) = shift (3 : ℂ) := by
  convert shift_comp (1 : ℂ) (2 : ℂ) using 1 <;> norm_num

private def U : (affine 1).left.Opens :=
  (affine 1).left.basicOpen ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin 1) ℂ)).inv
    (MvPolynomial.X (0 : Fin 1)))
private def V : (affine 1).left.Opens :=
  (affine 1).left.basicOpen ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin 1) ℂ)).inv
    (MvPolynomial.X (0 : Fin 1) - 1))

private theorem nonself_overlap : U ≠ V := by
  intro h
  have hU : U = PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) :=
    basicOpen_eq_of_affine _
  have hV : V = PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1) - 1 : MvPolynomial (Fin 1) ℂ) :=
    basicOpen_eq_of_affine _
  let r : PrimeSpectrum (MvPolynomial (Fin 1) ℂ) :=
    PrimeSpectrum.comap (MvPolynomial.eval (fun _ => (0 : ℂ))) default
  have H := Iff.of_eq (congrArg (fun W : (affine 1).left.Opens => r ∈ W)
    (hU.symm.trans (h.trans hV)))
  change (MvPolynomial.X (0 : Fin 1) ∉ r.asIdeal) ↔
    (MvPolynomial.X (0 : Fin 1) - 1 ∉ r.asIdeal) at H
  simp only [r, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, MvPolynomial.eval_X,
    map_sub, map_one] at H
  have hone : (1 : ℂ) ∈ (default : PrimeSpectrum ℂ).asIdeal := by simpa using H
  exact (default : PrimeSpectrum ℂ).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

private theorem nonself_overlap_pullback :
    IsPullback ((affine 1).left.homOfLE (show U ⊓ V ≤ U from inf_le_left))
      ((affine 1).left.homOfLE (show U ⊓ V ≤ V from inf_le_right)) U.ι V.ι :=
  isPullback_opens_inf U V

private theorem nonself_overlap_nonempty : (↑(U ⊓ V) : Set (affine 1).left).Nonempty := by
  let r : PrimeSpectrum (MvPolynomial (Fin 1) ℂ) :=
    PrimeSpectrum.comap (MvPolynomial.eval (fun _ => (2 : ℂ))) default
  refine ⟨r, ?_⟩
  have hU : U = PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) :=
    basicOpen_eq_of_affine _
  have hV : V = PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1) - 1 : MvPolynomial (Fin 1) ℂ) :=
    basicOpen_eq_of_affine _
  rw [hU, hV]
  change (MvPolynomial.X (0 : Fin 1) ∉ r.asIdeal) ∧
    (MvPolynomial.X (0 : Fin 1) - 1 ∉ r.asIdeal)
  norm_num [r, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Ideal.eq_bot_of_prime (I := (default : PrimeSpectrum ℂ).asIdeal)]

example : U ≠ V := nonself_overlap

/-- Independent concrete test for `retained_comparison`.
Source: SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem retained_comparison_example : Nonempty (g3_power E 1 ≅ symmetricPower E 1) := ⟨oneIso⟩

example : Nonempty (g3_power E 1 ≅ symmetricPower E 1) := retained_comparison_example

/-- Independent concrete test for `smooth_dimension`.
Source: Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem smooth_dimension_example : topologicalKrullDim (symmetricPower E 1).left = 1 := krull_dimension_positive

example : topologicalKrullDim (symmetricPower E 1).left = 1 := smooth_dimension_example

/-- Independent concrete test for `degree_zero`.
Source: Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem degree_zero_example : Nonempty (g3_power E 0 ≅ symmetricPower E 0) := ⟨zeroIso⟩

example : Nonempty (g3_power E 0 ≅ symmetricPower E 0) := degree_zero_example

/-- Independent concrete test for `branch_coordinates`.
Source: Hartshorne, Algebraic Geometry, II.5.
HC no distance; AV milestone no distance.
-/
theorem branch_coordinates_example : coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (1 : Fin 2) := coordinateIdeals_ne

example : coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (1 : Fin 2) := branch_coordinates_example

/-- Independent concrete test for `point_addition`.
Source: Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem point_addition_example : ∀ b : ComplexPoint (affine 1), s2c_branchInsertion (affine 1) 1 b ≫ g3_proj (affine 1) 2 (1 : Fin 2) = g3_proj (affine 1) 1 (0 : Fin 1) := by intro b; rw [s2c_branchInsertion, s2_check_lift_proj]; rfl

example : ∀ b : ComplexPoint (affine 1), s2c_branchInsertion (affine 1) 1 b ≫ g3_proj (affine 1) 2 (1 : Fin 2) = g3_proj (affine 1) 1 (0 : Fin 1) := point_addition_example

/-- Independent concrete test for `branch_intersections`.
Source: Hartshorne, Algebraic Geometry, II.5.
HC no distance; AV milestone no distance.
-/
theorem branch_intersections_example : coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (1 : Fin 2) := branch_intersections_falsification

example : coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (0 : Fin 2) ≠ coordinateIdeal 2 (0 : Fin 2) ⊔ coordinateIdeal 2 (1 : Fin 2) := branch_intersections_example

/-- Independent concrete test for `excess_branches`.
Source: Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem excess_branches_example : Nonempty (branchIntersection E 0 2 (fun _ => Over.homMk finitePoint finitePoint_over)).left := excess_branches_falsification

example : Nonempty (branchIntersection E 0 2 (fun _ => Over.homMk finitePoint finitePoint_over)).left := excess_branches_example

/-- Independent concrete test for `curve_coordinate_transport`.
Source: Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem curve_coordinate_transport_example : ∃ z : Fin 2 → ComplexPoint (affine 1), z ∘ Equiv.swap (0 : Fin 2) 1 = z ∧ Equiv.swap (0 : Fin 2) 1 ≠ Equiv.refl _ := curve_coordinate_transport_falsification

example : ∃ z : Fin 2 → ComplexPoint (affine 1), z ∘ Equiv.swap (0 : Fin 2) 1 = z ∧ Equiv.swap (0 : Fin 2) 1 ≠ Equiv.refl _ := curve_coordinate_transport_example

#print axioms retained_comparison_example
#print axioms smooth_dimension_example
#print axioms degree_zero_example
#print axioms branch_coordinates_example
#print axioms point_addition_example
#print axioms branch_intersections_example
#print axioms excess_branches_example
#print axioms curve_coordinate_transport_example
#print axioms quotient_nonself_overlap
#print axioms quotient_nonself_overlap_pullback
#print axioms nonself_overlap
#print axioms nonself_overlap_nonempty
#print axioms nonself_overlap_pullback
#print axioms corrupted_cocycle_falsification
end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
