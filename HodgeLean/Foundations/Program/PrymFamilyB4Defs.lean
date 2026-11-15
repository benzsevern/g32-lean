import HodgeLean.Foundations.Program.HurwitzPrymRexG32
import HodgeLean.Foundations.Program.HurwitzPrymDefs
import HodgeLean.Foundations.Program.RelativeTorusAbelianDefs

/-! # B4b: tuple components and lattice transport

The group is the concrete matrix realization used in B4's realization proof. A component
below is a braid orbit of tuples; it does not include moving branch points. The lattice
transport definitions take an existing scheme and an integral lattice identification.
They do not select an algebraization witness. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- The concrete group in the proof of `b4_g32_group_realization`.
Source: `HurwitzPrymRex_g32_group_realization`; G32 v0.16, §3.3 and Appendix A. -/
abbrev b4b_Group : Type := g32h_G

noncomputable instance b4b_group : Group b4b_Group := LeftCancelMonoid.groupOfFinite

example : Finite b4b_Group := inferInstance

/-- The faithful matrix realization, without selecting an existential witness.
Source: `HurwitzPrymRex_g32_group_realization`. -/
def b4b_toMatrix : b4b_Group →* Matrix (Fin 4) (Fin 4) ℂ := g32h_G.subtype

example : Function.Injective b4b_toMatrix := Subtype.val_injective

/-- The tuple orbit through a specified root under B4's Hurwitz moves.
Source: Völklein, *Groups as Galois Groups*, Chapter 10; `b4_SameComponent`. -/
def b4b_Component (root : Fin 13 → b4b_Group) : Type :=
  {t : Fin 13 → b4b_Group // b4_SameComponent root t}

example (root : Fin 13 → b4b_Group) : Nonempty (b4b_Component root) :=
  ⟨⟨root, Relation.EqvGen.refl root⟩⟩

/-- The matrix tuple of an orbit point under the concrete realization.
Source: G32 v0.16, §3.1; `b4_g32_group_realization`. -/
def b4b_tuple (root : Fin 13 → b4b_Group) (s : b4b_Component root) :
    Fin 13 → Matrix (Fin 4) (Fin 4) ℂ := fun j ↦ b4b_toMatrix (s.val j)

example (root : Fin 13 → b4b_Group) (s : b4b_Component root) (j : Fin 13) :
    b4b_tuple root s j ∈ g32h_G := (s.val j).property

/-- Transport an integral form to the scheme's period lattice by an integral identification.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.3. -/
def b4b_transportForm (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X)
    (Q : LinearMap.BilinForm ℤ Λ) : LinearMap.BilinForm ℤ (b2_abelianLattice X) :=
  Q.compl₁₂ e.symm.toIntLinearEquiv.toLinearMap e.symm.toIntLinearEquiv.toLinearMap

example (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X)
    (Q : LinearMap.BilinForm ℤ Λ) (x y : Λ) :
    b4b_transportForm Λ X e Q (e x) (e y) = Q x y := by
  change Q (e.symm (e x)) (e.symm (e y)) = Q x y
  rw [e.symm_apply_apply, e.symm_apply_apply]

/-- The degree-two class obtained from the transported integral form.
Source: Birkenhake–Lange, Lemma 1.3.1; `latticeClassHQ`. -/
def b4b_polarization (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X)
    (Q : LinearMap.BilinForm ℤ Λ) : HQ X 2 :=
  latticeClassHQ X (b2_bilinToAddHom (b4b_transportForm Λ X e Q))

example (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X)
    (Q : LinearMap.BilinForm ℤ Λ) :
    b4b_polarization Λ X e Q =
      latticeClassHQ X (b2_bilinToAddHom (b4b_transportForm Λ X e Q)) := rfl

/-- The contravariant action on rational periods of an integral lattice endomorphism.
Source: Birkenhake–Lange, §1.2 (analytic and rational representations). -/
def b4b_periodPrecomp (Λ : Type) [AddCommGroup Λ] (J : Λ →+ Λ) :
    (Λ →+ ℚ) →ₗ[ℚ] (Λ →+ ℚ) where
  toFun f := f.comp J
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

example (Λ : Type) [AddCommGroup Λ] (J : Λ →+ Λ) (f : Λ →+ ℚ) (x : Λ) :
    b4b_periodPrecomp Λ J f x = f (J x) := rfl

/-- Transport the dual lattice action to rational degree-one cohomology through periods.
Source: Birkenhake–Lange, §1.2; `abelianPeriodEquiv`. -/
def b4b_cohomologyAction (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X) (J : Λ →+ Λ) :
    HQ X 1 →ₗ[ℚ] HQ X 1 :=
  (abelianPeriodEquiv X).symm.toLinearMap ∘ₗ
    b4b_periodPrecomp (b2_abelianLattice X)
      (e.toAddMonoidHom.comp (J.comp e.symm.toAddMonoidHom)) ∘ₗ
    (abelianPeriodEquiv X).toLinearMap

example (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X) (J : Λ →+ Λ)
    (v : HQ X 1) (x : Λ) :
    abelianPeriodEquiv X (b4b_cohomologyAction Λ X e J v) (e x) =
      abelianPeriodEquiv X v (e (J x)) := by
  simp only [b4b_cohomologyAction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  change abelianPeriodEquiv X v (e (J (e.symm (e x)))) = _
  rw [e.symm_apply_apply]

/-- Enumeration for the integral group-algebra sums.
Source: `HurwitzPrymRex_g32_finite`. -/
noncomputable instance b4b_fintype : Fintype b4b_Group := Fintype.ofFinite _

example : Fintype b4b_Group := inferInstance

/-- The denominator for the primitive rational projector onto the first coordinate line.
With `|G| = 155520`, it is `3|G|/4`.
Source: G32 v0.16, Definition 3.2; Serre, *Linear Representations of Finite Groups*, §2.2
(matrix coefficient orthogonality). -/
def b4b_projectorDenominator : ℤ := 116640

example : b4b_projectorDenominator * 4 = 3 * 155520 := rfl

/-- Integral coefficients for the primitive projector: `6 Re(ρ(g⁻¹)₀₀)`.
The floor is an everywhere defined arithmetic operation; the integral coefficient identity
is a separate statement. The factor `6` clears the denominators of the printed matrices.
Source: G32 v0.16, Definition 3.2 and Appendix A; Serre, §2.2. -/
def b4b_projectorCoeff (g : b4b_Group) : ℤ :=
  ⌊6 * (b4b_toMatrix g⁻¹ 0 0).re⌋

example (g : b4b_Group) :
    b4b_projectorCoeff g = ⌊6 * (b4b_toMatrix g⁻¹ 0 0).re⌋ := rfl

/-- The image lattice of the specified integral primitive projector on a surface's periods.
Source: G32 v0.16, Definition 3.2; `b4_groupEnd`. -/
abbrev b4b_prymLattice (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) : Type :=
  (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).range

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    AddCommGroup (b4b_prymLattice C hG) := inferInstance

/-- The analytic Prym torus of the specified primitive projector.
Source: G32 v0.16, Definition 3.2; `b4_Prym`. -/
abbrev b4b_analyticPrym (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) : Type :=
  b4_Prym ℂ (C := C) b4b_projectorCoeff

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    AddCommGroup (b4b_analyticPrym C hG) := inferInstance

/-- The central scalar action, extracted by its matrix value from the finite group.
Source: G32 v0.16, §3.3 and Appendix A; the scalar `ω I` in the centre. -/
def b4b_centreAct (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (_hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    b3_periodLattice ℂ C →+ b3_periodLattice ℂ C :=
  ∑ g : b4b_Group, if b4b_toMatrix g = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ)
    then b4_latticeAct ℂ g else 0

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    b4b_centreAct C hG 0 = 0 := map_zero _

/-- The printed generators, as elements of the concrete finite group.
Source: G32 v0.16, Appendix A. -/
def b4b_generators : Fin 4 → b4b_Group :=
  ![⟨g32R1 g32h_omega, Submonoid.subset_closure (by simp)⟩,
    ⟨g32R2 g32h_omega, Submonoid.subset_closure (by simp)⟩,
    ⟨g32X g32h_omega, Submonoid.subset_closure (by simp)⟩,
    ⟨g32Y g32h_omega, Submonoid.subset_closure (by simp)⟩]

example : b4b_toMatrix (b4b_generators 0) = g32R1 g32h_omega := rfl

/-- Conjugate the first reflection by a word in the printed generators.
Source: G32 v0.16, Appendix A and Definition 3.5. -/
def b4b_reflection (w : List (Fin 4)) : b4b_Group :=
  let h := (w.map b4b_generators).prod
  h * b4b_generators 0 * h⁻¹

example : b4b_reflection [] = b4b_generators 0 := by
  simp only [b4b_reflection, List.map_nil, List.prod_nil, one_mul, inv_one, mul_one]

/-- A specified thirteen-entry root: four inverse pairs, four reflections with product
`x²`, and `x²`. The six reflections of each class are interleaved.
Source: G32 v0.16, Definition 3.5 and Appendix A. -/
def b4b_root : Fin 13 → b4b_Group :=
  ![b4b_generators 0, (b4b_generators 0)⁻¹,
    (b4b_generators 1)⁻¹, b4b_generators 1,
    b4b_reflection [2], (b4b_reflection [2])⁻¹,
    b4b_reflection [3], (b4b_reflection [3])⁻¹,
    b4b_reflection [1, 3, 1], (b4b_reflection [0, 0, 2])⁻¹,
    b4b_reflection [3, 2], (b4b_reflection [3, 2, 1])⁻¹,
    (b4b_generators 2)^2]

example : b4b_root 12 = (b4b_generators 2)^2 := rfl

/-- The tuple orbit selected by the explicit root.
Source: Völklein, Chapter 10; G32 v0.16, Definition 3.5. -/
abbrev b4b_Index := b4b_Component b4b_root

instance : Nonempty b4b_Index := ⟨⟨b4b_root, Relation.EqvGen.refl _⟩⟩

example : Nonempty b4b_Index := inferInstance

end HodgeLean.Foundations.Program
