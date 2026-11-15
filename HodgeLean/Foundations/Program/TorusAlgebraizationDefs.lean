import HodgeLean.Foundations.Program.RelativeTorusKernel
import HodgeLean.Foundations.AutomorphyLineBundleDefs
import HodgeLean.Adapters.GagaMapsDefs
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # B5: explicit automorphy data on the B2 universal cover

The form and semicharacter below are formulas in the input lattice, filtration and integral
form. No algebraic realization is selected. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Coordinates on the universal cover of the B2 torus.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
abbrev b5_V (Λ : Type*) [AddCommGroup Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :=
  Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ

example (Λ : Type*) [AddCommGroup Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    NormedSpace ℂ (b5_V Λ F) := inferInstance

/-- Lattice vectors in cover coordinates.
Source: Birkenhake–Lange, §1.1. -/
def b5_lattice (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : Λ →ₗ[ℤ] b5_V Λ F :=
  ((b2_coord _).restrictScalars ℤ).comp (b2_latticeMap Λ F).toIntLinearMap

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : b5_lattice Λ F 0 = 0 := map_zero _

/-- The lift of a cover vector to the conjugate Hodge summand.
Source: Birkenhake–Lange, §1.2; Mathlib `Submodule.quotientEquivOfIsCompl`. -/
def b5_lift (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    b5_V Λ F →ₗ[ℂ] ℂ ⊗[ℤ] Λ :=
  (b2_conjSubmodule Λ F).subtype.comp
    ((F.quotientEquivOfIsCompl (b2_conjSubmodule Λ F) hF).toLinearMap.comp
      (b2_coord _).symm.toLinearMap)

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    b5_lift Λ F hF 0 = 0 := map_zero _

/-- The Hermitian pairing, with conjugate-linear first argument and the integral normalization.
Source: Birkenhake–Lange, §2.1 and §4.2 (Riemann relations). -/
def b5_H (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (z w : b5_V Λ F) : ℂ :=
  -2 * Complex.I * Q.baseChange ℂ (b5_lift Λ F hF w)
    (b2_conj Λ (b5_lift Λ F hF z))

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) : b5_H Λ F hF Q 0 0 = 0 := by
  simp only [b5_H, map_zero, mul_zero]

/-- An integral quadratic refinement in Mathlib's chosen integral basis.
Source: Birkenhake–Lange, §2.2, construction of semicharacters. -/
def b5_refinement (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (Q : LinearMap.BilinForm ℤ Λ) (l : Λ) : ℤ :=
  ∑ i : Fin (Module.finrank ℤ Λ), ∑ j : Fin (Module.finrank ℤ Λ),
    if i < j then (Module.finBasis ℤ Λ).repr l i * (Module.finBasis ℤ Λ).repr l j *
      Q (Module.finBasis ℤ Λ i) (Module.finBasis ℤ Λ j) else 0

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (Q : LinearMap.BilinForm ℤ Λ) : b5_refinement Λ Q 0 = 0 := by
  simp [b5_refinement]

/-- The basis semicharacter, valued in the unit circle.
Source: Birkenhake–Lange, §2.2. -/
def b5_chi (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (Q : LinearMap.BilinForm ℤ Λ) (l : Λ) : Circle :=
  Circle.exp (Real.pi * b5_refinement Λ Q l)

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (Q : LinearMap.BilinForm ℤ Λ) (l : Λ) : ‖(b5_chi Λ Q l : ℂ)‖ = 1 :=
  (b5_chi Λ Q l).norm_coe

/-- The holomorphic factor for the original polarization, before taking its third power.
Source: Birkenhake–Lange, Theorem 2.2.3; `AppellHumbert.holFactor`. -/
def b5_factor (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (l : Λ) (z : b5_V Λ F) : ℂ :=
  (b5_chi Λ Q l : ℂ) * Complex.exp
    (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) z +
      (Real.pi / 2) * b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l))

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (l : Λ) (z : b5_V Λ F) :
    b5_factor Λ F hF Q l z ≠ 0 :=
  mul_ne_zero (b5_chi Λ Q l).coe_ne_zero (Complex.exp_ne_zero _)

/-- Theta section space for the nth power of the factor. No bundle object is claimed.
Source: Birkenhake–Lange, §3.1. -/
def b5_sections (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (n : ℕ) : Submodule ℂ (b5_V Λ F → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ ∀ l z,
    f (z + b5_lattice Λ F l) = b5_factor Λ F hF Q l z ^ n * f z}
  zero_mem' := ⟨differentiable_const 0, by intros; simp⟩
  add_mem' := fun hf hg ↦ ⟨hf.1.add hg.1, by
    intro l z
    simp only [Pi.add_apply, hf.2 l z, hg.2 l z, mul_add]⟩
  smul_mem' := fun c f hf ↦ ⟨hf.1.const_smul c, by
    intro l z
    simp only [Pi.smul_apply, smul_eq_mul, hf.2 l z]
    ring⟩

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (n : ℕ) : (0 : b5_V Λ F → ℂ) ∈
      b5_sections Λ F hF Q n := Submodule.zero_mem _

/-- Tensor multiplication gives the section spaces a multiplicative grading.
Source: Birkenhake–Lange, §3.1. -/
instance b5_sectionsGraded (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (k : ℕ) :
    SetLike.GradedMonoid (fun n : ℕ ↦ b5_sections Λ F hF Q (k * n)) where
  one_mem := ⟨differentiable_const 1, by intros; simp⟩
  mul_mem := by
    intro i j f g hf hg
    refine ⟨hf.1.mul hg.1, ?_⟩
    intro l z
    simp only [Pi.mul_apply, hf.2 l z, hg.2 l z, Nat.mul_add, pow_add]
    ring

/-- The section algebra with degrees divisible by `k`, regraded by `n`.
Source: Birkenhake–Lange, §7.3; Hartshorne, *Algebraic Geometry*, II.5. -/
abbrev b5_ring (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (k : ℕ) :=
  DirectSum ℕ (fun n ↦ b5_sections Λ F hF Q (k * n))

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (k : ℕ) : CommRing (b5_ring Λ F hF Q k) :=
  inferInstance

/-- The full section ring of the original theta bundle.
Source: Birkenhake–Lange, §3.1. -/
abbrev b5_R (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) := b5_ring Λ F hF Q 1

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) : Algebra ℂ (b5_R Λ F hF Q) := inferInstance

/-- The third Veronese section ring, whose degree one consists of sections of `L³`.
Source: Birkenhake–Lange, §7.3. -/
abbrev b5_S (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) := b5_ring Λ F hF Q 3

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) : Algebra ℂ (b5_S Λ F hF Q) := inferInstance

/-- Homogeneous pieces of the third Veronese algebra inside its direct sum.
Source: Hartshorne, *Algebraic Geometry*, II.2, definition of Proj. -/
def b5_grade (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (n : ℕ) : Submodule ℂ (b5_S Λ F hF Q) :=
  LinearMap.range (DirectSum.lof ℂ ℕ (fun n ↦ b5_sections Λ F hF Q (3 * n)) n)

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (n : ℕ) (f : b5_sections Λ F hF Q (3 * n)) :
    DirectSum.of _ n f ∈ b5_grade Λ F hF Q n := ⟨f, rfl⟩

instance b5_gradeMonoid (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) : SetLike.GradedMonoid (b5_grade Λ F hF Q) where
  one_mem := ⟨⟨1, SetLike.one_mem_graded (fun n ↦ b5_sections Λ F hF Q (3 * n))⟩, rfl⟩
  mul_mem := by
    rintro i j a b ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨⟨f.val * g.val, SetLike.mul_mem_graded (A := fun n ↦ b5_sections Λ F hF Q (3 * n)) f.property g.property⟩,
      (DirectSum.of_mul_of (A := fun n ↦ b5_sections Λ F hF Q (3 * n)) f g).symm⟩

private theorem b5_internal (A : ℕ → Type*) [∀ i, AddCommGroup (A i)]
    [∀ i, Module ℂ (A i)] :
    DirectSum.IsInternal (fun i ↦ LinearMap.range (DirectSum.lof ℂ ℕ A i)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hsum i hi
    obtain ⟨a, ha⟩ := hv i hi
    have heval := congrArg (DirectSum.component ℂ ℕ A i) hsum
    simp only [map_sum, map_zero] at heval
    have hne : ∀ j ∈ s, j ≠ i → v j i = 0 := by
      intro j hj hji
      obtain ⟨b, hb⟩ := hv j hj
      rw [← hb]
      exact DirectSum.of_eq_of_ne j i b hji.symm
    have hai : v i i = 0 := by
      change ∑ j ∈ s, v j i = 0 at heval
      simpa only [Finset.sum_eq_single i
        (fun j hj hji ↦ hne j hj hji) (fun h ↦ (h hi).elim), DFinsupp.zero_apply] using heval
    rw [← ha, DirectSum.lof_apply] at hai
    rw [← ha, hai, map_zero]
  · exact DFinsupp.iSup_range_lsingle

instance b5_gradedAlgebra (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) : GradedAlgebra (b5_grade Λ F hF Q) :=
  by
    have h : DirectSum.IsInternal (b5_grade Λ F hF Q) :=
      b5_internal (fun n ↦ b5_sections Λ F hF Q (3 * n))
    exact h.gradedAlgebra

/-- The algebraic model is the Proj of the third Veronese section ring.
Source: Hartshorne, *Algebraic Geometry*, II.2; Birkenhake–Lange, Theorem 4.5.1 and §7.3. -/
def b5_X (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (b5_grade Λ F hF Q)

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) :
    b5_X Λ F hF Q = AlgebraicGeometry.Proj (b5_grade Λ F hF Q) := rfl

open CategoryTheory AlgebraicGeometry

/-- The structure map to the complex base uses constants in degree zero.
Source: Hartshorne, *Algebraic Geometry*, II.2. -/
def b5_model (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) : Over (Spec ↧ℂ) :=
  Over.mk (Proj.toSpecZero (b5_grade Λ F hF Q) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (b5_grade Λ F hF Q 0))))

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) : (b5_model Λ F hF Q).left = b5_X Λ F hF Q := rfl

/-- Evaluate every homogeneous theta function in the cover trivialization and add the values.
Source: Hartshorne, *Algebraic Geometry*, II.2, evaluation map to Proj. -/
def b5_eval (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (z : b5_V Λ F) : b5_S Λ F hF Q →+* ℂ :=
  (Pi.evalRingHom (fun _ : b5_V Λ F ↦ ℂ) z).comp
    (DirectSum.coeRingHom (fun n ↦ b5_sections Λ F hF Q (3 * n)))

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (z : b5_V Λ F) : b5_eval Λ F hF Q z 1 = 1 :=
  map_one _

/-- Evaluation with values in the global functions of the complex point scheme.
Source: Mathlib `Scheme.ΓSpecIso`; Hartshorne, II.2. -/
def b5_evalGlobal (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (z : b5_V Λ F) :
    b5_S Λ F hF Q →+* Γ(Spec ↧ℂ, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.comp (b5_eval Λ F hF Q z)

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (z : b5_V Λ F) :
    b5_evalGlobal Λ F hF Q z 1 = 1 := map_one _

/-- Product filtration, using the two integral projections on complexifications.
Source: Birkenhake–Lange, §1.1 and §1.2. -/
def b5_productF (Λ₁ Λ₂ : Type*) [AddCommGroup Λ₁] [AddCommGroup Λ₂]
    (F₁ : Submodule ℂ (ℂ ⊗[ℤ] Λ₁)) (F₂ : Submodule ℂ (ℂ ⊗[ℤ] Λ₂)) :
    Submodule ℂ (ℂ ⊗[ℤ] (Λ₁ × Λ₂)) :=
  F₁.comap (b2_cplxMap (AddMonoidHom.fst Λ₁ Λ₂)) ⊓
    F₂.comap (b2_cplxMap (AddMonoidHom.snd Λ₁ Λ₂))

example (Λ₁ Λ₂ : Type*) [AddCommGroup Λ₁] [AddCommGroup Λ₂]
    (F₁ : Submodule ℂ (ℂ ⊗[ℤ] Λ₁)) (F₂ : Submodule ℂ (ℂ ⊗[ℤ] Λ₂)) :
    (0 : ℂ ⊗[ℤ] (Λ₁ × Λ₂)) ∈ b5_productF Λ₁ Λ₂ F₁ F₂ := Submodule.zero_mem _

/-- The product polarization is the sum of the two pullbacks.
Source: Birkenhake–Lange, §2.2 and §4.2. -/
def b5_productQ (Λ₁ Λ₂ : Type*) [AddCommGroup Λ₁] [AddCommGroup Λ₂]
    (Q₁ : LinearMap.BilinForm ℤ Λ₁) (Q₂ : LinearMap.BilinForm ℤ Λ₂) :
    LinearMap.BilinForm ℤ (Λ₁ × Λ₂) :=
  Q₁.compl₁₂ (LinearMap.fst ℤ Λ₁ Λ₂) (LinearMap.fst ℤ Λ₁ Λ₂) +
    Q₂.compl₁₂ (LinearMap.snd ℤ Λ₁ Λ₂) (LinearMap.snd ℤ Λ₁ Λ₂)

example (Λ₁ Λ₂ : Type*) [AddCommGroup Λ₁] [AddCommGroup Λ₂]
    (Q₁ : LinearMap.BilinForm ℤ Λ₁) (Q₂ : LinearMap.BilinForm ℤ Λ₂) (v w : Λ₁ × Λ₂) :
    b5_productQ Λ₁ Λ₂ Q₁ Q₂ v w = Q₁ v.1 w.1 + Q₂ v.2 w.2 := rfl

/-- The elliptic model for the lattice generated by `1` and `i`.
Source: Birkenhake–Lange, §1.1; B2 standard example. -/
abbrev b5_elliptic := b5_model (Fin 2 → ℤ) b2_stdF b2_std_isWeightOne b2_stdForm

example : b5_elliptic.left = b5_X (Fin 2 → ℤ) b2_stdF b2_std_isWeightOne b2_stdForm := rfl

open scoped MonoidalCategory
open CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory

/-- The reduced Zariski graph defined by the closure of the analytic graph's underlying points.
Source: Serre, GAGA, §3, Proposition 13; Hartshorne, II.3. -/
def b5_graphIdeal (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨closure (Point.underlying '' HodgeLean.Adapters.gagam_graph X Y f),
      isClosed_closure⟩ : TopologicalSpace.Closeds (X ⊗ Y).left)

/-- The graph scheme over the complex base.
Source: Hartshorne, II.3. -/
def b5_graph (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    Over (Spec ↧ℂ) :=
  Over.mk ((b5_graphIdeal X Y f).subschemeι ≫ (X ⊗ Y).hom)

/-- The inclusion of the reduced graph into the algebraic product.
Source: Hartshorne, II.3. -/
def b5_graphInclusion (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    b5_graph X Y f ⟶ X ⊗ Y :=
  Over.homMk (b5_graphIdeal X Y f).subschemeι rfl

/-- First graph projection.
Source: Serre, GAGA, §3, Proposition 13. -/
def b5_graphFirst (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    b5_graph X Y f ⟶ X := b5_graphInclusion X Y f ≫ fst X Y

/-- Second graph projection.
Source: Serre, GAGA, §3, Proposition 13. -/
def b5_graphSecond (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    b5_graph X Y f ⟶ Y := b5_graphInclusion X Y f ≫ snd X Y

example (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    b5_graphFirst X Y f = b5_graphInclusion X Y f ≫ fst X Y := rfl

example (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    (b5_graphIdeal X Y f).subscheme = (b5_graph X Y f).left := rfl

example (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    (b5_graph X Y f).hom = (b5_graphIdeal X Y f).subschemeι ≫ (X ⊗ Y).hom := rfl

example (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    (b5_graphInclusion X Y f).left = (b5_graphIdeal X Y f).subschemeι := rfl

example (X Y : Over (Spec ↧ℂ)) (f : ComplexPoint X → ComplexPoint Y) :
    b5_graphSecond X Y f = b5_graphInclusion X Y f ≫ snd X Y := rfl

end HodgeLean.Foundations.Program
