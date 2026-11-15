import HodgeLean.Foundations.Program.TorusAlgebraizationProofs

/-! # B5: torus algebraization specification

Explicit automorphy formulas and their geometric consequences for a polarized B2 torus.
The algebraization stages are implications from the weight-one and Riemann relations.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The explicit cover pairing has Hermitian symmetry.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 and §4.2. -/
theorem b5_hermitian (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z w : b5_V Λ F) :
    star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w :=
  b5_hermitian_aux Λ F hF Q hQ z w

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z w : b5_V Λ F) :
    star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w :=
  b5_hermitian Λ F hF Q hQ z w

/-- The imaginary pairing on integral vectors is the original form.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 and §4.2. -/
theorem b5_imaginary_lattice (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) :
    (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im = (Q l m : ℝ) :=
  b5_imaginary_lattice_aux Λ F hF Q hQ l m

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) :
    (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im = (Q l m : ℝ) :=
  b5_imaginary_lattice Λ F hF Q hQ l m

/-- The cover pairing is positive definite.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.2. -/
theorem b5_positive (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) (hz : z ≠ 0) :
    0 < (b5_H Λ F hF Q z z).re :=
  b5_positive_aux Λ F hF Q hQ z hz

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) (hz : z ≠ 0) :
    0 < (b5_H Λ F hF Q z z).re :=
  b5_positive Λ F hF Q hQ z hz

/-- The basis formula satisfies the semicharacter identity.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2. -/
theorem b5_semicharacter (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) :
    b5_chi Λ Q (l + m) = b5_chi Λ Q l * b5_chi Λ Q m * Circle.exp (Real.pi * (Q l m : ℝ)) :=
  b5_semicharacter_aux Λ F hF Q hQ l m

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) :
    b5_chi Λ Q (l + m) = b5_chi Λ Q l * b5_chi Λ Q m * Circle.exp (Real.pi * (Q l m : ℝ)) :=
  b5_semicharacter Λ F hF Q hQ l m

/-- The holomorphic factor has the lattice cocycle identity.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3. -/
theorem b5_factor_cocycle (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) (z : b5_V Λ F) :
    b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z :=
  b5_factor_cocycle_aux Λ F hF Q hQ l m z

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) (z : b5_V Λ F) :
    b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z :=
  b5_factor_cocycle Λ F hF Q hQ l m z

/-- The factor is holomorphic in the cover variable.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3. -/
theorem b5_factor_holomorphic (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l : Λ) :
    Differentiable ℂ (b5_factor Λ F hF Q l) :=
  b5_factor_holomorphic_aux Λ F hF Q hQ l

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l : Λ) :
    Differentiable ℂ (b5_factor Λ F hF Q l) :=
  b5_factor_holomorphic Λ F hF Q hQ l

/-- Degree-zero holomorphic sections are constant.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (compactness) and Liouville’s theorem. -/
theorem b5_sections_zero (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (f : b5_sections Λ F hF Q 0) :
    ∀ z, f.val z = f.val 0 :=
  b5_sections_zero_aux Λ F hF Q hQ f

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (f : b5_sections Λ F hF Q 0) :
    ∀ z, f.val z = f.val 0 :=
  b5_sections_zero Λ F hF Q hQ f

/-- Every section space is finite dimensional.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and Theorem 3.2.7. -/
theorem b5_sections_finite (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℕ) :
    Module.Finite ℂ (b5_sections Λ F hF Q n) :=
  b5_sections_finite_aux Λ F hF Q hQ n

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℕ) :
    Module.Finite ℂ (b5_sections Λ F hF Q n) :=
  b5_sections_finite Λ F hF Q hQ n

/-- The third tensor power has a section nonzero at each point.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 4.5.1. -/
theorem b5_Lcube_basepointFree (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0 :=
  b5_Lcube_basepointFree_aux Λ F hF Q hQ z

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0 :=
  b5_Lcube_basepointFree Λ F hF Q hQ z

/-- The third tensor power separates distinct torus points.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 4.5.1. -/
theorem b5_Lcube_separatesPoints (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z w : b5_V Λ F) (hzw : ¬ ∃ l : Λ, w = z + b5_lattice Λ F l) :
    ∃ s t : b5_sections Λ F hF Q 3, s.val z * t.val w ≠ s.val w * t.val z :=
  b5_Lcube_separatesPoints_aux Λ F hF Q hQ z w hzw

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z w : b5_V Λ F) (hzw : ¬ ∃ l : Λ, w = z + b5_lattice Λ F l) :
    ∃ s t : b5_sections Λ F hF Q 3, s.val z * t.val w ≠ s.val w * t.val z :=
  b5_Lcube_separatesPoints Λ F hF Q hQ z w hzw

/-- Sections vanishing at a point detect every nonzero tangent vector.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 4.5.1. -/
theorem b5_Lcube_separatesTangents (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z v : b5_V Λ F) (hv : v ≠ 0) :
    ∃ s : b5_sections Λ F hF Q 3, s.val z = 0 ∧ fderiv ℂ s.val z v ≠ 0 :=
  b5_Lcube_separatesTangents_aux Λ F hF Q hQ z v hv

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z v : b5_V Λ F) (hv : v ≠ 0) :
    ∃ s : b5_sections Λ F hF Q 3, s.val z = 0 ∧ fderiv ℂ s.val z v ≠ 0 :=
  b5_Lcube_separatesTangents Λ F hF Q hQ z v hv

/-- The third Veronese section algebra is generated by degree one.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §7.3 (Koizumi’s normal-generation theorem). -/
theorem b5_S_generated_one (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤ :=
  b5_S_generated_one_aux Λ F hF Q hQ

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤ :=
  b5_S_generated_one Λ F hF Q hQ

/-- The evaluation map sends the irrelevant ideal onto the unit ideal.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 4.5.1; Mathlib `Proj.fromOfGlobalSections`. -/
theorem b5_evaluation_irrelevant (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤ :=
  b5_evaluation_irrelevant_aux Λ F hF Q hQ z

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤ :=
  b5_evaluation_irrelevant Λ F hF Q hQ z

/-- The theta Proj is smooth over the complex base.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 4.5.1; Serre, GAGA, §2. -/
theorem b5_smooth (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.Smooth (b5_model Λ F hF Q).hom :=
  b5_smooth_aux Λ F hF Q hQ

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.Smooth (b5_model Λ F hF Q).hom :=
  b5_smooth Λ F hF Q hQ

/-- The theta Proj is projective over the complex base.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 4.5.1 and §7.3; Hartshorne, II.5. -/
theorem b5_projective (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.IsProjective (b5_model Λ F hF Q).hom :=
  b5_projective_aux Λ F hF Q hQ

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.IsProjective (b5_model Λ F hF Q).hom :=
  b5_projective Λ F hF Q hQ

/-- The theta Proj is integral.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and Theorem 4.5.1. -/
theorem b5_integral (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.IsIntegral (b5_X Λ F hF Q) :=
  b5_integral_aux Λ F hF Q hQ

example (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.IsIntegral (b5_X Λ F hF Q) :=
  b5_integral Λ F hF Q hQ

open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic
open scoped CategoryTheory.MonObj

/-- Evaluation defines a point over the complex base.
Source: Hartshorne, II.2; Mathlib `Proj.fromOfGlobalSections_toSpecZero`. -/
theorem b5_thetaCover_over (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    b5_thetaCoverHom Λ F hF Q hQ z ≫ (b5_model Λ F hF Q).hom = 𝟙 (Spec ↧ℂ) :=
  b5_thetaCover_over_aux Λ F hF Q hQ z

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    b5_thetaCoverHom Λ F hF Q hQ z ≫ (b5_model Λ F hF Q).hom = 𝟙 (Spec ↧ℂ) :=
  b5_thetaCover_over Λ F hF Q hQ z

/-- Evaluation depends only on the torus class.
Source: Birkenhake–Lange, Theorem 4.5.1. -/
theorem b5_theta_descent (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (v : (ℂ ⊗[ℤ] Λ) ⧸ F) :
    b5_theta Λ F hF Q hQ (QuotientAddGroup.mk v) =
      b5_thetaCover Λ F hF Q hQ (b2_coord _ v) :=
  b5_theta_descent_aux Λ F hF Q hQ v

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (v : (ℂ ⊗[ℤ] Λ) ⧸ F) :
    b5_theta Λ F hF Q hQ (QuotientAddGroup.mk v) =
      b5_thetaCover Λ F hF Q hQ (b2_coord _ v) :=
  b5_theta_descent Λ F hF Q hQ v

/-- The theta map is a homeomorphism onto the analytic complex points.
Source: Birkenhake–Lange, Theorem 4.5.1; Chow’s theorem. -/
theorem b5_theta_homeomorph (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsHomeomorph (b5_theta Λ F hF Q hQ) :=
  b5_theta_homeomorph_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsHomeomorph (b5_theta Λ F hF Q hQ) :=
  b5_theta_homeomorph Λ F hF Q hQ

open scoped Manifold ContDiff

/-- The theta map and its inverse are holomorphic, with the F4 function comparison and lattice descent.
Source: Birkenhake–Lange, Theorem 4.5.1; Serre, GAGA, §2. -/
theorem b5_theta_holomorphicFunctions (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b2_latticeMap_discrete F hF
    ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ)
        ω (b5_theta Λ F hF Q hQ) ∧
    ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ) 𝓘(ℂ, b5_V Λ F)
        ω (b5_thetaEquiv Λ F hF Q hQ).symm ∧
    ∀ (U : TopologicalSpace.Opens (ComplexPoint (b5_model Λ F hF Q))) (f : U → ℂ),
      (f4_analytification (b5_model Λ F hF Q)).IsHolFun f ↔
        ∃ g : b5_V Λ F → ℂ,
          DifferentiableOn ℂ g ((b5_thetaCover Λ F hF Q hQ) ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q)))) ∧
          (∀ l z, b5_thetaCover Λ F hF Q hQ z ∈ U →
            g (z + b5_lattice Λ F l) = g z) ∧
          ∀ z : (b5_thetaCover Λ F hF Q hQ) ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q))),
            g z = f ⟨b5_thetaCover Λ F hF Q hQ z, z.property⟩ :=
  b5_theta_holomorphicFunctions_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b2_latticeMap_discrete F hF
    ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ)
        ω (b5_theta Λ F hF Q hQ) ∧
    ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ) 𝓘(ℂ, b5_V Λ F)
        ω (b5_thetaEquiv Λ F hF Q hQ).symm ∧
    ∀ (U : TopologicalSpace.Opens (ComplexPoint (b5_model Λ F hF Q))) (f : U → ℂ),
      (f4_analytification (b5_model Λ F hF Q)).IsHolFun f ↔
        ∃ g : b5_V Λ F → ℂ,
          DifferentiableOn ℂ g ((b5_thetaCover Λ F hF Q hQ) ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q)))) ∧
          (∀ l z, b5_thetaCover Λ F hF Q hQ z ∈ U →
            g (z + b5_lattice Λ F l) = g z) ∧
          ∀ z : (b5_thetaCover Λ F hF Q hQ) ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q))),
            g z = f ⟨b5_thetaCover Λ F hF Q hQ z, z.property⟩ :=
  b5_theta_holomorphicFunctions Λ F hF Q hQ

open scoped MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

/-- Add graph isiso.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_add_graph_isIso (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsIso (b5_graphFirst ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)) (b5_model Λ F hF Q) (b5_addAnalytic Λ F hF Q hQ)) :=
  b5_add_graph_isIso_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsIso (b5_graphFirst ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)) (b5_model Λ F hF Q) (b5_addAnalytic Λ F hF Q hQ)) :=
  b5_add_graph_isIso Λ F hF Q hQ

/-- Neg graph isiso.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_neg_graph_isIso (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsIso (b5_graphFirst (b5_model Λ F hF Q) (b5_model Λ F hF Q) (b5_negAnalytic Λ F hF Q hQ)) :=
  b5_neg_graph_isIso_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsIso (b5_graphFirst (b5_model Λ F hF Q) (b5_model Λ F hF Q) (b5_negAnalytic Λ F hF Q hQ)) :=
  b5_neg_graph_isIso Λ F hF Q hQ

/-- Group laws.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_group_laws (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    (b5_identity Λ F hF Q hQ ▷ (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ = (λ_ (b5_model Λ F hF Q)).hom ∧
    ((b5_model Λ F hF Q) ◁ b5_identity Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ = (ρ_ (b5_model Λ F hF Q)).hom ∧
    (b5_add Λ F hF Q hQ ▷ (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ =
      (α_ (b5_model Λ F hF Q) (b5_model Λ F hF Q) (b5_model Λ F hF Q)).hom ≫ ((b5_model Λ F hF Q) ◁ b5_add Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ ∧
    lift (b5_neg Λ F hF Q hQ) (𝟙 (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ = toUnit (b5_model Λ F hF Q) ≫ b5_identity Λ F hF Q hQ ∧
    lift (𝟙 (b5_model Λ F hF Q)) (b5_neg Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ = toUnit (b5_model Λ F hF Q) ≫ b5_identity Λ F hF Q hQ ∧
    (β_ (b5_model Λ F hF Q) (b5_model Λ F hF Q)).hom ≫ b5_add Λ F hF Q hQ = b5_add Λ F hF Q hQ :=
  b5_group_laws_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    (b5_identity Λ F hF Q hQ ▷ (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ = (λ_ (b5_model Λ F hF Q)).hom ∧
    ((b5_model Λ F hF Q) ◁ b5_identity Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ = (ρ_ (b5_model Λ F hF Q)).hom ∧
    (b5_add Λ F hF Q hQ ▷ (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ =
      (α_ (b5_model Λ F hF Q) (b5_model Λ F hF Q) (b5_model Λ F hF Q)).hom ≫ ((b5_model Λ F hF Q) ◁ b5_add Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ ∧
    lift (b5_neg Λ F hF Q hQ) (𝟙 (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ = toUnit (b5_model Λ F hF Q) ≫ b5_identity Λ F hF Q hQ ∧
    lift (𝟙 (b5_model Λ F hF Q)) (b5_neg Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ = toUnit (b5_model Λ F hF Q) ≫ b5_identity Λ F hF Q hQ ∧
    (β_ (b5_model Λ F hF Q) (b5_model Λ F hF Q)).hom ≫ b5_add Λ F hF Q hQ = b5_add Λ F hF Q hQ :=
  b5_group_laws Λ F hF Q hQ

/-- Commutative.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_commutative (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    IsCommMonObj (b5_model Λ F hF Q) :=
  b5_commutative_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    IsCommMonObj (b5_model Λ F hF Q) :=
  b5_commutative Λ F hF Q hQ

/-- Group.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_group (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    b5_theta Λ F hF Q hQ 0 = 1 ∧
    (∀ t u, b5_theta Λ F hF Q hQ (t + u) = b5_theta Λ F hF Q hQ t * b5_theta Λ F hF Q hQ u) ∧
    (∀ t, b5_theta Λ F hF Q hQ (-t) = (b5_theta Λ F hF Q hQ t)⁻¹) :=
  b5_group_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    b5_theta Λ F hF Q hQ 0 = 1 ∧
    (∀ t u, b5_theta Λ F hF Q hQ (t + u) = b5_theta Λ F hF Q hQ t * b5_theta Λ F hF Q hQ u) ∧
    (∀ t, b5_theta Λ F hF Q hQ (-t) = (b5_theta Λ F hF Q hQ t)⁻¹) :=
  b5_group Λ F hF Q hQ

open scoped MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

/-- Periodderivative bijective.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_periodDerivative_bijective (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Function.Bijective (b5_periodDerivative Λ F hF Q hQ) :=
  b5_periodDerivative_bijective_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Function.Bijective (b5_periodDerivative Λ F hF Q hQ) :=
  b5_periodDerivative_bijective Λ F hF Q hQ

/-- Periodderivative lattice.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_periodDerivative_lattice (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l : Λ, b5_periodDerivative Λ F hF Q hQ (b5_lattice Λ F l) ∈
      HodgeLean.Adapters.abelianPeriodLattice (b5_model Λ F hF Q) :=
  b5_periodDerivative_lattice_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l : Λ, b5_periodDerivative Λ F hF Q hQ (b5_lattice Λ F l) ∈
      HodgeLean.Adapters.abelianPeriodLattice (b5_model Λ F hF Q) :=
  b5_periodDerivative_lattice Λ F hF Q hQ

/-- Periodmap bijective.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_periodMap_bijective (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Function.Bijective (b5_periodMap Λ F hF Q hQ) :=
  b5_periodMap_bijective_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Function.Bijective (b5_periodMap Λ F hF Q hQ) :=
  b5_periodMap_bijective Λ F hF Q hQ

/-- Period filtration.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_period_filtration (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    F.map (b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom) = b2_abelianF (b5_model Λ F hF Q) :=
  b5_period_filtration_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    F.map (b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom) = b2_abelianF (b5_model Λ F hF Q) :=
  b5_period_filtration Λ F hF Q hQ

/-- Polarization normalized.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_polarization_normalized (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m : Λ,
      b5_originalChernPairing Λ F hF Q hQ (b5_periodEquiv Λ F hF Q hQ l) (b5_periodEquiv Λ F hF Q hQ m) = Q l m :=
  b5_polarization_normalized_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m : Λ,
      b5_originalChernPairing Λ F hF Q hQ (b5_periodEquiv Λ F hF Q hQ l) (b5_periodEquiv Λ F hF Q hQ m) = Q l m :=
  b5_polarization_normalized Λ F hF Q hQ

/-- Originalchernpairing integral.
Source: Birkenhake–Lange, §1.1, §2.2 and Theorem 4.5.1; Serre, GAGA, §3. -/
theorem b5_originalChernPairing_integral (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m : b2_abelianLattice (b5_model Λ F hF Q),
      (b5_H Λ F hF Q ((b5_periodLinearEquiv Λ F hF Q hQ).symm l.val)
        ((b5_periodLinearEquiv Λ F hF Q hQ).symm m.val)).im =
      (b5_originalChernPairing Λ F hF Q hQ l m : ℝ) :=
  b5_originalChernPairing_integral_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m : b2_abelianLattice (b5_model Λ F hF Q),
      (b5_H Λ F hF Q ((b5_periodLinearEquiv Λ F hF Q hQ).symm l.val)
        ((b5_periodLinearEquiv Λ F hF Q hQ).symm m.val)).im =
      (b5_originalChernPairing Λ F hF Q hQ l m : ℝ) :=
  b5_originalChernPairing_integral Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    ∀ t, b5_thetaEquiv Λ F hF Q hQ t = b5_theta Λ F hF Q hQ t :=
  fun _ ↦ rfl

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    ∀ p, b5_addAnalytic Λ F hF Q hQ p = b5_theta Λ F hF Q hQ
      ((b5_thetaEquiv Λ F hF Q hQ).symm (Point.map (fst (b5_model Λ F hF Q) (b5_model Λ F hF Q)) p) +
       (b5_thetaEquiv Λ F hF Q hQ).symm (Point.map (snd (b5_model Λ F hF Q) (b5_model Λ F hF Q)) p)) :=
  fun _ ↦ rfl

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    ∀ p, b5_negAnalytic Λ F hF Q hQ p = b5_theta Λ F hF Q hQ (-(b5_thetaEquiv Λ F hF Q hQ).symm p) :=
  fun _ ↦ rfl

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    (b5_groupObj Λ F hF Q hQ).mul = b5_add Λ F hF Q hQ :=
  rfl

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    (b5_groupObj Λ F hF Q hQ).inv = b5_neg Λ F hF Q hQ :=
  rfl

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    (b5_groupObj Λ F hF Q hQ).one = b5_identity Λ F hF Q hQ :=
  rfl

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    b5_identity Λ F hF Q hQ = b5_theta Λ F hF Q hQ 0 :=
  rfl

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b5_periodDerivative Λ F hF Q hQ 0 = 0 :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  map_zero (b5_periodDerivative Λ F hF Q hQ)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b5_periodLinearEquiv Λ F hF Q hQ 0 = 0 :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  map_zero (b5_periodLinearEquiv Λ F hF Q hQ)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b5_periodMap Λ F hF Q hQ 0 = 0 :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  map_zero (b5_periodMap Λ F hF Q hQ)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b5_periodEquiv Λ F hF Q hQ 0 = 0 :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  map_zero (b5_periodEquiv Λ F hF Q hQ)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m : Λ, b5_originalChernPairing Λ F hF Q hQ
      (b5_periodEquiv Λ F hF Q hQ l) (b5_periodEquiv Λ F hF Q hQ m) = Q l m :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  b5_polarization_normalized Λ F hF Q hQ

end HodgeLean.Foundations.Program
