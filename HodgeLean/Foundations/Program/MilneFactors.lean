import HodgeLean.Foundations.Program.MilneFactorsProofs

/-! # Milne M1: first-stage factor specification (FROZEN SPEC)

Implication from the displayed abelian-variety instances and positive polarization
inputs to the algebraic preparation for classical-factor decomposition. The generic
matrix statements give implications from explicit linear involutions and unit Gram
matrices. They retain the full orthogonal group, including reflections.
Matching Albert types, simultaneous block normal forms, the representation on H¹,
and tensor generation are deferred. This first stage supplies no direct M3 input;
its eventual output will be degree-two generation for the full group on all powers.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-- The actual complex endomorphism centralizer is semisimple.
Source: Milne (1999), §1, definition and semisimplicity of C(A). -/
theorem m1_centralizer_semisimple (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    IsSemisimpleRing (m0_endCentralizer J) :=
  m1_centralizer_semisimple_aux J

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    IsSemisimpleRing (m0_endCentralizer J) :=
  m1_centralizer_semisimple J

/-- The centralizer has matrix coordinates with no zero-size simple blocks.
Source: Milne (1999), Lemma 3.5; Mathlib IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed. -/
theorem m1_centralizer_matrix (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    ∃ (s : ℕ) (d : Fin s → ℕ), (∀ i, 0 < d i) ∧
      Nonempty ((m0_endCentralizer J) ≃ₐ[ℂ]
        ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) :=
  m1_centralizer_matrix_aux J

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    ∃ (s : ℕ) (d : Fin s → ℕ), (∀ i, 0 < d i) ∧
      Nonempty ((m0_endCentralizer J) ≃ₐ[ℂ]
        ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) :=
  m1_centralizer_matrix J

/-- The bilinear adjoint gives a linear involution reversing multiplication on the centralizer.
Source: Milne (1999), §1, involution on C(A); m0_centralizer_adjoint. -/
theorem m1_centralizer_involution (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) :
    ∃ τ : (m0_endCentralizer J) ≃ₗ[ℂ] (m0_endCentralizer J),
      Function.Involutive τ ∧
      (∀ a b, τ (a * b) = τ b * τ a) ∧
      (∀ (a : m0_endCentralizer J) (x y : ℂ ⊗[ℚ] HQ J 1),
        m0_form J pol hη ((a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) x) y =
          m0_form J pol hη x ((τ a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) y)) :=
  m1_centralizer_involution_aux J pol hη hpos

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) :
    ∃ τ : (m0_endCentralizer J) ≃ₗ[ℂ] (m0_endCentralizer J),
      Function.Involutive τ ∧
      (∀ a b, τ (a * b) = τ b * τ a) ∧
      (∀ (a : m0_endCentralizer J) (x y : ℂ ⊗[ℚ] HQ J 1),
        m0_form J pol hη ((a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) x) y =
          m0_form J pol hη x ((τ a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) y)) :=
  m1_centralizer_involution J pol hη hpos

/-- The adjoint permutes simple blocks in orbits of size one or two, preserving size.
Source: Milne (1999), Lemma 3.5, reduction to involution-stable factors. -/
theorem m1_involution_blocks (s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, 0 < d i)
    (τ : ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₗ[ℂ]
      ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a) :
    ∃ σ : Equiv.Perm (Fin s), Function.Involutive σ ∧
      (∀ i, d (σ i) = d i) ∧
      (∀ i, τ (m1_blockId s d i) = m1_blockId s d (σ i)) :=
  m1_involution_blocks_aux s d hd τ hτ hmul

example (s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, 0 < d i)
    (τ : ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₗ[ℂ]
      ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a) :
    ∃ σ : Equiv.Perm (Fin s), Function.Involutive σ ∧
      (∀ i, d (σ i) = d i) ∧
      (∀ i, τ (m1_blockId s d i) = m1_blockId s d (σ i)) :=
  m1_involution_blocks s d hd τ hτ hmul

/-- An involution on a fixed simple block is the adjoint of a symmetric or alternating form.
Source: Milne (1999), Lemma 3.5, cases (b) and (c). -/
theorem m1_simple_involution (n : ℕ) (hn : 0 < n)
    (τ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hτ : Function.Involutive τ) (hmul : ∀ A B, τ (A * B) = τ B * τ A) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧
      (B.transpose = B ∨ B.transpose = -B) ∧
      ∀ X, τ X = m1_gramAdjoint n B X :=
  m1_simple_involution_aux n hn τ hτ hmul

example (n : ℕ) (hn : 0 < n)
    (τ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hτ : Function.Involutive τ) (hmul : ∀ A B, τ (A * B) = τ B * τ A) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧
      (B.transpose = B ∨ B.transpose = -B) ∧
      ∀ X, τ X = m1_gramAdjoint n B X :=
  m1_simple_involution n hn τ hτ hmul

/-- The norm-one equation for a fixed block gives its full bilinear isometry group.
Source: Milne (1999), Lemma 3.5, cases (b) and (c), and §2 classical groups. -/
theorem m1_gram_norm_one (n : ℕ) (B X : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B) :
    m1_gramAdjoint n B X * X = 1 ↔
      IsUnit X ∧ X.transpose * B * X = B :=
  m1_gram_norm_one_aux n B X hB

example (n : ℕ) (B X : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B) :
    m1_gramAdjoint n B X * X = 1 ↔
      IsUnit X ∧ X.transpose * B * X = B :=
  m1_gram_norm_one n B X hB

/-- The norm-one elements of an exchanged pair are parametrized by the full general linear group.
Source: Milne (1999), Lemma 3.5, case (a). -/
theorem m1_exchange_norm_one (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    m1_exchange n X * X = 1 ↔
      ∃ U : (Matrix (Fin n) (Fin n) ℂ)ˣ,
        X = (U.val, U.inv.transpose) :=
  m1_exchange_norm_one_aux n X

example (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    m1_exchange n X * X = 1 ↔
      ∃ U : (Matrix (Fin n) (Fin n) ℂ)ˣ,
        X = (U.val, U.inv.transpose) :=
  m1_exchange_norm_one n X

end HodgeLean.Foundations.Program
