import HodgeLean.Foundations.Program.MilneTensorProofs

/-! # Milne M1 tensor specification

Implication from semisimple representation theory and bilinear normal forms to
quadratic generation for full O, Sp, and the geometric centralizer norm-one group.
The statements retain multiplicities, permutations, and the scalar tensor unit.
The auxiliary bodies are open. M2 divisor identification and M3 cup integration
are separate obligations; no Hodge-class supplier is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

/-- Matrix coordinates for the actual module, retaining every multiplicity.
Source: Milne (1999), Lemma 3.5 and the representation decomposition in §2; semisimple module theory. -/
theorem m1b_equivariant_matrix (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSemisimpleRing A] :
    ∃ (s : ℕ) (d m : Fin s → ℕ), (∀ i, 0 < d i ∧ 0 < m i) ∧
      ∃ (e : A ≃ₐ[ℂ] ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
        (E : V ≃ₗ[ℂ] ((i : Fin s) → Fin (m i) → Fin (d i) → ℂ)),
        ∀ (a : A) (v : V) (i : Fin s) (j : Fin (m i)),
          E ((a : Module.End ℂ V) v) i j = (e a i).mulVec (E v i j) :=
  m1b_equivariant_matrix_aux V A

example (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSemisimpleRing A] :
    ∃ (s : ℕ) (d m : Fin s → ℕ), (∀ i, 0 < d i ∧ 0 < m i) ∧
      ∃ (e : A ≃ₐ[ℂ] ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
        (E : V ≃ₗ[ℂ] ((i : Fin s) → Fin (m i) → Fin (d i) → ℂ)),
        ∀ (a : A) (v : V) (i : Fin s) (j : Fin (m i)),
          E ((a : Module.End ℂ V) v) i j = (e a i).mulVec (E v i j) :=
  m1b_equivariant_matrix V A

/-- A nondegenerate symmetric matrix over ℂ has identity Gram matrix in a suitable basis.
Source: Milne (1999), Lemma 3.5(b), symmetric bilinear normal form. -/
theorem m1b_symmetric_normal (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (hs : B.transpose = B) :
    ∃ P : (Matrix (Fin n) (Fin n) ℂ)ˣ, P.val.transpose * B * P.val = 1 :=
  m1b_symmetric_normal_aux n B hB hs

example (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (hs : B.transpose = B) :
    ∃ P : (Matrix (Fin n) (Fin n) ℂ)ˣ, P.val.transpose * B * P.val = 1 :=
  m1b_symmetric_normal n B hB hs

/-- A nondegenerate alternating matrix has even size and standard symplectic coordinates.
Source: Milne (1999), Lemma 3.5(c), alternating bilinear normal form. -/
theorem m1b_alternating_normal (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (hs : B.transpose = -B) :
    ∃ (k : ℕ) (e : Fin n ≃ (Fin k ⊕ Fin k))
      (P : (Matrix (Fin n) (Fin n) ℂ)ˣ),
      n = 2 * k ∧ P.val.transpose * B * P.val =
        Matrix.reindex e.symm e.symm (m1b_J k) :=
  m1b_alternating_normal_aux n B hB hs

example (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (hs : B.transpose = -B) :
    ∃ (k : ℕ) (e : Fin n ≃ (Fin k ⊕ Fin k))
      (P : (Matrix (Fin n) (Fin n) ℂ)ˣ),
      n = 2 * k ∧ P.val.transpose * B * P.val =
        Matrix.reindex e.symm e.symm (m1b_J k) :=
  m1b_alternating_normal n B hB hs

/-- An involution exchanging two matrix factors has transpose-exchange coordinates.
Source: Milne (1999), Lemma 3.5(a). -/
theorem m1b_exchange_normal (n : ℕ)
    (τ : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℂ]
      (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hswap : τ (1, 0) = (0, 1)) :
    ∃ e : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ),
      ∀ a, e (τ a) = m1_exchange n (e a) :=
  m1b_exchange_normal_aux n τ hτ hmul hswap

example (n : ℕ)
    (τ : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℂ]
      (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hswap : τ (1, 0) = (0, 1)) :
    ∃ e : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ),
      ∀ a, e (τ a) = m1_exchange n (e a) :=
  m1b_exchange_normal n τ hτ hmul hswap

/-- Full orthogonal tensor invariants on repeated copies are generated in degree two.
Source: Milne (1999), §3, orthogonal tensor theorem and Proposition 3.6(b). -/
theorem m1b_orthogonal_tensors (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n :=
  m1b_orthogonal_tensors_aux V B hB hs r n

example (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n :=
  m1b_orthogonal_tensors V B hB hs r n

/-- Symplectic tensor invariants on repeated copies are generated in degree two.
Source: Milne (1999), §3, symplectic tensor theorem and Proposition 3.6(a). -/
theorem m1b_symplectic_tensors (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (ha : ∀ x, B x x = 0) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n :=
  m1b_symplectic_tensors_aux V B hB ha r n

example (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (ha : ∀ x, B x x = 0) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n :=
  m1b_symplectic_tensors V B hB ha r n

/-- Independent actions give the span of tensor products of fixed vectors.
Source: Milne (1999), Lemma 3.1(b), basis argument for product groups. -/
theorem m1b_independent_factors (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (hS : 1 ∈ S) (hT : 1 ∈ T) :
    (⨅ u ∈ S, ⨅ v ∈ T, LinearMap.ker (TensorProduct.map u v - LinearMap.id)) =
      Submodule.span ℂ {z : V ⊗[ℂ] W | ∃ x y,
        (∀ u ∈ S, u x = x) ∧ (∀ v ∈ T, v y = y) ∧ z = x ⊗ₜ[ℂ] y} :=
  m1b_independent_factors_aux V W S T hS hT

example (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (hS : 1 ∈ S) (hT : 1 ∈ T) :
    (⨅ u ∈ S, ⨅ v ∈ T, LinearMap.ker (TensorProduct.map u v - LinearMap.id)) =
      Submodule.span ℂ {z : V ⊗[ℂ] W | ∃ x y,
        (∀ u ∈ S, u x = x) ∧ (∀ v ∈ T, v y = y) ∧ z = x ⊗ₜ[ℂ] y} :=
  m1b_independent_factors V W S T hS hT

/-- Group invariance can be tested on every colored tensor word of a binary direct sum.
Source: Milne (1999), proof of Proposition 3.6, direct-sum tensor expansion. -/
theorem m1b_colored_fixed (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (n : ℕ) (t : ⨂[ℂ]^n (V × W)) :
    (∀ u ∈ S, ∀ v ∈ T, SchurWeyl.tensorPow (Fin n) (u.prodMap v) t = t) ↔
      ∀ (s : Finset (Fin n)) u, u ∈ S → ∀ v, v ∈ T →
        TensorProduct.map (SchurWeyl.tensorPow {i // i ∈ s} u)
          (SchurWeyl.tensorPow {i // i ∉ s} v)
          (InvariantsExterior.coloredWordOut s t) =
            InvariantsExterior.coloredWordOut s t :=
  m1b_colored_fixed_aux V W S T n t

example (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (n : ℕ) (t : ⨂[ℂ]^n (V × W)) :
    (∀ u ∈ S, ∀ v ∈ T, SchurWeyl.tensorPow (Fin n) (u.prodMap v) t = t) ↔
      ∀ (s : Finset (Fin n)) u, u ∈ S → ∀ v, v ∈ T →
        TensorProduct.map (SchurWeyl.tensorPow {i // i ∈ s} u)
          (SchurWeyl.tensorPow {i // i ∉ s} v)
          (InvariantsExterior.coloredWordOut s t) =
            InvariantsExterior.coloredWordOut s t :=
  m1b_colored_fixed V W S T n t

/-- The norm-one group of a semisimple algebra with involution has quadratic tensor generation.
Source: Milne (1999), Lemma 3.5 and Proposition 3.6, combined with Lemma 3.1(b). -/
theorem m1b_norm_one_tensors (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSemisimpleRing A]
    (τ : A ≃ₗ[ℂ] A) (hτ : Function.Involutive τ)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (r n : ℕ) :
    m1b_fixed (m1b_copies r ''
      {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1}) n =
    m1b_products (m1b_fixed (m1b_copies r ''
      {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1}) 2) n :=
  m1b_norm_one_tensors_aux V A τ hτ hmul r n

example (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSemisimpleRing A]
    (τ : A ≃ₗ[ℂ] A) (hτ : Function.Involutive τ)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (r n : ℕ) :
    m1b_fixed (m1b_copies r ''
      {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1}) n =
    m1b_products (m1b_fixed (m1b_copies r ''
      {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1}) 2) n :=
  m1b_norm_one_tensors V A τ hτ hmul r n

/-- The geometric centralizer norm-one group has quadratic tensor generation on all powers.
Source: Milne (1999), proof of Proposition 3.4 via Proposition 3.6 and Lemma 3.5. -/
theorem m1b_centralizer_tensors (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r n : ℕ) :
    m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) n =
      m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) n :=
  m1b_centralizer_tensors_aux J pol hη hpos r n

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r n : ℕ) :
    m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) n =
      m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) n :=
  m1b_centralizer_tensors J pol hη hpos r n

end HodgeLean.Foundations.Program
