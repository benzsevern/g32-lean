import HodgeLean.Foundations.Program.MilneFactorsDefs

/-! # Tensor constructions for Milne M1

Fixed subspaces, homogeneous products with permutations, and full bilinear isometries.
The degree-zero construction retains all scalars.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Simultaneous fixed tensors for a set of linear operators.
Source: Milne (1999), §3, tensor invariants of S(A). -/
def m1b_fixed {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Set (Module.End ℂ V)) (n : ℕ) : Submodule ℂ (⨂[ℂ]^n V) :=
  ⨅ u ∈ S, LinearMap.ker (SchurWeyl.tensorPow (Fin n) u - LinearMap.id)

example {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Set (Module.End ℂ V)) (n : ℕ) (t : ⨂[ℂ]^n V) :
    t ∈ m1b_fixed S n ↔ ∀ u ∈ S, SchurWeyl.tensorPow (Fin n) u t = t := by
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

/-- Products of a specified quadratic subspace, with arbitrary slot permutations.
Source: Milne (1999), Proposition 3.6 and Remark 3.7; tensor formulation of pair contractions. -/
def m1b_products {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Q : Submodule ℂ (⨂[ℂ]^2 V)) : (n : ℕ) → Submodule ℂ (⨂[ℂ]^n V)
  | 0 => ⊤
  | 1 => ⊥
  | n + 2 => Submodule.span ℂ {t | ∃ (σ : Equiv.Perm (Fin (n + 2)))
      (a : ⨂[ℂ]^n V) (b : ⨂[ℂ]^2 V),
      a ∈ m1b_products Q n ∧ b ∈ Q ∧
      t = SchurWeyl.permRep ℂ V (Fin (n + 2)) σ
        (InvariantsExterior.tensorAppend n 2 (a ⊗ₜ[ℂ] b))}

example {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Q : Submodule ℂ (⨂[ℂ]^2 V)) :
    PiTensorProduct.tprod ℂ (fun i : Fin 0 => Fin.elim0 i) ∈ m1b_products Q 0 :=
  Submodule.mem_top

/-- Repeated copies of the same operator, with trivial action on the copy index.
Source: Milne (1999), Proposition 3.6, multiplicity spaces. -/
def m1b_copies {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : ℕ) (u : Module.End ℂ V) : Module.End ℂ (Fin r → V) :=
  LinearMap.piMap (fun _ => u)

example {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : ℕ) (u : Module.End ℂ V) (x : Fin r → V) (i : Fin r) :
    m1b_copies r u x i = u (x i) := rfl

/-- All invertible bilinear isometries; no determinant restriction is imposed.
Source: Milne (1999), Lemma 3.5(b,c), including the full orthogonal group. -/
def m1b_isometries {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V) : Set (Module.End ℂ V) :=
  {u | IsUnit u ∧ ∀ x y, B (u x) (u y) = B x y}

example {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : LinearMap.BilinForm ℂ V) : 1 ∈ m1b_isometries B :=
  ⟨isUnit_one, fun _ _ => rfl⟩

/-- Standard alternating matrix on two equally sized coordinate blocks.
Source: Milne (1999), Lemma 3.5(c), symplectic normal form. -/
def m1b_J (k : ℕ) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ :=
  Matrix.fromBlocks 0 1 (-1) 0

example (k : ℕ) : (m1b_J k).transpose = -m1b_J k := by
  ext i j
  cases i <;> cases j <;> simp [m1b_J, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

-- The scalar unit is fixed and nonzero even when the underlying vector space is zero.
example {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Set (Module.End ℂ V)) :
    PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V)) ∈ m1b_fixed S 0 := by
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro u _
  rw [SchurWeyl.tensorPow_tprod]
  congr 1
  funext i
  exact Fin.elim0 i

example {V : Type*} [AddCommGroup V] [Module ℂ V] :
    PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V)) ≠ 0 := by
  intro h
  have he := congrArg (PiTensorProduct.isEmptyEquiv (R := ℂ)
    (s := fun _ : Fin 0 => V) (Fin 0)) h
  exact one_ne_zero (by
    simpa only [PiTensorProduct.isEmptyEquiv_apply_tprod, map_zero] using he)

-- Independent reflection check for the full orthogonal convention.
example : (-1 : Module.End ℂ ℂ) ∈
    m1b_isometries (LinearMap.mul ℂ ℂ) := by
  refine ⟨isUnit_one.neg, ?_⟩
  intro x y
  simp

-- Independent unequal-degree GL check, using only the existing library result.
example (d a b : ℕ) (h : a ≠ b) :
    (SchurWeyl.mixedRep ℂ (Fin d → ℂ) (Fin a) (Fin b)).invariants = ⊥ :=
  SchurWeyl.invariants_mixedRep_eq_bot (by simpa only [Fintype.card_fin] using h)

-- Balanced GL is reused without introducing a new open statement.
example (d k : ℕ) :
    (SchurWeyl.mixedRep ℂ (Fin d → ℂ) (Fin k) (Fin k)).invariants =
      Submodule.span ℂ (Set.range (SchurWeyl.contraction ℂ (Fin d → ℂ) (Fin k))) :=
  SchurWeyl.invariants_mixedRep_eq_span_contraction

end HodgeLean.Foundations.Program
