import HodgeLean.Foundations.AppellHumbert
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-! # Definitions for the Appell--Humbert sections spec (FROZEN)

This file is part of the frozen Appell--Humbert sections-and-class spec. Do not edit it.
HC no distance; AV milestone no distance.

**Convention.** `AppellHumbert.HermitianForm` is conjugate-linear in its *first* argument, whereas
Birkenhake--Lange take `H` complex-linear in the first argument. The frozen `AppellHumbert.factor`
evaluates `H v l`, which is therefore conjugate-linear in `v`; `holFactor` below evaluates `H l v`,
which is Birkenhake--Lange's `H_BL(v, l)` written in this repository's convention, and is
holomorphic in `v`. Theta functions are defined with `holFactor`.
-/

noncomputable section

namespace HodgeLean.Foundations.AppellHumbert

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]

/-- The zero Hermitian form.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
def HermitianForm.zero : HermitianForm (V := V) where
  toFun _ _ := 0
  add_left _ _ _ := by simp
  smul_left _ _ _ := by simp
  add_right _ _ _ := by simp
  smul_right _ _ _ := by simp
  conj_symm _ _ := by simp

example (x y : V) : (HermitianForm.zero (V := V)).toFun x y = 0 := rfl

/-- The sum of two Hermitian forms.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
def HermitianForm.add (H₁ H₂ : HermitianForm (V := V)) : HermitianForm (V := V) where
  toFun x y := H₁.toFun x y + H₂.toFun x y
  add_left x y z := by rw [H₁.add_left, H₂.add_left]; ring
  smul_left c x y := by rw [H₁.smul_left, H₂.smul_left]; ring
  add_right x y z := by rw [H₁.add_right, H₂.add_right]; ring
  smul_right c x y := by rw [H₁.smul_right, H₂.smul_right]; ring
  conj_symm x y := by rw [star_add, H₁.conj_symm, H₂.conj_symm]

example (H₁ H₂ : HermitianForm (V := V)) (x y : V) :
    (H₁.add H₂).toFun x y = H₁.toFun x y + H₂.toFun x y := rfl

end Forms

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The holomorphic Appell--Humbert factor of automorphy
`a(l, v) = χ(l) exp(π H(l, v) + (π/2) H(l, l))`. With this repository's convention (`H`
conjugate-linear in the first argument), `H l v` is Birkenhake--Lange's `H(v, l)`, so this is
their canonical factor, complex-linear (hence holomorphic) in `v`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and Theorem 2.2.3. -/
def holFactor (D : Datum (V := V)) (l : D.lattice) (v : V) : ℂ :=
  (D.semicharacter l : ℂ) * Complex.exp
    (Real.pi * D.hermitian.toFun l v + (Real.pi / 2) * D.hermitian.toFun l l)

example (D : Datum (V := V)) (l : D.lattice) (v : V) :
    holFactor D l v = (D.semicharacter l : ℂ) * Complex.exp
      (Real.pi * D.hermitian.toFun l v + (Real.pi / 2) * D.hermitian.toFun l l) := rfl

/-- The space of theta functions for an Appell--Humbert datum: entire functions `θ : V → ℂ`
with `θ (v + l) = a(l, v) θ v` for every lattice point `l`, where `a = holFactor D`. These are
the global sections of the associated line bundle, pulled back to `V`; that identification is
*not* made here.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 (canonical factors and
theta functions). -/
def sections (D : Datum (V := V)) : Submodule ℂ (V → ℂ) where
  carrier := {θ | Differentiable ℂ θ ∧ ∀ (l : D.lattice) (v : V), θ (v + l) = holFactor D l v * θ v}
  zero_mem' := ⟨differentiable_const 0, fun _ _ ↦ by simp⟩
  add_mem' := fun {f g} hf hg ↦ ⟨hf.1.add hg.1, fun l v ↦ by
    simp only [Pi.add_apply, hf.2 l v, hg.2 l v, mul_add]⟩
  smul_mem' := fun c f hf ↦ ⟨hf.1.const_smul c, fun l v ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, hf.2 l v]; ring⟩

example (D : Datum (V := V)) (θ : V → ℂ) : θ ∈ sections D ↔
    Differentiable ℂ θ ∧ ∀ (l : D.lattice) (v : V), θ (v + l) = holFactor D l v * θ v :=
  Iff.rfl

/-- The trivial Appell--Humbert datum on a full lattice: `H = 0` and `χ = 1`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 (the datum of the
trivial bundle). -/
def Datum.trivial (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    Datum (V := V) where
  lattice := L
  hermitian := HermitianForm.zero
  integral _ _ := ⟨0, by simp [HermitianForm.imaginary, HermitianForm.zero]⟩
  semicharacter _ := 1
  semicharacter_add _ _ := by simp [HermitianForm.imaginary, HermitianForm.zero]

example (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (l : L) (v : V) :
    holFactor (Datum.trivial L) l v = 1 := by
  simp [holFactor, Datum.trivial, HermitianForm.zero]

/-- The tensor product of two Appell--Humbert data, on the lattice of the first one, which must
lie in the lattice of the second: Hermitian forms add and semicharacters multiply.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 (the map
`P(Λ) → Pic(X)` is a homomorphism; the group law on data). -/
def Datum.tensor (D₁ D₂ : Datum (V := V)) (h : D₁.lattice ≤ D₂.lattice) : Datum (V := V) where
  lattice := D₁.lattice
  hermitian := D₁.hermitian.add D₂.hermitian
  integral l m := by
    obtain ⟨n₁, h₁⟩ := D₁.integral l m
    obtain ⟨n₂, h₂⟩ := D₂.integral ⟨l, h l.2⟩ ⟨m, h m.2⟩
    exact ⟨n₁ + n₂, by
      simp only [HermitianForm.imaginary, HermitianForm.add, Complex.add_im] at h₁ h₂ ⊢
      rw [h₁, h₂]; push_cast; ring⟩
  semicharacter l := D₁.semicharacter l * D₂.semicharacter ⟨l, h l.2⟩
  semicharacter_add l m := by
    have e : (⟨((l + m : D₁.lattice) : V), h (l + m).2⟩ : D₂.lattice) =
        ⟨l, h l.2⟩ + ⟨m, h m.2⟩ := rfl
    rw [e, D₁.semicharacter_add, D₂.semicharacter_add]
    simp only [HermitianForm.imaginary, HermitianForm.add, Complex.add_im, mul_add,
      Circle.exp_add]
    ac_rfl

example (D₁ D₂ : Datum (V := V)) (h : D₁.lattice ≤ D₂.lattice) (x y : V) :
    (D₁.tensor D₂ h).hermitian.toFun x y = D₁.hermitian.toFun x y + D₂.hermitian.toFun x y := rfl

/-- The twist of a datum by a vector `w ∈ V`: same lattice and Hermitian form, semicharacter
multiplied by the character `l ↦ exp(2πi E(l, w))`. It is the datum of `t_w^* L`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2. -/
def Datum.twist (D : Datum (V := V)) (w : V) : Datum (V := V) where
  lattice := D.lattice
  hermitian := D.hermitian
  integral := D.integral
  semicharacter l := D.semicharacter l * Circle.exp (2 * Real.pi * D.hermitian.imaginary l w)
  semicharacter_add l m := by
    rw [D.semicharacter_add]
    simp only [Submodule.coe_add, HermitianForm.imaginary, D.hermitian.add_left, Complex.add_im,
      mul_add, Circle.exp_add]
    ac_rfl

example (D : Datum (V := V)) (w : V) (l : D.lattice) :
    (D.twist w).semicharacter l =
      D.semicharacter l * Circle.exp (2 * Real.pi * D.hermitian.imaginary l w) := rfl

/-- The integral alternating form `E = Im H` of a datum, as a biadditive `ℤ`-valued form on the
lattice. Its values are the integers provided by `Datum.integral`; they are read off with
`Int.floor`, which is exact on integers.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 and §2.1. -/
def Datum.imForm (D : Datum (V := V)) : D.lattice →+ D.lattice →+ ℤ :=
  have hfl : ∀ l m : D.lattice, (⌊D.hermitian.imaginary l m⌋ : ℝ) = D.hermitian.imaginary l m :=
    fun l m ↦ by obtain ⟨n, hn⟩ := D.integral l m; rw [hn, Int.floor_intCast]
  AddMonoidHom.mk' (fun l ↦ AddMonoidHom.mk' (fun m ↦ ⌊D.hermitian.imaginary l m⌋)
    (fun m m' ↦ by
      apply Int.cast_injective (α := ℝ)
      rw [Int.cast_add, hfl, hfl, hfl]
      simp only [Submodule.coe_add, HermitianForm.imaginary, D.hermitian.add_right,
        Complex.add_im]))
    (fun l l' ↦ by
      ext m
      apply Int.cast_injective (α := ℝ)
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [Int.cast_add, hfl, hfl, hfl]
      simp only [Submodule.coe_add, HermitianForm.imaginary, D.hermitian.add_left,
        Complex.add_im])

example (D : Datum (V := V)) (l m : D.lattice) :
    D.imForm l m = ⌊D.hermitian.imaginary l m⌋ := rfl

end Lattice

section LatticeClass

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- The rational coordinate functionals of the chosen `ℤ`-basis of a finite free lattice, as
rational characters `Λ →+ ℚ`.

Source: Bourbaki, *Algèbre*, ch. II, §2.6 (dual bases). -/
def latticeDualBasis (i : Module.Free.ChooseBasisIndex ℤ Λ) : Λ →+ ℚ :=
  (Int.castAddHom ℚ).comp ((Module.Free.chooseBasis ℤ Λ).coord i).toAddMonoidHom

example (i : Module.Free.ChooseBasisIndex ℤ Λ) (x : Λ) :
    latticeDualBasis i x = (((Module.Free.chooseBasis ℤ Λ).coord i x : ℤ) : ℚ) := rfl

/-- The degree-two class of a biadditive integral form on a lattice, in the second exterior
power of the rational dual `Λ →+ ℚ`: with `eᵢ` the chosen basis and `eᵢ*` its rational dual,
`[E] = ∑ᵢ ∑ⱼ (E(eᵢ, eⱼ)/2) eᵢ* ∧ eⱼ*`. For alternating `E` this is `∑_{i<j} E(eᵢ,eⱼ) eᵢ* ∧ eⱼ*`,
the element of `⋀² Hom(Λ, ℚ)` corresponding to `E` (canonical, independent of the basis).

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.3 and Lemma 1.3.1
(`H²(X, ℤ) = Alt²(Λ, ℤ)`); Bourbaki, *Algèbre*, ch. III, §11. -/
def latticeClass (E : Λ →+ Λ →+ ℤ) : ⋀[ℚ]^2 (Λ →+ ℚ) :=
  ∑ i, ∑ j, (((E (Module.Free.chooseBasis ℤ Λ i) (Module.Free.chooseBasis ℤ Λ j) : ℤ) : ℚ) / 2) •
    exteriorPower.ιMulti ℚ 2 ![latticeDualBasis i, latticeDualBasis j]

example : latticeClass (0 : Λ →+ Λ →+ ℤ) = 0 := by simp [latticeClass]

end LatticeClass

end HodgeLean.Foundations.AppellHumbert
