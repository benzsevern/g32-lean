import HodgeLean.Foundations.AutomorphyChernClassProofs

/-! # The alternating form of a factor of automorphy (FROZEN SPEC)

Scope. This module specifies the first, lattice-side part of Appell--Humbert stage 3 (the Chern
class side of Lefschetz (1,1) for abelian `X`), without sheaf cohomology. For a factor
`a : L → V → ℂ` on a subgroup `L` of a complex normed space `V`, written `a = exp(2πi f)` with `f`
continuous in `v`, the alternating form
`E_f(l, m) = f(m, v + l) + f(l, v) - f(l, v + m) - f(m, v)` (`logForm`, `chernForm`) is the
classical description of `c₁(L(a))` in `Alt²(L, ℤ)`. Claimed:
* every factor continuous and nowhere zero in `v` has a continuous logarithm;
* the implication from the cocycle identity to integrality and independence of the base point,
  antisymmetry, and biadditivity of `E_f`;
* independence of the logarithm (no cocycle needed), additivity `E_{a·b} = E_a + E_b`, and
  vanishing on coboundaries `k(v + l) / k(v)`;
* for the holomorphic Appell--Humbert factor `holFactor D`: an explicit continuous logarithm, and
  `E = -D.imForm` (the sign comes from this repository's convention that `H` is conjugate-linear
  in its first argument), hence the degree-two class `latticeClass E = -latticeClass D.imForm`;
* falsification: the trivial factor gives `E = 0`; without the cocycle identity `logForm` is
  neither integral nor independent of the base point.

Not claimed: that `E_a` is the first Chern class of `L(a)` in sheaf cohomology (the exponential
sequence and `H¹(V/L, 𝒪*) → H²(V/L, ℤ)` are not formalized), any statement in `HQ X 2` (for the
period lattice of an abelian `X` it would be `latticeClassHQ` of the bundled form), invariance under isomorphism of the sheaves `L(a)`,
algebraization by GAGA or ampleness (stage 4), and that every line bundle comes from a factor.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.AutomorphyChernClass

open AppellHumbert

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}

/-- Every factor that is continuous and nowhere zero in `v` has a continuous logarithm
`a l v = exp(2πi f l v)`: `V` is simply connected (it is contractible) and locally path connected,
and `exp : ℂ → ℂ \ {0}` is a covering map, so `a l` lifts. This makes the hypotheses `hlog`, `hf`
below satisfiable for every holomorphic factor.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 (`a = e^{2πi f}`); Mathlib
`Complex.isCoveringMap_exp` and `IsCoveringMap.existsUnique_continuousMap_lifts`. -/
theorem spec_exists_continuous_log (a : L → V → ℂ) (ha : ∀ l, Continuous (a l))
    (ha₀ : ∀ l v, a l v ≠ 0) :
    ∃ f : L → V → ℂ, (∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v)) ∧
      ∀ l, Continuous (f l) :=
  spec_exists_continuous_log_aux a ha ha₀

example (a : L → V → ℂ) (ha : ∀ l, Continuous (a l))
    (ha₀ : ∀ l v, a l v ≠ 0) :
    ∃ f : L → V → ℂ, (∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v)) ∧
      ∀ l, Continuous (f l) :=
  spec_exists_continuous_log a ha ha₀

/-- For a continuous logarithm `f` of a cocycle `a`, the expression `logForm f v l m` is an
integer independent of the base point `v`, namely `chernForm f l m`. The cocycle makes
`F(l, m, v) = f(l, v + m) + f(m, v) - f(l + m, v)` integer-valued, hence constant in `v` (it is
continuous and `V` is connected), and `logForm f v l m = F(m, l, v) - F(l, m, v)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2. -/
theorem spec_logForm_eq_chernForm (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (v : V) (l m : L) :
    logForm f v l m = chernForm f l m :=
  spec_logForm_eq_chernForm_aux a f hcoc hlog hf v l m

example (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (v : V) (l m : L) :
    logForm f v l m = chernForm f l m :=
  spec_logForm_eq_chernForm a f hcoc hlog hf v l m

/-- The form of a continuous logarithm of a cocycle is antisymmetric (it vanishes on the
diagonal by the `Defs` example): `logForm f v m l = -logForm f v l m` identically, and both sides
are integers, on which rounding commutes with negation.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2. -/
theorem spec_chernForm_antisymm (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : L) :
    chernForm f m l = -chernForm f l m :=
  spec_chernForm_antisymm_aux a f hcoc hlog hf l m

example (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : L) :
    chernForm f m l = -chernForm f l m :=
  spec_chernForm_antisymm a f hcoc hlog hf l m

/-- The form of a continuous logarithm of a cocycle is biadditive. The constant
`F(l, m) = f(l, v + m) + f(m, v) - f(l + m, v)` is a `ℤ`-valued 2-cocycle of `L` with trivial
action, and `chernForm f l m = F(m, l) - F(l, m)` is its commutator form, which is biadditive for
an abelian group.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 and Lemma 2.1.1;
Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2. -/
theorem spec_chernForm_biadditive (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E : L →+ L →+ ℤ, ∀ l m, E l m = chernForm f l m :=
  spec_chernForm_biadditive_aux a f hcoc hlog hf

example (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E : L →+ L →+ ℤ, ∀ l m, E l m = chernForm f l m :=
  spec_chernForm_biadditive a f hcoc hlog hf

/-- The form does not depend on the choice of continuous logarithm: two continuous logarithms of
the same factor differ by a continuous integer-valued function of `v`, hence by a constant `k(l)`,
which cancels in `logForm`. No cocycle hypothesis is needed.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2. -/
theorem spec_chernForm_log_indep (a f f' : L → V → ℂ)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hlog' : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f' l v))
    (hf : ∀ l, Continuous (f l)) (hf' : ∀ l, Continuous (f' l)) :
    chernForm f = chernForm f' :=
  spec_chernForm_log_indep_aux a f f' hlog hlog' hf hf'

example (a f f' : L → V → ℂ)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hlog' : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f' l v))
    (hf : ∀ l, Continuous (f l)) (hf' : ∀ l, Continuous (f' l)) :
    chernForm f = chernForm f' :=
  spec_chernForm_log_indep a f f' hlog hlog' hf hf'

/-- Additivity, `E_{a·b} = E_a + E_b`: for cocycles `a`, `b` and continuous logarithms `f`, `g`,
`h` of `a`, `b`, `a * b`, the form of `h` is the sum. `f + g` is a continuous logarithm of
`a * b`, `logForm` is additive in the logarithm, and the values are integers.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 and §2.1 (factors
multiply under tensor product). -/
theorem spec_chernForm_mul (a b f g h : L → V → ℂ)
    (hcoca : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hcocb : ∀ l m v, b (l + m) v = b l (v + m) * b m v)
    (hloga : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hlogb : ∀ l v, b l v = Complex.exp (2 * Real.pi * Complex.I * g l v))
    (hlogab : ∀ l v, a l v * b l v = Complex.exp (2 * Real.pi * Complex.I * h l v))
    (hf : ∀ l, Continuous (f l)) (hg : ∀ l, Continuous (g l)) (hh : ∀ l, Continuous (h l)) :
    chernForm h = chernForm f + chernForm g :=
  spec_chernForm_mul_aux a b f g h hcoca hcocb hloga hlogb hlogab hf hg hh

example (a b f g h : L → V → ℂ)
    (hcoca : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hcocb : ∀ l m v, b (l + m) v = b l (v + m) * b m v)
    (hloga : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hlogb : ∀ l v, b l v = Complex.exp (2 * Real.pi * Complex.I * g l v))
    (hlogab : ∀ l v, a l v * b l v = Complex.exp (2 * Real.pi * Complex.I * h l v))
    (hf : ∀ l, Continuous (f l)) (hg : ∀ l, Continuous (g l)) (hh : ∀ l, Continuous (h l)) :
    chernForm h = chernForm f + chernForm g :=
  spec_chernForm_mul a b f g h hcoca hcocb hloga hlogb hlogab hf hg hh

/-- The form vanishes on coboundaries: if `a l v = k(v + l) / k(v)` with `k` continuous and
nowhere zero, then `E_a = 0`. Write `k = exp(2πi g)` with `g` continuous (by lifting); then
`g(v + l) - g(v)` is a continuous logarithm of `a` whose `logForm` vanishes identically, and the
form does not depend on the logarithm.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 (equivalent factors) and
Theorem 2.1.2. -/
theorem spec_chernForm_coboundary (k : V → ℂ) (hk : Continuous k) (hk₀ : ∀ v, k v ≠ 0)
    (f : L → V → ℂ)
    (hlog : ∀ (l : L) v, k (v + l) / k v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    chernForm f = 0 :=
  spec_chernForm_coboundary_aux k hk hk₀ f hlog hf

example (k : V → ℂ) (hk : Continuous k) (hk₀ : ∀ v, k v ≠ 0)
    (f : L → V → ℂ)
    (hlog : ∀ (l : L) v, k (v + l) / k v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    chernForm f = 0 :=
  spec_chernForm_coboundary k hk hk₀ f hlog hf

/-- Falsification check: the trivial factor `1` gives `E = 0`. A continuous logarithm of `1` is
integer-valued and continuous in `v`, hence `f l v = c(l)`, and `logForm` cancels.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2. -/
theorem spec_chernForm_trivial (f : L → V → ℂ)
    (hlog : ∀ l v, Complex.exp (2 * Real.pi * Complex.I * f l v) = 1)
    (hf : ∀ l, Continuous (f l)) :
    chernForm f = 0 :=
  spec_chernForm_trivial_aux f hlog hf

example (f : L → V → ℂ)
    (hlog : ∀ l v, Complex.exp (2 * Real.pi * Complex.I * f l v) = 1)
    (hf : ∀ l, Continuous (f l)) :
    chernForm f = 0 :=
  spec_chernForm_trivial f hlog hf

end General

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- `holLog D` is a continuous logarithm of the holomorphic Appell--Humbert factor: `|χ(l)| = 1`
gives `exp(i arg χ(l)) = χ(l)`, and `v ↦ H(l, v)` is `ℂ`-linear on finite-dimensional `V`, hence
continuous. This shows the hypotheses of `spec_chernForm_holFactor` are satisfiable.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and Theorem 2.2.3. -/
theorem spec_holLog_isLog (D : Datum (V := V)) :
    (∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * holLog D l v)) ∧
      ∀ l, Continuous (holLog D l) :=
  spec_holLog_isLog_aux D

example (D : Datum (V := V)) :
    (∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * holLog D l v)) ∧
      ∀ l, Continuous (holLog D l) :=
  spec_holLog_isLog D

/-- For the holomorphic Appell--Humbert factor of a datum, the form is `-Im H`, that is
`E(l, m) = Im H(m, l)`, for every continuous logarithm. With `holLog D`, `logForm` is
`(H(m, l) - H(l, m)) / 2i = -Im H(l, m)`. The sign is a convention: Birkenhake--Lange take `H`
complex-linear in its first argument and get `c₁ = Im H_BL`; this repository's `H` is
conjugate-linear in its first argument, `H(l, m) = H_BL(m, l)`, so `Im H_BL(l, m) = -Im H(l, m)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 and Theorem 2.2.3. -/
theorem spec_chernForm_holFactor (D : Datum (V := V)) (f : D.lattice → V → ℂ)
    (hlog : ∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : D.lattice) :
    chernForm f l m = -D.imForm l m :=
  spec_chernForm_holFactor_aux D f hlog hf l m

example (D : Datum (V := V)) (f : D.lattice → V → ℂ)
    (hlog : ∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : D.lattice) :
    chernForm f l m = -D.imForm l m :=
  spec_chernForm_holFactor D f hlog hf l m

/-- The degree-two class of the form of `holFactor D` is the negative of the stage-1 class
`latticeClass D.imForm`: the bundled form is `-D.imForm` by `spec_chernForm_holFactor`, and
`latticeClass` is additive (`spec_latticeClass_add`).
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 and Lemma 1.3.1. -/
theorem spec_chernForm_holFactor_latticeClass (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice] (f : D.lattice → V → ℂ)
    (hlog : ∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E : D.lattice →+ D.lattice →+ ℤ, (∀ l m, E l m = chernForm f l m) ∧
      latticeClass E = -latticeClass D.imForm :=
  spec_chernForm_holFactor_latticeClass_aux D f hlog hf

example (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice] (f : D.lattice → V → ℂ)
    (hlog : ∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E : D.lattice →+ D.lattice →+ ℤ, (∀ l m, E l m = chernForm f l m) ∧
      latticeClass E = -latticeClass D.imForm :=
  spec_chernForm_holFactor_latticeClass D f hlog hf

end Lattice

/-- Falsification check: without the cocycle identity the form is not well defined. On `ℂ`
with `L = ⊤`, the factor `a(l, v) = exp(2πi v²)` with continuous logarithm `f(l, v) = v²` fails the
cocycle identity, `logForm f v 1 0 = 2v + 1` is not an integer at `v = 1/4`, and it depends on `v`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 (the cocycle is
what makes the form integral and constant). -/
theorem spec_logForm_cocycle_failure :
    let L : Submodule ℤ ℂ := ⊤
    let one : L := ⟨1, Submodule.mem_top⟩
    let f : L → ℂ → ℂ := fun _ v ↦ v ^ 2
    let a : L → ℂ → ℂ := fun l v ↦ Complex.exp (2 * Real.pi * Complex.I * f l v)
    (∃ (l m : L) (v : ℂ), a (l + m) v ≠ a l (v + m) * a m v) ∧
      (¬ ∃ n : ℤ, logForm f (1 / 4) one 0 = n) ∧ logForm f 0 one 0 ≠ logForm f 1 one 0 :=
  spec_logForm_cocycle_failure_aux

example :
    let L : Submodule ℤ ℂ := ⊤
    let one : L := ⟨1, Submodule.mem_top⟩
    let f : L → ℂ → ℂ := fun _ v ↦ v ^ 2
    let a : L → ℂ → ℂ := fun l v ↦ Complex.exp (2 * Real.pi * Complex.I * f l v)
    (∃ (l m : L) (v : ℂ), a (l + m) v ≠ a l (v + m) * a m v) ∧
      (¬ ∃ n : ℤ, logForm f (1 / 4) one 0 = n) ∧ logForm f 0 one 0 ≠ logForm f 1 one 0 :=
  spec_logForm_cocycle_failure

end HodgeLean.Foundations.AutomorphyChernClass
