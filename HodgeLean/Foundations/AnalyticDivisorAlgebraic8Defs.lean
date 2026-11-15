import HodgeLean.Foundations.AnalyticDivisorAlgebraic7
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-! # Definitions for local divisors of analytic hypersurface germs

This file packages the prime-factor multiplicities of a nonzero analytic germ as a finitely
supported function on associate classes. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic8

open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- The product-coordinate analytic germ represented by a function analytic at the origin.
Source: Gunning--Rossi, II.B, Definition 1. -/
def productAnalyticGermOf {n : ℕ} (f : (Fin n → ℂ) × ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) : ProductAnalyticGerm n :=
  ⟨@Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ (nhds 0) f, f, hf, rfl⟩

/-- The UFD structure on analytic germs in product coordinates, transported from the ordinary
finite-coordinate model.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Theorems 3--6. -/
theorem productAnalyticGermUFD (n : ℕ) :
    UniqueFactorizationMonoid (ProductAnalyticGerm n) := by
  let e := Classical.choose (spec_finSucc_product_equiv (n := n))
  exact e.toMulEquiv.uniqueFactorizationMonoid (spec_analyticGerm_ufd (n + 1))

/-- A local factor class is an associate class of analytic germs. Irreducible classes are the
ones that occur in the support of a nonzero local divisor.
Source: Gunning--Rossi, II.B, Definition 1 and Theorems 3--6. -/
abbrev LocalFactorClass (n : ℕ) := Associates (ProductAnalyticGerm n)

/-- The local divisor of an analytic germ: the finitely supported function recording the
multiplicity of each associate class in its UFD factorization. The zero germ is assigned the zero
function; geometric divisor statements below therefore explicitly exclude it.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
noncomputable def localDivisor (n : ℕ) (f : ProductAnalyticGerm n) :
    LocalFactorClass n →₀ ℕ := by
  classical
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) := productAnalyticGermUFD n
  exact factorization (Associates.mk f)

example : ProductAnalyticGerm 1 :=
  productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 ^ 2 * (y.2 - y.1 0))
    ((analyticAt_snd.pow 2).mul (analyticAt_snd.sub
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
        analyticAt_fst rfl)))

example : LocalFactorClass 1 →₀ ℕ :=
  localDivisor 1 (productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ 1 + y.1 0)
    (analyticAt_const.add
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
        analyticAt_fst rfl)))

end HodgeLean.Foundations.AnalyticDivisorAlgebraic8
