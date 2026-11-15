import HodgeLean.Adapters.AutomorphyChernHQProofs

/-! # The Chern form in `HQ X 2` on `X`'s own period lattice: frozen specification

Scope (Appell–Humbert stage 4a). For a smooth projective integral complex group `X` with S12
period lattice `Λ = abelianPeriodLattice X ⊆ ℂ^g`, `g = dim X.left`, the datum
`datumOfX X H E hE χ hχ` (`AutomorphyChernHQDefs`) is an Appell–Humbert datum on `Λ` itself, so
the stage-3 Chern form `chernForm` of its holomorphic factor (`AutomorphyChernClass`) is a form on
`Λ` and has a class `latticeClassHQ` in `HQ X 2` (stage 7b, `LatticeClassHQ`). Claimed:
* the integral form of the datum is the given `E`, and every `H` with integral `Im H` on `Λ` has a
  semicharacter, so the datum exists for every such `H`;
* for every continuous logarithm `f` of its factor, `chernForm f = -E` on `Λ`, so the class of the
  Chern form in `HQ X 2` is `-latticeClassHQ X E`;
* Hard Lefschetz for `-η` is equivalent to Hard Lefschetz for `η`, for any cup product;
* as an implication from these and `spec_latticeClassHQ_hardLefschetz`: for positive definite `H`,
  Hard Lefschetz holds for the class of the Chern form;
* falsification: for the trivial datum (`E = 0`) the class is zero and Hard Lefschetz fails in
  positive dimension.

Not claimed: that the datum defines a line bundle on the scheme `X` or that its class is algebraic
(GAGA, the remaining stage); that `chernForm` is the sheaf-cohomological `c₁`; that every line
bundle on `X(ℂ)` comes from such a datum; `LefschetzOneOneHyp`. The identification of `ℂ^g / Λ`
with `X(ℂ)` is the S12 uniformization, which is used only through the lattice `Λ` and the proved
period equivalence inside `latticeClassHQ`; no complex-manifold isomorphism is claimed.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass

namespace HodgeLean.Adapters

section Sign

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Hard Lefschetz is insensitive to the sign of the class: `L_{-η}^r = (-1)^r L_η^r`, since the
cup product is linear in its first argument, and `(-1)^r` is a unit of `ℚ`.
Source: Huybrechts, *Complex Geometry*, Proposition 3.3.13 (Hard Lefschetz, the operator `L`);
`lefschetzPow`, `CupProduct.cup`. -/
theorem spec_hardLefschetz_neg_iff (μ : CupProduct X) (η : HQ X 2) :
    HardLefschetz X μ (-η) ↔ HardLefschetz X μ η :=
  spec_hardLefschetz_neg_iff_aux X μ η

example (μ : CupProduct X) (η : HQ X 2) (h : HardLefschetz X μ η) :
    HardLefschetz X μ (-η) :=
  (spec_hardLefschetz_neg_iff X μ η).2 h

end Sign

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The integral alternating form of `datumOfX` is the given `E`: `imForm` reads off
`⌊Im H(l, m)⌋ = ⌊E(l, m)⌋ = E(l, m)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3; `Datum.imForm`. -/
theorem spec_datumOfX_imForm (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)) :
    (datumOfX X H E hE χ hχ).imForm = E :=
  spec_datumOfX_imForm_aux X H E hE χ hχ

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (l m : abelianPeriodLattice X) :
    (datumOfX X H E hE χ hχ).imForm l m = E l m :=
  DFunLike.congr_fun (DFunLike.congr_fun (spec_datumOfX_imForm X H E hE χ hχ) l) m

/-- Every Hermitian form whose imaginary part is integral on the period lattice has a
semicharacter there, so `datumOfX` applies to every such `H`. With a `ℤ`-basis `eᵢ` of `Λ`,
`χ(∑ aᵢ eᵢ) = (-1)^{∑_{i<j} aᵢ aⱼ E(eᵢ, eⱼ)}` works, because `E = Im H` is alternating, so
`E(l, m) ≡ E(m, l) mod 2`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 (semicharacters exist for
every `H ∈ NS(X)`); Mumford, *Abelian Varieties*, Ch. I §2. -/
theorem spec_exists_semicharacterOfX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    ∃ χ : abelianPeriodLattice X → Circle, ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m) :=
  spec_exists_semicharacterOfX_aux X H E hE

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    ∃ D : Datum (V := Fin (dim X.left) → ℂ), D.lattice = abelianPeriodLattice X ∧
      D.hermitian = H := by
  obtain ⟨χ, hχ⟩ := spec_exists_semicharacterOfX X H E hE
  exact ⟨datumOfX X H E hE χ hχ, rfl, rfl⟩

/-- On `X`'s own period lattice, the Chern form of the holomorphic factor of `datumOfX` is `-E`,
for every continuous logarithm `f`. This is `spec_chernForm_holFactor` with
`spec_datumOfX_imForm`; the sign is the convention explained there.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 and
Theorem 2.2.3; `spec_chernForm_holFactor`. -/
theorem spec_chernForm_datumOfX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, holFactor (datumOfX X H E hE χ hχ) l v =
      Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : abelianPeriodLattice X) :
    chernForm f l m = -E l m :=
  spec_chernForm_datumOfX_aux X H E hE χ hχ f hlog hf l m

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (l m : abelianPeriodLattice X) :
    chernForm (holLog (datumOfX X H E hE χ hχ)) l m = -E l m :=
  spec_chernForm_datumOfX X H E hE χ hχ _ (spec_holLog_isLog _).1
    (spec_holLog_isLog (datumOfX X H E hE χ hχ)).2 l m

/-- The class of the Chern form in `HQ X 2`: the Chern form of `datumOfX` bundles into an integral
form on `Λ` whose class `latticeClassHQ` is `-latticeClassHQ X E`. It follows from
`spec_chernForm_datumOfX` and additivity `spec_latticeClassHQ_add`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2, Theorem 2.2.3 and
Lemma 1.3.1; `spec_chernForm_datumOfX`, `spec_latticeClassHQ_add`. -/
theorem spec_chernClassHQ_datumOfX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, holFactor (datumOfX X H E hE χ hχ) l v =
      Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      (∀ l m, E' l m = chernForm f l m) ∧ latticeClassHQ X E' = -latticeClassHQ X E :=
  spec_chernClassHQ_datumOfX_aux X H E hE χ hχ f hlog hf

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)) :
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      (∀ l m, E' l m = chernForm (holLog (datumOfX X H E hE χ hχ)) l m) ∧
        latticeClassHQ X E' = -latticeClassHQ X E :=
  spec_chernClassHQ_datumOfX X H E hE χ hχ _ (spec_holLog_isLog _).1
    (spec_holLog_isLog (datumOfX X H E hE χ hχ)).2

/-- Hard Lefschetz for the class of the Chern form of a positive datum on `X`'s period lattice.
This is an implication from `spec_chernClassHQ_datumOfX`, `spec_latticeClassHQ_hardLefschetz`
(through `hardLefschetz_abelian_of_cupPow`) and `spec_hardLefschetz_neg_iff`; it does not say the
class is algebraic.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 and §4.1;
Huybrechts, *Complex Geometry*, Proposition 3.3.13; `spec_latticeClassHQ_hardLefschetz`. -/
theorem spec_chernClassHQ_datumOfX_hardLefschetz
    (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, holFactor (datumOfX X H E hE χ hχ) l v =
      Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      (∀ l m, E' l m = chernForm f l m) ∧
        HardLefschetz X (cupProductOf X) (latticeClassHQ X E') :=
  spec_chernClassHQ_datumOfX_hardLefschetz_aux X H hH E hE χ hχ f hlog hf

example (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    ∃ η : HQ X 2, HardLefschetz X (cupProductOf X) η := by
  obtain ⟨χ, hχ⟩ := spec_exists_semicharacterOfX X H E hE
  obtain ⟨E', -, hL⟩ := spec_chernClassHQ_datumOfX_hardLefschetz X H hH E hE χ hχ _
    (spec_holLog_isLog _).1 (spec_holLog_isLog (datumOfX X H E hE χ hχ)).2
  exact ⟨_, hL⟩

/-- Falsification: for the trivial datum (`H = 0`, `E = 0`, `χ = 1`) on `X`'s period lattice, the
class of the Chern form is zero, and in positive dimension Hard Lefschetz fails for it. So the
positivity premise of `spec_chernClassHQ_datumOfX_hardLefschetz` cannot be dropped.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3 (the trivial
datum); `spec_chernForm_datumOfX`, `spec_latticeClassHQ_zero_falsification`. -/
theorem spec_chernClassHQ_trivial_falsification (hg : 0 < dim X.left)
    (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, holFactor (datumOfXTrivial X) l v =
      Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      (∀ l m, E' l m = chernForm f l m) ∧ latticeClassHQ X E' = 0 ∧
        ¬ HardLefschetz X (cupProductOf X) (latticeClassHQ X E') :=
  spec_chernClassHQ_trivial_falsification_aux X hg f hlog hf

example (hg : 0 < dim X.left) :
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      (∀ l m, E' l m = chernForm (holLog (datumOfXTrivial X)) l m) ∧
        ¬ HardLefschetz X (cupProductOf X) (latticeClassHQ X E') := by
  obtain ⟨E', hE', -, hn⟩ := spec_chernClassHQ_trivial_falsification X hg _
    (spec_holLog_isLog _).1 (spec_holLog_isLog (datumOfXTrivial X)).2
  exact ⟨E', hE', hn⟩

end HodgeLean.Adapters
