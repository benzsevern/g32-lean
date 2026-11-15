import HodgeLean.Adapters.AutomorphyLineBundleOnXProofs

/-! # The line bundle `L(H, χ)` on `X(ℂ)` and its theta sections: frozen specification

Scope (Appell–Humbert stage 5a, step (a) of the route in `docs/specs/AnalyticDivisorAlgebraic.md`).
For a smooth projective integral complex group `X` with S12 period lattice
`Λ = abelianPeriodLattice X ⊆ ℂ^g`, `g = dim X.left`, and exponential `exp : ℂ^g → X(ℂ)`
(`abelianExp`), the sheaf `L(a)` of a factor of automorphy `a` is defined on `X(ℂ)` itself
(`sectionsOnX`, `presheafX`): its sections over `U` are the holomorphic `f` on `exp⁻¹(U)` with
`f (x + l) = a l x * f x`. Holomorphy on `X(ℂ)` is upstream's (`holomorphicOnX`, charts from
algebraic étale coordinates). Claimed:
* for every factor `a`: `L(a)` on `X(ℂ)` is the stage-1 sheaf on `ℂ^g ⧸ Λ` read through `exp`, and
  it is a sheaf;
* for an Appell–Humbert datum `D = datumOfX X H E hE χ hχ` on `Λ`: the global sections of
  `L(holFactor D)` on `X(ℂ)` are exactly the theta functions `sections D`; and `L(holFactor D)` is
  a holomorphic line bundle for upstream's complex structure: over the image of every open `W`
  with disjoint `Λ`-translates, restriction to `W` identifies its sections with the holomorphic
  functions on the open set `exp(W) ⊆ X(ℂ)`, as an implication from stage 1's local triviality
  and the unif lane's local biholomorphism;
* for the trivial factor: `L(1)` is upstream's sheaf of holomorphic functions on `X(ℂ)`;
* for a theta function `θ ∈ sections D`: its zero set is `Λ`-invariant and descends to a closed
  subset `thetaZeroLocusX X θ` of `X(ℂ)` whose preimage under `exp` is `{θ = 0}`, with empty
  interior when `θ ≠ 0`;
* for a positive definite `H`: every semicharacter for `H` is a twist of any other, so a nonzero
  theta function for one semicharacter gives one for every semicharacter (BL §3.2, the reduction
  to one semicharacter);
* falsification: for `H = 0` and `χ` nontrivial there is no nonzero theta function (while for
  `χ = 1` the constants are sections), and nontrivial characters of `Λ` exist in positive
  dimension.

Not claimed: the existence of a nonzero theta function for positive `H` when `g ≥ 2`, or the
dimension `√det E` of `sections D`; a sheaf of `𝒪_{X(ℂ)}`-modules, a total space or a
`VectorBundle` instance; that every holomorphic line bundle on `X(ℂ)` comes from a factor; closed
analyticity of `thetaZeroLocusX X θ` for `g ≥ 2`; multiplicities of the divisor `(θ)`; that the
Chern form is the sheaf-theoretic `c₁` of `presheafX`; any algebraicity (GAGA, Chow);
`LefschetzOneOneHyp` (`docs/specs/AutomorphyLineBundleOnX.md`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyLineBundle
open scoped Manifold CategoryTheory.MonObj

namespace HodgeLean.Adapters

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- Falsification: for `H = 0` and a nontrivial semicharacter (then a character of `Λ`) there is no
nonzero theta function. The factor is `χ(l)`, so `|θ|` is `Λ`-periodic, hence bounded since `Λ`
is a full lattice; by Liouville `θ` is a constant `c`, and `c = χ(l) c` with `χ(l) ≠ 1` forces
`c = 0`. With `χ = 1` the constants are sections (`spec_trivial_sections`), so the hypothesis on
`χ` is needed.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and §3.1; Mumford, *Abelian
Varieties*, §8 (vii) (a nontrivial `L ∈ Pic⁰(X)` has no nonzero section); Liouville's theorem. -/
theorem spec_sections_eq_bot_of_hermitian_zero (D : Datum (V := V))
    (hH : ∀ x y, D.hermitian.toFun x y = 0) (hχ : ∃ l, D.semicharacter l ≠ 1) :
    sections D = ⊥ :=
  spec_sections_eq_bot_of_hermitian_zero_aux D hH hχ

example (D : Datum (V := V)) (hH : ∀ x y, D.hermitian.toFun x y = 0)
    (hχ : ∃ l, D.semicharacter l ≠ 1) (θ : V → ℂ) (hθ : θ ∈ sections D) : θ = 0 := by
  rw [spec_sections_eq_bot_of_hermitian_zero D hH hχ] at hθ
  exact hθ

/-- For positive definite `H`, every character `ψ` of `Λ` is `l ↦ exp(2πi E(l, w))` for some
`w ∈ V`, so the semicharacter `χψ` is that of the twist `D.twist w`. `E = Im H` is a nondegenerate
real form on `V` (`E(v, iv) = H(v, v) > 0`), a `ℤ`-basis `eᵢ` of `Λ` is an `ℝ`-basis of `V`, so
there is `w` with `2π E(eᵢ, w) ≡ arg ψ(eᵢ)`, and two characters agreeing on a basis agree.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2 and §2.4–§2.5
(`Pic⁰(X)` is the group of characters of `Λ`, and `φ_L` is onto it for nondegenerate `H`);
Mumford, *Abelian Varieties*, §8, Theorem 1; `Datum.twist`. -/
theorem spec_exists_twist_semicharacter (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) (ψ : D.lattice → Circle)
    (hψ : ∀ l m, ψ (l + m) = ψ l * ψ m) :
    ∃ w : V, ∀ l, (D.twist w).semicharacter l = D.semicharacter l * ψ l :=
  spec_exists_twist_semicharacter_aux D hH ψ hψ

example (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) :
    ∃ w : V, ∀ l, (D.twist w).semicharacter l = D.semicharacter l * 1 :=
  spec_exists_twist_semicharacter D hH (fun _ ↦ 1) (fun _ _ ↦ (one_mul 1).symm)

/-- For positive definite `H`, a nonzero theta function for one semicharacter gives a nonzero theta
function for every semicharacter `χψ`: take the twist of `spec_exists_twist_semicharacter` and the
translate `exp(-π H(w, v)) θ(v + w)` of `spec_sections_translate`, which is nonzero when `θ` is.
This reduces the existence of theta functions (BL §3.2) to a single semicharacter.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 2.3.2 and §3.2;
`spec_exists_twist_semicharacter`, `spec_sections_translate`. -/
theorem spec_sections_twist_ne_bot (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) (hD : sections D ≠ ⊥) (ψ : D.lattice → Circle)
    (hψ : ∀ l m, ψ (l + m) = ψ l * ψ m) :
    ∃ w : V, (∀ l, (D.twist w).semicharacter l = D.semicharacter l * ψ l) ∧
      sections (D.twist w) ≠ ⊥ :=
  spec_sections_twist_ne_bot_aux D hH hD ψ hψ

example (D : Datum (V := V)) (hH : D.hermitian.IsPositiveDefinite) (hD : sections D ≠ ⊥)
    (ψ : D.lattice → Circle) (hψ : ∀ l m, ψ (l + m) = ψ l * ψ m) :
    ∃ w : V, ∃ θ ∈ sections (D.twist w), θ ≠ 0 := by
  obtain ⟨w, -, hw⟩ := spec_sections_twist_ne_bot D hH hD ψ hψ
  obtain ⟨θ, hθ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  exact ⟨w, θ, hθ, hne⟩

end General

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- For every factor `a`, the sections of `L(a)` on `X(ℂ)` over `U` are the sections of the
stage-1 bundle on `ℂ^g ⧸ Λ` over `proj(exp⁻¹(U))`, by the identity on functions: `exp⁻¹(U)` is
`Λ`-saturated, so it is the preimage of its image in `ℂ^g ⧸ Λ`, and both definitions impose the
same holomorphy and functional equation on it. Through the S12 isomorphism
`ℂ^g ⧸ Λ ≃ X(ℂ)` this says `presheafX X a` is the pushforward of `presheaf Λ a`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §2.1; S12
`complexExponentialQuotientEquiv`; `AutomorphyLineBundle.sectionsOn`. -/
theorem spec_sectionsOnX_equiv (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (U : Set (ComplexPoint X)) :
    ∃ e : sectionsOnX X a U ≃ₗ[ℂ]
        sectionsOn (abelianPeriodLattice X) a
          (proj (abelianPeriodLattice X) '' (abelianExp X ⁻¹' U)),
      ∀ f (x : abelianExp X ⁻¹' U),
        (e f : proj (abelianPeriodLattice X) ⁻¹'
            (proj (abelianPeriodLattice X) '' (abelianExp X ⁻¹' U)) → ℂ)
          ⟨x, Set.mem_image_of_mem _ x.2⟩ = (f : abelianExp X ⁻¹' U → ℂ) x :=
  spec_sectionsOnX_equiv_aux X a U

example (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ) (U : Set (ComplexPoint X)) :
    Nonempty (sectionsOnX X a U ≃ₗ[ℂ]
      sectionsOn (abelianPeriodLattice X) a
        (proj (abelianPeriodLattice X) '' (abelianExp X ⁻¹' U))) :=
  let ⟨e, _⟩ := spec_sectionsOnX_equiv X a U; ⟨e⟩

/-- For every factor `a`, `L(a)` on `X(ℂ)` is a sheaf. Holomorphy and the functional equation are
local on `exp⁻¹(U)`, and the preimages of a cover of `U` cover `exp⁻¹(U)` by `Λ`-stable open
sets; alternatively, transport `spec_presheaf_isSheaf` along `spec_sectionsOnX_equiv` and the
homeomorphism `ℂ^g ⧸ Λ ≃ X(ℂ)`.
Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2; Hartshorne, *Algebraic Geometry*,
II.1; `spec_presheaf_isSheaf`. -/
theorem spec_presheafX_isSheaf (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ) :
    TopCat.Presheaf.IsSheaf (presheafX X a) :=
  spec_presheafX_isSheaf_aux X a

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)) :
    TopCat.Presheaf.IsSheaf (presheafX X (holFactor (datumOfX X H E hE χ hχ))) :=
  spec_presheafX_isSheaf X _

/-- The global sections of `L(H, χ)` on `X(ℂ)` are the theta functions: `exp⁻¹(X(ℂ)) = ℂ^g`, and
both sides are the entire functions with the `holFactor`-functional equation.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and §3.1;
`spec_appellHumbert_globalSections`. -/
theorem spec_globalSectionsX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)) :
    ∃ e : sectionsOnX X (holFactor (datumOfX X H E hE χ hχ)) Set.univ ≃ₗ[ℂ]
        sections (datumOfX X H E hE χ hχ),
      ∀ f (v : Fin (dim X.left) → ℂ),
        (e f : (Fin (dim X.left) → ℂ) → ℂ) v =
          (f : abelianExp X ⁻¹' Set.univ → ℂ) ⟨v, Set.mem_univ _⟩ :=
  spec_globalSectionsX_aux X H E hE χ hχ

/-- Falsification on `X(ℂ)`: for `H = 0` and a nontrivial character `χ` of `Λ`, the bundle
`L(0, χ)` has no nonzero global section, while the trivial bundle (`χ = 1`) has the constants. -/
example (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * (HermitianForm.zero (V := Fin (dim X.left) → ℂ)).imaginary l m))
    (h0 : ∀ l m : abelianPeriodLattice X,
      ((0 : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) l m : ℝ) =
        (HermitianForm.zero (V := Fin (dim X.left) → ℂ)).imaginary l m)
    (hne : ∃ l, χ l ≠ 1) :
    sectionsOnX X (holFactor (datumOfX X HermitianForm.zero 0 h0 χ hχ)) Set.univ = ⊥ := by
  obtain ⟨e, -⟩ := spec_globalSectionsX X HermitianForm.zero 0 h0 χ hχ
  have hb := spec_sections_eq_bot_of_hermitian_zero (datumOfX X HermitianForm.zero 0 h0 χ hχ)
    (fun _ _ ↦ rfl) hne
  rw [Submodule.eq_bot_iff]
  intro f hf
  have h1 : ((e ⟨f, hf⟩ : sections _) : (Fin (dim X.left) → ℂ) → ℂ) = 0 := by
    have := (e ⟨f, hf⟩).2
    exact (Submodule.mem_bot ℂ).mp (hb ▸ this)
  have h2 : e ⟨f, hf⟩ = 0 := Subtype.ext h1
  have h3 : (⟨f, hf⟩ : sectionsOnX X _ Set.univ) = 0 := by
    rw [← e.map_eq_zero_iff]; exact h2
  exact congrArg Subtype.val h3

/-- Local triviality of `L(H, χ)` for upstream's complex structure on `X(ℂ)`: for an open
`W ⊆ ℂ^g` with disjoint `Λ`-translates, `exp(W)` is open, and restriction to `W` identifies the
sections of `L(holFactor D)` over `exp(W)` with the holomorphic functions on `exp(W)`, the section
`f` going to the function `exp w ↦ f w`. `exp` is injective on `W` (disjoint translates and
kernel `Λ`), stage 1's `spec_appellHumbert_restrictEquiv` identifies the sections with the
holomorphic functions on `W`, and `exp|_W` is a biholomorphism onto `exp(W)` by the unif lane's
`spec_complexExponential_localBiholomorph`. Every point of `X(ℂ)` lies in such an `exp(W)`
(`spec_exists_disjoint_nhds`, S12 surjectivity), so `L(H, χ)` is locally isomorphic to the sheaf
of holomorphic functions.
Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2; Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., §1.1, §2.1 and Theorem 2.2.3; `spec_appellHumbert_restrictEquiv`,
`spec_complexExponential_localBiholomorph`. -/
theorem spec_restrictEquivX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (W : Set (Fin (dim X.left) → ℂ)) (hW : IsOpen W)
    (hdisj : ∀ l : abelianPeriodLattice X,
      ((· + (l : Fin (dim X.left) → ℂ)) '' W ∩ W).Nonempty → l = 0) :
    IsOpen (abelianExp X '' W) ∧
      ∃ e : sectionsOnX X (holFactor (datumOfX X H E hE χ hχ)) (abelianExp X '' W) ≃ₗ[ℂ]
          holomorphicOnX X (abelianExp X '' W),
        ∀ f (w : W),
          (e f : abelianExp X '' W → ℂ) ⟨abelianExp X w, Set.mem_image_of_mem _ w.2⟩ =
            (f : abelianExp X ⁻¹' (abelianExp X '' W) → ℂ)
              ⟨w, Set.subset_preimage_image _ _ w.2⟩ :=
  spec_restrictEquivX_aux X H E hE χ hχ W hW hdisj

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (v : Fin (dim X.left) → ℂ) :
    ∃ U : Set (ComplexPoint X), IsOpen U ∧ abelianExp X v ∈ U ∧
      Nonempty (sectionsOnX X (holFactor (datumOfX X H E hE χ hχ)) U ≃ₗ[ℂ]
        holomorphicOnX X U) := by
  obtain ⟨W, hW, hv, hdisj⟩ := spec_exists_disjoint_nhds (abelianPeriodLattice X) v
  obtain ⟨hU, e, -⟩ := spec_restrictEquivX X H E hE χ hχ W hW hdisj
  exact ⟨abelianExp X '' W, hU, Set.mem_image_of_mem _ hv, ⟨e⟩⟩

/-- The trivial factor gives upstream's structure sheaf: for open `U ⊆ X(ℂ)`, a `Λ`-invariant
holomorphic function on `exp⁻¹(U)` descends to a function on `U` that is holomorphic in
upstream's charts, and conversely. Descent uses S12 (`exp` onto, fibres `v + Λ`); holomorphy of
the descended function is local, near `exp v` it is `f ∘ e.symm` for the unif lane's local
biholomorphism `e` at `v`; the converse composes with the holomorphic `exp` (stage 4e).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §2.1;
`spec_complexExponential_localBiholomorph`, `spec_one_equiv_structureSheaf`. -/
theorem spec_one_equiv_holomorphicOnX (U : Set (ComplexPoint X)) (hU : IsOpen U) :
    ∃ e : sectionsOnX X 1 U ≃ₗ[ℂ] holomorphicOnX X U,
      ∀ f (x : abelianExp X ⁻¹' U),
        (e f : U → ℂ) ⟨abelianExp X x, x.2⟩ = (f : abelianExp X ⁻¹' U → ℂ) x :=
  spec_one_equiv_holomorphicOnX_aux X U hU

example (U : Set (ComplexPoint X)) (hU : IsOpen U) :
    Nonempty (sectionsOnX X 1 U ≃ₗ[ℂ] holomorphicOnX X U) :=
  let ⟨e, _⟩ := spec_one_equiv_holomorphicOnX X U hU; ⟨e⟩

/-- The zero set of a theta function is `Λ`-invariant, so its image in `X(ℂ)` pulls back to it:
`exp v = exp w` means `w = v + l` with `l ∈ Λ`, and `θ (v + l) = holFactor D l v * θ v` with a
factor that never vanishes (a unit-circle element times an exponential).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §4.1; S12
`complexExponentialLattice`. -/
theorem spec_preimage_thetaZeroLocusX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    abelianExp X ⁻¹' thetaZeroLocusX X θ = {v | θ v = 0} :=
  spec_preimage_thetaZeroLocusX_aux X H E hE χ hχ θ hθ

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (v : Fin (dim X.left) → ℂ) (l : abelianPeriodLattice X) (hv : θ v = 0) :
    θ (v + l) = 0 := by
  have h : v + l ∈ abelianExp X ⁻¹' thetaZeroLocusX X θ := by
    change abelianExp X (v + l) ∈ thetaZeroLocusX X θ
    rw [abelianExp_add_lattice]
    exact ⟨v, hv, rfl⟩
  rw [spec_preimage_thetaZeroLocusX X H E hE χ hχ θ hθ] at h
  exact h

/-- The zero locus of a theta function is closed in `X(ℂ)`: by `spec_preimage_thetaZeroLocusX`
and S12 surjectivity its complement is `exp({θ ≠ 0})`, which is open because `θ` is continuous
and `exp` is an open map.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1; S12
`isOpenMap_complexExponential`, `surjective_complexExponential`. -/
theorem spec_isClosed_thetaZeroLocusX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsClosed (thetaZeroLocusX X θ) :=
  spec_isClosed_thetaZeroLocusX_aux X H E hE χ hχ θ hθ

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsOpen (thetaZeroLocusX X θ)ᶜ :=
  (spec_isClosed_thetaZeroLocusX X H E hE χ hχ θ hθ).isOpen_compl

/-- The zero locus of a nonzero theta function has empty interior in `X(ℂ)`: the preimage of the
interior is open, contained in `{θ = 0}` by `spec_preimage_thetaZeroLocusX`, and nonempty if the
interior is (S12 surjectivity); but an entire `θ` vanishing on a nonempty open set is `0`, by the
one-variable identity theorem on each complex line through a point of that set.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1; Gunning–Rossi, *Analytic
Functions of Several Complex Variables*, Ch. I, §A, Theorem 6. -/
theorem spec_interior_thetaZeroLocusX (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) :
    interior (thetaZeroLocusX X θ) = ∅ :=
  spec_interior_thetaZeroLocusX_aux X H E hE χ hχ θ hθ hne

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) :
    thetaZeroLocusX X θ ≠ Set.univ := by
  intro h
  have hi := spec_interior_thetaZeroLocusX X H E hE χ hχ θ hθ hne
  rw [h, interior_univ] at hi
  exact Set.eq_empty_iff_forall_notMem.mp hi (abelianExp X 0) trivial

/-- Non-vacuity of the falsification on `X`: in positive dimension `Λ` has a nontrivial character,
for instance `l ↦ (-1)^{n₀(l)}` with `n₀` the first coordinate in S12's `ℤ`-basis of `Λ` (rank
`2g > 0`). With `H = 0` it is a semicharacter, so `datumOfX X 0 0 _ χ _` is a datum to which the
falsification example applies.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`Λ ≅ ℤ^{2g}`) and §2.2;
S12 `complexExponentialLatticeBasis` (`abelianLatticeBasis`). -/
theorem spec_exists_nontrivial_characterX (hg : 0 < dim X.left) :
    ∃ χ : abelianPeriodLattice X → Circle,
      (∀ l m, χ (l + m) = χ l * χ m) ∧ ∃ l, χ l ≠ 1 :=
  spec_exists_nontrivial_characterX_aux X hg

example (hg : 0 < dim X.left) :
    ∃ χ : abelianPeriodLattice X → Circle, ∃ l, χ l ≠ 1 := by
  obtain ⟨χ, -, h⟩ := spec_exists_nontrivial_characterX X hg
  exact ⟨χ, h⟩

end HodgeLean.Adapters
