module

public import HodgeLean.Foundations.Program.SchoenExceptionalProofs

/-! # S3 frozen specification: local calculation and a proper-map foundation

Implication from explicit local branch equations and faithful characters to local
linear vanishing; implication from fibrewise sheaf vanishing to global vanishing.
The model calculation uses actual singular cohomology of disjoint Riemann spheres.
An identification with the exceptional divisor of Schoen's actual resolution,
and its character sheaf, is not supplied. See `docs/specs/spec-s3.md`.
HC no distance; AV milestone no distance.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The total transform in the chart `y = x t`, `u = x v` factors by `x^m`.
Source: G32 v0.16, Lemma 4.3 and its preceding construction; local equation
`u^m = x^a y^(m-a)` for a paired branch intersection. -/
theorem s3_blowup_chart (m a : ℕ) (ha : a ≤ m) (x t v : ℂ) :
    (x * v) ^ m - x ^ a * (x * t) ^ (m - a) =
      x ^ m * (v ^ m - t ^ (m - a)) :=
  s3_blowup_chart_aux m a ha x t v

example (m a : ℕ) (ha : a ≤ m) (x t v : ℂ) :
    (x * v) ^ m - x ^ a * (x * t) ^ (m - a) =
      x ^ m * (v ^ m - t ^ (m - a)) :=
  s3_blowup_chart m a ha x t v

/-- A faithful-character function vanishes at a point with nontrivial inertia.
The equation fixes the convention for the action on functions.
Source: G32 v0.16, Lemma 4.3, permutation-stalk argument. -/
theorem s3_inertia_stalk (G Ω : Type) [Group G] [MulAction G Ω]
    (χ : G →* ℂˣ) (hχ : Function.Injective χ) (f : Ω → ℂ)
    (hf : ∀ g x, f (g • x) = (χ g : ℂ) * f x)
    (x : Ω) (g : G) (hg : g ≠ 1) (hfix : g • x = x) : f x = 0 :=
  s3_inertia_stalk_aux G Ω χ hχ f hf x g hg hfix

example (G Ω : Type) [Group G] [MulAction G Ω]
    (χ : G →* ℂˣ) (hχ : Function.Injective χ) (f : Ω → ℂ)
    (hf : ∀ g x, f (g • x) = (χ g : ℂ) * f x)
    (x : Ω) (g : G) (hg : g ≠ 1) (hfix : g • x = x) : f x = 0 :=
  s3_inertia_stalk G Ω χ hχ f hf x g hg hfix

/-- The circle cochain differential for a primitive character and nonzero exponent
is invertible. No prime-selection premise is used.
Source: G32 v0.16, Lemma 4.3, nontrivial local monodromy; the cellular
cochain differential on a circle is monodromy minus identity. -/
theorem s3_monodromy_differential (m a : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (ha : ¬ m ∣ a) : Function.Bijective (fun z : ℂ => (ζ ^ a - 1) * z) :=
  s3_monodromy_differential_aux m a ζ hζ ha

example (m a : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (ha : ¬ m ∣ a) : Function.Bijective (fun z : ℂ => (ζ ^ a - 1) * z) :=
  s3_monodromy_differential m a ζ hζ ha

/-- After one circuit of the components the model map is homotopic to identity.
Source: G32 v0.16, Lemma 4.3, two-point fibre; complex dilation on the
Riemann sphere is isotopic to identity through nonzero complex dilations. -/
theorem s3_fibre_iterate_homotopic (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    ContinuousMap.Homotopic
      ⟨(s3_deck d c hc)^[d], (s3_deck d c hc).continuous.iterate d⟩
      (ContinuousMap.id (s3_Fibre d)) :=
  s3_fibre_iterate_homotopic_aux d hd c hc

example (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    ContinuousMap.Homotopic
      ⟨(s3_deck d c hc)^[d], (s3_deck d c hc).continuous.iterate d⟩
      (ContinuousMap.id (s3_Fibre d)) :=
  s3_fibre_iterate_homotopic d hd c hc

/-- Only characters factoring through the permutation of components occur in the
cohomology of this model, in every degree including zero.
Source: G32 v0.16, Lemma 4.3, exceptional-fibre vanishing; homotopy invariance
of singular cohomology applied to the component circuit. -/
theorem s3_fibre_eigen_vanishing (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0)
    (μ : ℂ) (hμ : μ ^ d ≠ 1) (n : ℕ)
    (v : Cohomology ℂ (TopCat.of (s3_Fibre d)) n)
    (hv : cohomologyMap ℂ n (TopCat.ofHom ⟨s3_deck d c hc, (s3_deck d c hc).continuous⟩) v = μ • v) :
    v = 0 :=
  s3_fibre_eigen_vanishing_aux d hd c hc μ hμ n v hv

example (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0)
    (μ : ℂ) (hμ : μ ^ d ≠ 1) (n : ℕ)
    (v : Cohomology ℂ (TopCat.of (s3_Fibre d)) n)
    (hv : cohomologyMap ℂ n (TopCat.ofHom ⟨s3_deck d c hc, (s3_deck d c hc).continuous⟩) v = μ • v) :
    v = 0 :=
  s3_fibre_eigen_vanishing d hd c hc μ hμ n v hv

/-- The primitive part vanishes on the model with `gcd(m,a)` components, for every
nonzero exponent modulo `m`, irrespective of the available primes.
Source: G32 v0.16, Lemma 4.3; normalization of the two-point cyclic cover
has `gcd(m,a)` components and each maps with degree `m/gcd(m,a)`. -/
theorem s3_primitive_fibre_vanishing (m a : ℕ) (hm : 0 < m) (ha : ¬ m ∣ a)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (c : ℂ) (hc : c ≠ 0) (n : ℕ)
    (v : Cohomology ℂ (TopCat.of (s3_Fibre (Nat.gcd m a))) n)
    (hv : cohomologyMap ℂ n
      (TopCat.ofHom ⟨s3_deck (Nat.gcd m a) c hc, (s3_deck (Nat.gcd m a) c hc).continuous⟩) v = ζ • v) : v = 0 :=
  s3_primitive_fibre_vanishing_aux m a hm ha ζ hζ c hc n v hv

example (m a : ℕ) (hm : 0 < m) (ha : ¬ m ∣ a)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (c : ℂ) (hc : c ≠ 0) (n : ℕ)
    (v : Cohomology ℂ (TopCat.of (s3_Fibre (Nat.gcd m a))) n)
    (hv : cohomologyMap ℂ n
      (TopCat.ofHom ⟨s3_deck (Nat.gcd m a) c hc, (s3_deck (Nat.gcd m a) c hc).continuous⟩) v = ζ • v) : v = 0 :=
  s3_primitive_fibre_vanishing m a hm ha ζ hζ c hc n v hv

/-- A sheaf with zero cohomology on every fibre of a proper map has zero global
cohomology. The premise includes degree zero and all higher degrees.
Source: Schapira, An Introduction to Categories and Sheaves, version 2023-10-01,
Theorem 11.3.6, followed by Leray, as used in G32 v0.16, Lemma 4.3. -/
theorem s3_proper_fibre_vanishing (X Y : TopCat) [T2Space X] [T2Space Y]
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (hF : ∀ (y : Y) (q : ℕ), Subsingleton
      (CategoryTheory.Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat
        (s3_fibreInclusion p y)).obj F) q)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F n) :=
  s3_proper_fibre_vanishing_aux X Y p hp F hF n

example (X Y : TopCat) [T2Space X] [T2Space Y]
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (hF : ∀ (y : Y) (q : ℕ), Subsingleton
      (CategoryTheory.Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat
        (s3_fibreInclusion p y)).obj F) q)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F n) :=
  s3_proper_fibre_vanishing X Y p hp F hF n

end HodgeLean.Foundations.Program
