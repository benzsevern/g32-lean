import HodgeLean.Blocks.HodgeStructure.Polarisation
import HodgeLean.Foundations.Program.FoundationVocabDefs

/-!
# Abstract polarized variations of Hodge structure: definitions

The local system is a functor from Mathlib's `FundamentalGroupoid B` to finite-dimensional
rational vector spaces (the representation route; Mathlib has no locally constant sheaf API).
Over a simply connected subset `U` the groupoid of `U` is thin, so parallel transport inside
`U` is the image of the unique homotopy class of paths in `U`.

Mathlib has no holomorphic vector bundles with connections. The narrowest version used here:
the flat bundle `𝓛 ⊗ 𝒪_B` has fibre `ℂ ⊗[ℚ] 𝓛_b`; a section is holomorphic over a simply
connected open `U` when its flat coordinates (transport to a reference fibre) are `ω`-smooth,
that is complex analytic in charts; the connection is the derivative of the flat coordinates,
transported back. Holomorphic subbundles are those spanned locally by holomorphic frames.

The last section builds one instance, `d1_constVHS E : d1_PolarizedVHS E E`: the constant local
system `ℚ²` over `E` with the symplectic form and the weight-one filtration `F¹ = ℂ · (e₀ + i e₁)`.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

open HodgeBlocks

section Coordinates

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]

/-- Coordinates on a finite-dimensional complex vector space from Mathlib's chosen basis.
Source: Bourbaki, *Algèbre*, ch. II, §7 (finite bases); `Module.finBasis`. -/
def d1_coord (H : Type*) [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H] :
    H ≃ₗ[ℂ] (Fin (Module.finrank ℂ H) → ℂ) :=
  (Module.finBasis ℂ H).equivFun

example : (ℂ ≃ₗ[ℂ] (Fin (Module.finrank ℂ ℂ) → ℂ)) := d1_coord ℂ

/-- A map from a complex manifold to a finite-dimensional complex vector space is holomorphic
on `U` when its coordinates are `ω`-smooth (complex analytic in charts) on `U`.
Source: Huybrechts, *Complex Geometry*, §2.1; Mathlib `ContMDiffOn` with `n = ω`. -/
def d1_IsHolomorphicOn (f : B → H) (U : Set B) : Prop :=
  ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin (Module.finrank ℂ H) → ℂ) ω (d1_coord H ∘ f) U

example (U : Set E) : d1_IsHolomorphicOn E (fun _ : E ↦ (0 : ℂ)) U :=
  contMDiffOn_const

/-- The derivative of a map into a finite-dimensional complex vector space, in coordinates.
Source: Huybrechts, *Complex Geometry*, §2.1; Mathlib `mfderiv`. -/
def d1_flatDeriv (f : B → H) (b : B) (v : E) : H :=
  (d1_coord H).symm
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin (Module.finrank ℂ H) → ℂ) (d1_coord H ∘ f) b v)

example (b v : E) : ℂ := d1_flatDeriv E (fun _ : E ↦ (0 : ℂ)) b v

/-- A family of subspaces of a fixed space is holomorphic on `U` (a holomorphic map to a
Grassmannian) when it is spanned near each point of `U` by a holomorphic frame.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 0, §5 and ch. 1, §5;
Huybrechts, *Complex Geometry*, §2.2. -/
def d1_IsHolomorphicFamilyOn (G : B → Submodule ℂ H) (U : Set B) : Prop :=
  ∀ b₁ ∈ U, ∃ W : Set B, IsOpen W ∧ b₁ ∈ W ∧ W ⊆ U ∧
    ∃ (r : ℕ) (σ : Fin r → B → H), (∀ i, d1_IsHolomorphicOn E (σ i) W) ∧
      ∀ b ∈ W, LinearIndependent ℂ (fun i ↦ σ i b) ∧
        Submodule.span ℂ (Set.range fun i ↦ σ i b) = G b

example : d1_IsHolomorphicFamilyOn E (fun _ : E ↦ (⊥ : Submodule ℂ ℂ)) Set.univ :=
  fun _ _ ↦ ⟨Set.univ, isOpen_univ, Set.mem_univ _, subset_rfl, 0, Fin.elim0,
    fun i ↦ Fin.elim0 i, fun _ _ ↦ ⟨linearIndependent_empty_type, by simp⟩⟩

end Coordinates

section LocalSystem

/-- A local system of finite-dimensional rational vector spaces on `B`, as a representation of
the fundamental groupoid.
Source: Deligne, *Équations différentielles à points singuliers réguliers*, LNM 163, I.1;
Voisin, *Hodge Theory and Complex Algebraic Geometry I*, ch. 9. -/
structure d1_LocalSystem (B : Type*) [TopologicalSpace B] where
  functor : FundamentalGroupoid B ⥤ ModuleCat.{0} ℚ
  finite : ∀ b, Module.Finite ℚ (functor.obj b)

example (B : Type*) [TopologicalSpace B] : d1_LocalSystem B where
  functor := (Functor.const _).obj (ModuleCat.of ℚ ℚ)
  finite _ := inferInstanceAs (Module.Finite ℚ ℚ)

namespace d1_LocalSystem

variable {B : Type*} [TopologicalSpace B] (L : d1_LocalSystem B)

/-- The fibre of a local system at a point.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, ch. 9. -/
abbrev fiber (b : B) : Type := L.functor.obj (FundamentalGroupoid.mk b)

instance (b : B) : Module.Finite ℚ (L.fiber b) := L.finite _

/-- The fibre `ℂ ⊗ 𝓛_b` of the flat bundle `𝓛 ⊗ 𝒪_B`.
Source: Deligne, LNM 163, I.2; Voisin, *Hodge Theory I*, ch. 9. -/
abbrev cFiber (b : B) : Type := ℂ ⊗[ℚ] L.fiber b

example (b : B) : Module.Finite ℂ (L.cFiber b) := inferInstance

/-- Parallel transport along a homotopy class of paths.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, ch. 9. -/
def transport {b b' : B} (γ : Path.Homotopic.Quotient b b') : L.fiber b ≃ₗ[ℚ] L.fiber b' :=
  (L.functor.mapIso (asIso (show FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b' from γ))
    ).toLinearEquiv

example (b : B) (x : L.fiber b) : L.fiber b :=
  L.transport (Path.Homotopic.Quotient.mk (Path.refl b)) x

/-- The homotopy class in `B` of a path inside a simply connected subset `U`; every path in `U`
between the two points gives this class.
Source: Hatcher, *Algebraic Topology*, §1.1, Proposition 1.6. -/
def classIn (U : Set B) (hU : IsSimplyConnected U) (b b₀ : U) :
    Path.Homotopic.Quotient (b : B) b₀ :=
  haveI := hU.simplyConnectedSpace
  Path.Homotopic.Quotient.mk ((PathConnectedSpace.somePath b b₀).map continuous_subtype_val)

example (U : Set B) (hU : IsSimplyConnected U) (b : U) :
    classIn U hU b b = Path.Homotopic.Quotient.mk (Path.refl (b : B)) := by
  have := hU.simplyConnectedSpace
  unfold classIn
  apply Quotient.sound
  exact (SimplyConnectedSpace.paths_homotopic (PathConnectedSpace.somePath b b)
    (Path.refl b)).map ⟨Subtype.val, continuous_subtype_val⟩

/-- Complexified parallel transport inside a simply connected subset: the flat trivialisation
of `𝓛 ⊗ 𝒪` over `U`.
Source: Voisin, *Hodge Theory I*, ch. 9; Griffiths, Publ. Math. IHES 38, §1. -/
def flatTransport (U : Set B) (hU : IsSimplyConnected U) (b b₀ : U) :
    L.cFiber b ≃ₗ[ℂ] L.cFiber b₀ :=
  LinearEquiv.baseChange ℚ ℂ _ _ (L.transport (classIn U hU b b₀))

example (U : Set B) (hU : IsSimplyConnected U) (b : U) : L.cFiber b ≃ₗ[ℂ] L.cFiber b :=
  L.flatTransport U hU b b

open scoped Classical in
/-- The flat coordinates of a section over `U`, valued in the reference fibre at `b₀`.
Source: Voisin, *Hodge Theory I*, ch. 9. -/
def flatCoord (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (s : ∀ b, L.cFiber b) :
    B → L.cFiber b₀ :=
  fun b ↦ if h : b ∈ U then L.flatTransport U hU ⟨b, h⟩ b₀ (s b) else 0

example (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) : B → L.cFiber b₀ :=
  L.flatCoord U hU b₀ 0

open scoped Classical in
/-- The flat section over `U` through a vector of the reference fibre, extended by zero.
Source: Voisin, *Hodge Theory I*, ch. 9. -/
def flatSection (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (x : L.cFiber b₀) :
    ∀ b, L.cFiber b :=
  fun b ↦ if h : b ∈ U then (L.flatTransport U hU ⟨b, h⟩ b₀).symm x else 0

example (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) : ∀ b, L.cFiber b :=
  L.flatSection U hU b₀ 0

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E B]

/-- A section of `𝓛 ⊗ 𝒪_B` is holomorphic on the simply connected set `U` when its flat
coordinates are holomorphic there.
Source: Deligne, LNM 163, I.2.17; Voisin, *Hodge Theory I*, ch. 9. -/
def IsHolomorphicSectionOn (U : Set B) (hU : IsSimplyConnected U) (b₀ : U)
    (s : ∀ b, L.cFiber b) : Prop :=
  d1_IsHolomorphicOn E (L.flatCoord U hU b₀ s) U

example (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    L.IsHolomorphicSectionOn E U hU b₀ 0 := by
  have h : d1_coord _ ∘ L.flatCoord U hU b₀ 0 = fun _ ↦ 0 := by
    funext b
    by_cases hb : b ∈ U <;> simp [flatCoord, hb]
  show ContMDiffOn _ _ _ (d1_coord _ ∘ L.flatCoord U hU b₀ 0) U
  rw [h]
  exact contMDiffOn_const

/-- The flat connection `∇ = 1 ⊗ d` on `𝓛 ⊗ 𝒪_B` over `U`: differentiate the flat
coordinates and transport the result back to the fibre at `b`.
Source: Deligne, LNM 163, I.2.17 (the equivalence between local systems and flat connections);
Voisin, *Hodge Theory I*, ch. 9. -/
def connection (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (s : ∀ b, L.cFiber b)
    (b : U) (v : E) : L.cFiber b :=
  (L.flatTransport U hU b b₀).symm (d1_flatDeriv E (L.flatCoord U hU b₀ s) b v)

example (U : Set B) (hU : IsSimplyConnected U) (b₀ b : U) (v : E) : L.cFiber b :=
  L.connection E U hU b₀ 0 b v

/-- A family of subspaces `G_b ⊆ ℂ ⊗ 𝓛_b` is a holomorphic subbundle when, near each point, it
is spanned by a holomorphic frame on a simply connected open neighbourhood.
Source: Griffiths, Publ. Math. IHES 38, §1; Huybrechts, *Complex Geometry*, §2.2. -/
def IsHolomorphicSubbundle (G : ∀ b, Submodule ℂ (L.cFiber b)) : Prop :=
  ∀ b₁ : B, ∃ (U : Set B) (hU : IsSimplyConnected U) (h₁ : b₁ ∈ U), IsOpen U ∧
    ∃ (r : ℕ) (s : Fin r → ∀ b, L.cFiber b),
      (∀ i, L.IsHolomorphicSectionOn E U hU ⟨b₁, h₁⟩ (s i)) ∧
      ∀ b ∈ U, LinearIndependent ℂ (fun i ↦ s i b) ∧
        Submodule.span ℂ (Set.range fun i ↦ s i b) = G b

/-- Griffiths transversality `∇ F^p ⊆ F^{p-1} ⊗ Ω¹`: on every simply connected open set, the
covariant derivative of a holomorphic section of `F^p` lies in `F^{p-1}`.
Source: Griffiths, *Periods of integrals on algebraic manifolds II*, Amer. J. Math. 90 (1968),
§1; Voisin, *Hodge Theory I*, ch. 10. -/
def IsTransversal (F : ℤ → ∀ b, Submodule ℂ (L.cFiber b)) : Prop :=
  ∀ (U : Set B) (hU : IsSimplyConnected U), IsOpen U → ∀ (b₀ : U) (p : ℤ)
    (s : ∀ b, L.cFiber b), L.IsHolomorphicSectionOn E U hU b₀ s → (∀ b : U, s b ∈ F p b) →
      ∀ (b : U) (v : E), L.connection E U hU b₀ s b v ∈ F (p - 1) b

example : L.IsTransversal E (fun _ _ ↦ ⊤) := fun _ _ _ _ _ _ _ _ _ _ ↦ Submodule.mem_top

end d1_LocalSystem

end LocalSystem

section Filtration

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- A Hodge filtration of weight `n` on `ℂ ⊗ V`: decreasing, exhaustive, separated, and
`F^p ⊕ \bar F^{n-p+1} = ℂ ⊗ V` for every `p`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHES 40 (1971), §1.2; Voisin, *Hodge
Theory I*, ch. 7. -/
structure d1_IsHodgeFiltration (n : ℤ) (G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) : Prop where
  antitone : Antitone G
  exhaustive : ∃ a, G a = ⊤
  separated : ∃ c, G c = ⊥
  isCompl : ∀ p, IsCompl (G p) ((G (n - p + 1)).map (sigmaQ V))

omit [Module.Finite ℚ V] in
theorem d1_map_sigmaQ_top : (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)).map (sigmaQ V) = ⊤ := by
  rw [Submodule.map_top, LinearMap.range_eq_top]
  exact Function.Involutive.surjective (sigmaQ_involutive V)

example : d1_IsHodgeFiltration 0
    (fun p : ℤ ↦ if p ≤ 0 then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) else ⊥) := by
  refine ⟨fun a b h ↦ ?_, ⟨0, by simp⟩, ⟨1, by simp⟩, fun p ↦ ?_⟩
  · by_cases hb : b ≤ 0
    · simp [hb, h.trans hb]
    · simp [hb]
  · by_cases hp : p ≤ 0
    · have h₁ : ¬ (0 - p + 1 ≤ 0) := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hp), ite_eq_right_of_eq_false _ _ (eq_false h₁),
        Submodule.map_bot]
      exact isCompl_top_bot
    · have h₁ : 0 - p + 1 ≤ 0 := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hp), ite_eq_left_of_eq_true _ _ (eq_true h₁),
        d1_map_sigmaQ_top]
      exact isCompl_bot_top

/-- The Hodge pieces `H^{p,q} = F^p ∩ \bar F^q` for `p + q = n`, and `0` otherwise.
Source: Deligne, *Théorie de Hodge II*, §1.2; Voisin, *Hodge Theory I*, ch. 7. -/
def d1_hodgePiece (n : ℤ) (G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) :
    ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V) :=
  fun pq ↦ if pq.1 + pq.2 = n then G pq.1 ⊓ (G pq.2).map (sigmaQ V) else ⊥

omit [Module.Finite ℚ V] in
theorem d1_hodgePiece_supported (n : ℤ) (G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (pq : ℤ × ℤ)
    (h : pq.1 + pq.2 ≠ n) : d1_hodgePiece n G pq = ⊥ := by
  simp [d1_hodgePiece, h]

example (G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) : d1_hodgePiece 1 G (0, 0) = ⊥ :=
  d1_hodgePiece_supported 1 G (0, 0) (by norm_num)

/-- A polarized Hodge filtration of weight `n` for the rational form `Q`: a Hodge filtration,
`Q` nondegenerate and `(-1)^n`-symmetric, the first Hodge--Riemann relation
`Q(F^p, F^{n-p+1}) = 0`, and the second, `i^{p-q} Q(x, \bar x) > 0` on `H^{p,q} ∖ 0`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§2; Cattani--El Zein--Griffiths--Lê, *Hodge Theory* (2014), Chapter 3. -/
structure d1_IsPolarizedFiltration (n : ℤ) (Q : LinearMap.BilinForm ℚ V)
    (G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) : Prop where
  hodge : d1_IsHodgeFiltration n G
  nondegenerate : Q.Nondegenerate
  symm : ∀ x y, Q x y = ((-1 : ℚ) ^ n) * Q y x
  riemann_first : ∀ p, ∀ x ∈ G p, ∀ y ∈ G (n - p + 1), Q.baseChange ℂ x y = 0
  riemann_second : ∀ p q : ℤ, p + q = n → ∀ x ∈ d1_hodgePiece n G (p, q), x ≠ 0 →
    0 < (Iexp (p - q) * Q.baseChange ℂ x (sigmaQ V x)).re

/-- The period domain: polarized Hodge filtrations of weight `n` for `Q` with Hodge numbers
`f p = dim F^p`.
Source: Griffiths, Amer. J. Math. 90 (1968), §§2--3; Carlson--Müller-Stach--Peters, *Period
Mappings and Period Domains* (2017), ch. 4. -/
def d1_PeriodDomain (n : ℤ) (Q : LinearMap.BilinForm ℚ V) (f : ℤ → ℕ) :
    Set (ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) :=
  {G | d1_IsPolarizedFiltration n Q G ∧ ∀ p, Module.finrank ℂ (G p) = f p}

example (Q : LinearMap.BilinForm ℚ V) (f : ℤ → ℕ) : Set (ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) :=
  d1_PeriodDomain 1 Q f

end Filtration

section VHS

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A polarized variation of rational Hodge structure of weight `weight` over a complex
manifold `B`: a local system, a Hodge filtration by holomorphic subbundles of `𝓛 ⊗ 𝒪_B`
satisfying Griffiths transversality for the flat connection, and a flat rational form which
polarizes every fibre.
Source: Griffiths, Publ. Math. IHES 38 (1970), §§1--3; Schmid, Invent. Math. 22 (1973), §3;
Carlson--Müller-Stach--Peters, *Period Mappings and Period Domains*, ch. 4. -/
structure d1_PolarizedVHS (B : Type*) [TopologicalSpace B] [ChartedSpace E B]
    [IsManifold 𝓘(ℂ, E) ω B] where
  L : d1_LocalSystem B
  weight : ℤ
  F : ℤ → ∀ b, Submodule ℂ (L.cFiber b)
  Q : ∀ b, LinearMap.BilinForm ℚ (L.fiber b)
  holomorphic : ∀ p, L.IsHolomorphicSubbundle E (F p)
  transversal : L.IsTransversal E F
  flat : ∀ (b b' : B) (γ : Path.Homotopic.Quotient b b') (x y : L.fiber b),
    Q b' (L.transport γ x) (L.transport γ y) = Q b x y
  polarized : ∀ b, d1_IsPolarizedFiltration weight (Q b) (fun p ↦ F p b)

variable {E} {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

open scoped Classical in
/-- The period map on a simply connected set `U` with reference point `b₀`: transport the Hodge
filtration at `b` to the fibre at `b₀`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def d1_periodMap [IsManifold 𝓘(ℂ, E) ω B]
    (V : d1_PolarizedVHS E B) (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    B → ℤ → Submodule ℂ (V.L.cFiber b₀) :=
  fun b p ↦ if h : b ∈ U then (V.F p b).map (V.L.flatTransport U hU ⟨b, h⟩ b₀).toLinearMap
    else V.F p b₀

example [IsManifold 𝓘(ℂ, E) ω B]
    (V : d1_PolarizedVHS E B) (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    B → ℤ → Submodule ℂ (V.L.cFiber b₀) := d1_periodMap V U hU b₀

/-- The Hodge numbers `f^p = dim F^p` at a point.
Source: Griffiths, Amer. J. Math. 90 (1968), §2. -/
def d1_hodgeNumbers [IsManifold 𝓘(ℂ, E) ω B] (V : d1_PolarizedVHS E B) (b : B) : ℤ → ℕ :=
  fun p ↦ Module.finrank ℂ (V.F p b)

example [IsManifold 𝓘(ℂ, E) ω B] (V : d1_PolarizedVHS E B) (b : B) : ℤ → ℕ := d1_hodgeNumbers V b

variable (E) {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]

/-- A map to filtrations of a fixed space is horizontal on `U` when, on every open `W ⊆ U`,
the derivative of a holomorphic section of `F^p` lies in `F^{p-1}`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1 (horizontal distribution); Carlson--
Müller-Stach--Peters, ch. 4. -/
def d1_IsHorizontalOn (Φ : B → ℤ → Submodule ℂ H) (U : Set B) : Prop :=
  ∀ W : Set B, IsOpen W → W ⊆ U → ∀ (p : ℤ) (σ : B → H), d1_IsHolomorphicOn E σ W →
    (∀ b ∈ W, σ b ∈ Φ b p) → ∀ b ∈ W, ∀ v : E, d1_flatDeriv E σ b v ∈ Φ b (p - 1)

example (U : Set E) : d1_IsHorizontalOn E (fun _ _ ↦ (⊤ : Submodule ℂ ℂ)) U :=
  fun _ _ _ _ _ _ _ _ _ _ ↦ Submodule.mem_top

end VHS

section Chart

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

open scoped Classical in
/-- The affine chart of a Grassmannian at the step `p`: the projection onto `G^p` along the
fixed complement `\bar G₀^{n-p+1}`, or `0` when `G^p` is not a complement of it.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 1, §5 (Grassmannian charts);
Carlson--Müller-Stach--Peters, *Period Mappings and Period Domains*, ch. 4. -/
def d1_graphProjection (n : ℤ) (G₀ G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (p : ℤ) :
    Module.End ℂ (ℂ ⊗[ℚ] V) :=
  if h : IsCompl (G p) ((G₀ (n - p + 1)).map (sigmaQ V)) then
    (G p).subtype ∘ₗ (G p).projectionOnto _ h
  else 0

example (G₀ : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) : Module.End ℂ (ℂ ⊗[ℚ] V) :=
  d1_graphProjection 1 G₀ G₀ 1

/-- Filtrations whose steps `lo, …, lo + m - 1` are complements of the conjugate reference
steps: the domain of the chart `d1_chartCoord`.
Source: Carlson--Müller-Stach--Peters, ch. 4; Griffiths, Amer. J. Math. 90 (1968), §3. -/
def d1_chartDomainSet (n : ℤ) (G₀ : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (lo : ℤ) (m : ℕ) :
    Set (ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) :=
  {G | ∀ i : Fin m, IsCompl (G (lo + i)) ((G₀ (n - (lo + i) + 1)).map (sigmaQ V))}

example (G₀ : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) : G₀ ∈ d1_chartDomainSet 1 G₀ 0 0 :=
  fun i ↦ Fin.elim0 i

/-- Matrix coordinates of the graph projections at the steps `lo, …, lo + m - 1`, in Mathlib's
chosen basis of `ℂ ⊗ V`.
Source: Carlson--Müller-Stach--Peters, ch. 4. -/
def d1_chartCoord (n : ℤ) (G₀ : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (lo : ℤ) (m : ℕ)
    (G : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) :
    Fin m → Fin (Module.finrank ℂ (ℂ ⊗[ℚ] V)) → Fin (Module.finrank ℂ (ℂ ⊗[ℚ] V)) → ℂ :=
  fun i j k ↦ LinearMap.toMatrix (Module.finBasis ℂ _) (Module.finBasis ℂ _)
    (d1_graphProjection n G₀ G (lo + i)) j k

example (G₀ : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (lo : ℤ) (m : ℕ) :
    Fin m → Fin (Module.finrank ℂ (ℂ ⊗[ℚ] V)) → Fin (Module.finrank ℂ (ℂ ⊗[ℚ] V)) → ℂ :=
  d1_chartCoord 1 G₀ lo m G₀

end Chart

section PeriodChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

/-- The reference Hodge filtration at `b₀`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1. -/
def d1_refFiltration [IsManifold 𝓘(ℂ, E) ω B]
    (V : d1_PolarizedVHS E B) (b₀ : B) : ℤ → Submodule ℂ (V.L.cFiber b₀) :=
  fun p ↦ V.F p b₀

example [IsManifold 𝓘(ℂ, E) ω B]
    (V : d1_PolarizedVHS E B) (b₀ : B) : ℤ → Submodule ℂ (V.L.cFiber b₀) :=
  d1_refFiltration V b₀

/-- The open set of `U` on which the period map stays in the chart centred at the reference
filtration.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def d1_chartDomain [IsManifold 𝓘(ℂ, E) ω B]
    (V : d1_PolarizedVHS E B) (U : Set B) (hU : IsSimplyConnected U) (b₀ : U)
    (lo : ℤ) (m : ℕ) : Set B :=
  interior {b | b ∈ U ∧
    d1_periodMap V U hU b₀ b ∈ d1_chartDomainSet V.weight (d1_refFiltration V b₀) lo m}

example [IsManifold 𝓘(ℂ, E) ω B]
    (V : d1_PolarizedVHS E B) (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    IsOpen (d1_chartDomain V U hU b₀ 0 0) := isOpen_interior

/-- The period map in chart coordinates.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def d1_chartPeriod [IsManifold 𝓘(ℂ, E) ω B]
    (V : d1_PolarizedVHS E B) (U : Set B) (hU : IsSimplyConnected U) (b₀ : U)
    (lo : ℤ) (m : ℕ) :
    B → Fin m → Fin (Module.finrank ℂ (V.L.cFiber b₀)) →
      Fin (Module.finrank ℂ (V.L.cFiber b₀)) → ℂ :=
  fun b ↦ d1_chartCoord V.weight (d1_refFiltration V b₀) lo m (d1_periodMap V U hU b₀ b)

example [IsManifold 𝓘(ℂ, E) ω B]
    (V : d1_PolarizedVHS E B) (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (b : B) :
    Fin 0 → Fin (Module.finrank ℂ (V.L.cFiber b₀)) →
      Fin (Module.finrank ℂ (V.L.cFiber b₀)) → ℂ :=
  d1_chartPeriod V U hU b₀ 0 0 b

end PeriodChart


section ConstantExample

/-! ### The constant variation of weight one on `ℚ²`

The constant local system with fibre `ℚ²`, the standard symplectic form
`Q(x, y) = x₀ y₁ - x₁ y₀`, and the constant Hodge filtration `F⁰ = ℂ²`, `F¹ = ℂ · (e₀ + i e₁)`,
`F² = 0`, over the base `E` itself. This is a genuine `d1_PolarizedVHS E E`; its fibre is the
polarized Hodge structure `H¹` of an elliptic curve with period `i`. -/

/-- A complex normed space is simply connected.
Source: Hatcher, *Algebraic Topology*, §1.1 (convex sets are contractible); Mathlib
`RealTopologicalVectorSpace.contractibleSpace`. -/
theorem d1_isSimplyConnected_univ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsSimplyConnected (Set.univ : Set E) := by
  have : ContractibleSpace (Set.univ : Set E) := (Homeomorph.Set.univ E).contractibleSpace
  exact SimplyConnectedSpace.ofContractible _

/-- The constant local system with fibre `W`: every homotopy class of paths acts by the identity.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, ch. 9 (constant local
systems). -/
def d1_constLocalSystem (B : Type*) [TopologicalSpace B] (W : Type) [AddCommGroup W]
    [Module ℚ W] [Module.Finite ℚ W] : d1_LocalSystem B where
  functor := (Functor.const _).obj (ModuleCat.of ℚ W)
  finite _ := inferInstanceAs (Module.Finite ℚ W)

example (B : Type*) [TopologicalSpace B] (b : B) :
    Module.finrank ℚ ((d1_constLocalSystem B (Fin 2 → ℚ)).fiber b) = 2 :=
  Module.finrank_fin_fun ℚ

variable {B : Type*} [TopologicalSpace B]
variable (W : Type) [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]

theorem d1_constLocalSystem_transport {b b' : B} (γ : Path.Homotopic.Quotient b b')
    (x : (d1_constLocalSystem B W).fiber b) : (d1_constLocalSystem B W).transport γ x = x :=
  rfl

theorem d1_constLocalSystem_flatTransport (U : Set B) (hU : IsSimplyConnected U) (b b₀ : U)
    (x : (d1_constLocalSystem B W).cFiber b) :
    (d1_constLocalSystem B W).flatTransport U hU b b₀ x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c w => rfl
  | add x y hx hy => exact (map_add _ _ _).trans (by rw [hx, hy]; rfl)

/-- The standard symplectic form `Q(x, y) = x₀ y₁ - x₁ y₀` on `ℚ²`.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 2, §6 (the intersection form
on `H¹` of a curve); Birkenhake--Lange, *Complex Abelian Varieties*, §3.1. -/
def d1_sympForm : LinearMap.BilinForm ℚ (Fin 2 → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y ↦ x 0 * y 1 - x 1 * y 0)
    (fun _ _ _ ↦ by simp only [Pi.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [Pi.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem d1_sympForm_apply (x y : Fin 2 → ℚ) :
    d1_sympForm x y = x 0 * y 1 - x 1 * y 0 := rfl

example : d1_sympForm (Pi.single 0 1) (Pi.single 1 1) = 1 := by simp

/-- The vector `e₀ + i e₁` of `ℂ ⊗ ℚ²`, spanning `H^{1,0}` of the weight-one example.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, §3.1 (period matrix `(1, i)`). -/
def d1_hodgeVector : ℂ ⊗[ℚ] (Fin 2 → ℚ) :=
  (1 : ℂ) ⊗ₜ Pi.single 0 1 + Complex.I ⊗ₜ Pi.single 1 1

example : ℂ ⊗[ℚ] (Fin 2 → ℚ) := d1_hodgeVector

theorem d1_sigmaQ_hodgeVector : sigmaQ (Fin 2 → ℚ) d1_hodgeVector =
    (1 : ℂ) ⊗ₜ Pi.single 0 1 - Complex.I ⊗ₜ Pi.single 1 1 := by
  show sigmaQR _ _ = _
  simp [d1_hodgeVector, sub_eq_add_neg, TensorProduct.neg_tmul]

local notation "W2" => (Fin 2 → ℚ)
local notation "QC" => d1_sympForm.baseChange ℂ

theorem d1_QC_vv : QC d1_hodgeVector d1_hodgeVector = 0 := by
  simp [d1_hodgeVector, LinearMap.BilinForm.baseChange_tmul]

theorem d1_QC_vσv : QC d1_hodgeVector (sigmaQ _ d1_hodgeVector) = -2 * Complex.I := by
  rw [d1_sigmaQ_hodgeVector]
  simp [d1_hodgeVector, LinearMap.BilinForm.baseChange_tmul]
  ring

theorem d1_QC_σvv : QC (sigmaQ _ d1_hodgeVector) d1_hodgeVector = 2 * Complex.I := by
  rw [d1_sigmaQ_hodgeVector]
  simp [d1_hodgeVector, LinearMap.BilinForm.baseChange_tmul]
  ring

open scoped Classical in
/-- The weight-one Hodge filtration `F⁰ = ℂ ⊗ ℚ²`, `F¹ = ℂ · (e₀ + i e₁)`, `F² = 0`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§2; Birkenhake--Lange, *Complex Abelian Varieties*, §3.1. -/
def d1_weightOneFiltration : ℤ → Submodule ℂ (ℂ ⊗[ℚ] W2) :=
  fun p ↦ if p ≤ 0 then ⊤ else if p = 1 then ℂ ∙ d1_hodgeVector else ⊥

example : d1_weightOneFiltration 2 = ⊥ := by simp [d1_weightOneFiltration]

theorem d1_hodgeVector_ne_zero : d1_hodgeVector ≠ 0 := by
  intro h
  have := d1_QC_vσv
  rw [h, map_zero, LinearMap.zero_apply] at this
  simp at this

theorem d1_sigmaQ_hodgeVector_ne_zero : sigmaQ W2 d1_hodgeVector ≠ 0 := by
  intro h
  have := d1_QC_σvv
  rw [h, map_zero, LinearMap.zero_apply] at this
  simp at this

theorem d1_map_sigmaQ_span :
    (ℂ ∙ d1_hodgeVector).map (sigmaQ W2) = ℂ ∙ sigmaQ W2 d1_hodgeVector := by
  rw [Submodule.map_span, Set.image_singleton]

theorem d1_isCompl_line :
    IsCompl (ℂ ∙ d1_hodgeVector) ((ℂ ∙ d1_hodgeVector).map (sigmaQ W2)) := by
  rw [d1_map_sigmaQ_span]
  have hdisj : Disjoint (ℂ ∙ d1_hodgeVector) (ℂ ∙ sigmaQ W2 d1_hodgeVector) := by
    rw [Submodule.disjoint_def]
    intro x hx hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hy
    have h := congrArg (QC d1_hodgeVector) hd
    rw [map_smul, map_smul, d1_QC_vv, d1_QC_vσv] at h
    have hd0 : d = 0 := by
      have : d * (-2 * Complex.I) = 0 := by simpa using h
      simpa [Complex.I_ne_zero] using this
    rw [← hd, hd0, zero_smul]
  refine ⟨hdisj, codisjoint_iff.mpr (Submodule.eq_top_of_finrank_eq ?_)⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ℂ ∙ d1_hodgeVector)
    (ℂ ∙ sigmaQ W2 d1_hodgeVector)
  rw [disjoint_iff.mp hdisj, finrank_bot, finrank_span_singleton d1_hodgeVector_ne_zero,
    finrank_span_singleton d1_sigmaQ_hodgeVector_ne_zero] at h
  rw [Module.finrank_baseChange, Module.finrank_fin_fun]
  omega

theorem d1_weightOneFiltration_isHodge : d1_IsHodgeFiltration 1 d1_weightOneFiltration := by
  refine ⟨fun a b hab ↦ ?_, ⟨0, by simp [d1_weightOneFiltration]⟩,
    ⟨2, by simp [d1_weightOneFiltration]⟩, fun p ↦ ?_⟩
  · simp only [d1_weightOneFiltration]
    split_ifs <;> first | exact le_top | exact bot_le | exact le_rfl | omega
  · simp only [d1_weightOneFiltration]
    split_ifs <;> first
      | omega
      | (rw [Submodule.map_bot]; exact isCompl_top_bot)
      | (rw [d1_map_sigmaQ_top]; exact isCompl_bot_top)
      | (subst_vars; exact d1_isCompl_line)

theorem d1_sympForm_nondegenerate : d1_sympForm.Nondegenerate := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · have h0 := hx (Pi.single 0 1)
    have h1 := hx (Pi.single 1 1)
    simp at h0 h1
    funext i; fin_cases i <;> simp [h0, h1]
  · have h0 := hy (Pi.single 0 1)
    have h1 := hy (Pi.single 1 1)
    simp at h0 h1
    funext i; fin_cases i <;> simp [h0, h1]

theorem d1_mem_weightOne_le (p : ℤ) (x : ℂ ⊗[ℚ] W2) (hx : x ∈ d1_weightOneFiltration p)
    (hp : 2 ≤ p) : x = 0 := by
  have : ¬ p ≤ 0 := by omega
  have h' : p ≠ 1 := by omega
  simpa [d1_weightOneFiltration, this, h'] using hx

/-- The weight-one filtration is polarized by the symplectic form: the Hodge--Riemann relations
for `H¹` of an elliptic curve.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§2; Birkenhake--Lange, *Complex Abelian Varieties*, §4.2 (Riemann relations). -/
theorem d1_weightOneFiltration_isPolarized :
    d1_IsPolarizedFiltration 1 d1_sympForm d1_weightOneFiltration where
  hodge := d1_weightOneFiltration_isHodge
  nondegenerate := d1_sympForm_nondegenerate
  symm x y := by simp; ring
  riemann_first p x hx y hy := by
    rcases lt_trichotomy p 1 with hp | rfl | hp
    · rw [d1_mem_weightOne_le _ y hy (by omega), map_zero]
    · have h1 : ¬ (1 : ℤ) ≤ 0 := by omega
      have hx' : x ∈ ℂ ∙ d1_hodgeVector := by simpa [d1_weightOneFiltration, h1] using hx
      have hy' : y ∈ ℂ ∙ d1_hodgeVector := by simpa [d1_weightOneFiltration, h1] using hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx'
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy'
      rw [map_smul, map_smul, LinearMap.smul_apply, d1_QC_vv, smul_zero, smul_zero]
    · rw [d1_mem_weightOne_le _ x hx (by omega), map_zero, LinearMap.zero_apply]
  riemann_second p q hpq x hx hx0 := by
    simp only [d1_hodgePiece, hpq, ite_true, Submodule.mem_inf] at hx
    obtain ⟨hxp, hxq⟩ := hx
    rcases lt_trichotomy p 0 with hp | rfl | hp
    · exfalso; apply hx0
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hxq
      rw [d1_mem_weightOne_le _ y hy (by omega), map_zero]
    · obtain rfl : q = 1 := by omega
      have h1 : ¬ (1 : ℤ) ≤ 0 := by omega
      rw [show d1_weightOneFiltration 1 = ℂ ∙ d1_hodgeVector by simp [d1_weightOneFiltration],
        d1_map_sigmaQ_span] at hxq
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxq
      have hc : c ≠ 0 := by rintro rfl; simp at hx0
      rw [(sigmaQ W2).map_smulₛₗ, sigmaQ_involutive, map_smul, map_smul, LinearMap.smul_apply,
        d1_QC_σvv]
      simp only [smul_eq_mul, Iexp]
      have : Complex.I ^ ((0 : ℤ) - 1) = -Complex.I := by
        rw [zero_sub, zpow_neg, zpow_one, Complex.inv_I]
      rw [this]
      have h2 : -Complex.I * ((starRingEnd ℂ) c * (c * (2 * Complex.I))) =
          2 * (c * (starRingEnd ℂ) c) := by ring_nf; rw [Complex.I_sq]; ring
      rw [h2, Complex.mul_conj]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      norm_num
      exact hc
    · obtain rfl : p = 1 := by
        by_contra h
        apply hx0
        exact d1_mem_weightOne_le _ x hxp (by omega)
      obtain rfl : q = 0 := by omega
      have h1 : ¬ (1 : ℤ) ≤ 0 := by omega
      have hxp' : x ∈ ℂ ∙ d1_hodgeVector := by simpa [d1_weightOneFiltration, h1] using hxp
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxp'
      have hc : c ≠ 0 := by rintro rfl; simp at hx0
      rw [(sigmaQ W2).map_smulₛₗ, map_smul, map_smul, LinearMap.smul_apply, d1_QC_vσv]
      simp only [smul_eq_mul, Iexp]
      have : Complex.I ^ ((1 : ℤ) - 0) = Complex.I := by simp
      rw [this]
      have h2 : Complex.I * ((starRingEnd ℂ) c * (c * (-2 * Complex.I))) =
          2 * (c * (starRingEnd ℂ) c) := by ring_nf; rw [Complex.I_sq]; ring
      rw [h2, Complex.mul_conj]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      norm_num
      exact hc

example : d1_IsPolarizedFiltration 1 d1_sympForm d1_weightOneFiltration :=
  d1_weightOneFiltration_isPolarized

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A constant family of subspaces of the fibre of a constant local system is a holomorphic
subbundle: a basis of the subspace gives a constant flat holomorphic frame on all of `E`.
Source: Griffiths, Publ. Math. IHES 38, §1; Huybrechts, *Complex Geometry*, §2.2. -/
theorem d1_const_isHolomorphicSubbundle (G : Submodule ℂ (ℂ ⊗[ℚ] W)) :
    (d1_constLocalSystem E W).IsHolomorphicSubbundle E (fun _ ↦ G) := by
  intro b₁
  let β := Module.finBasis ℂ G
  refine ⟨Set.univ, d1_isSimplyConnected_univ E, Set.mem_univ _, isOpen_univ,
    Module.finrank ℂ G, fun i _ ↦ (β i : ℂ ⊗[ℚ] W), fun i ↦ ?_, fun b _ ↦ ⟨?_, ?_⟩⟩
  · have h : (d1_coord _ ∘ (d1_constLocalSystem E W).flatCoord Set.univ
        (d1_isSimplyConnected_univ E) ⟨b₁, Set.mem_univ _⟩ (fun _ ↦ (β i : ℂ ⊗[ℚ] W))) =
        fun _ ↦ d1_coord (ℂ ⊗[ℚ] W) (β i) := by
      funext b
      simp only [Function.comp_apply, d1_LocalSystem.flatCoord, Set.mem_univ, dite_true]
      exact congrArg (d1_coord _) (d1_constLocalSystem_flatTransport W Set.univ _ _ _ _)
    show ContMDiffOn _ _ _ (d1_coord _ ∘ _) _
    rw [h]
    exact contMDiffOn_const
  · exact β.linearIndependent.map' G.subtype (Submodule.ker_subtype G)
  · show Submodule.span ℂ (Set.range fun i ↦ (β i : ℂ ⊗[ℚ] W)) = G
    calc Submodule.span ℂ (Set.range fun i ↦ (β i : ℂ ⊗[ℚ] W))
        = (Submodule.span ℂ (Set.range β)).map G.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]; rfl
      _ = G := by rw [β.span_eq, Submodule.map_top, Submodule.range_subtype]

example : (d1_constLocalSystem E W2).IsHolomorphicSubbundle E
    (fun _ ↦ d1_weightOneFiltration 1) :=
  d1_const_isHolomorphicSubbundle W2 E _

theorem d1_constWeightOne_transversal :
    (d1_constLocalSystem E W2).IsTransversal E (fun p _ ↦ d1_weightOneFiltration p) := by
  intro U hU _ b₀ p s _ hsF b v
  by_cases hp : p ≤ 1
  · have : d1_weightOneFiltration (p - 1) = ⊤ := by
      simp [d1_weightOneFiltration, show p - 1 ≤ 0 by omega]
    show _ ∈ d1_weightOneFiltration (p - 1)
    rw [this]
    exact Submodule.mem_top
  · have hs0 : ∀ b' : U, s b' = 0 := fun b' ↦
      d1_mem_weightOne_le p _ (hsF b') (by omega)
    have hc : (d1_constLocalSystem E W2).flatCoord U hU b₀ s = fun _ ↦ 0 := by
      funext b'
      by_cases hb : b' ∈ U
      · simp only [d1_LocalSystem.flatCoord, hb, dite_true]
        rw [hs0 ⟨b', hb⟩, map_zero]
      · simp [d1_LocalSystem.flatCoord, hb]
    have hd : d1_flatDeriv E (fun _ : E ↦ (0 : (d1_constLocalSystem E W2).cFiber b₀))
        b v = 0 := by
      have : (d1_coord _ ∘ fun _ : E ↦ (0 : (d1_constLocalSystem E W2).cFiber b₀)) =
          fun _ ↦ 0 := by funext; simp
      rw [d1_flatDeriv, this, mfderiv_const]
      exact map_zero _
    simp only [d1_LocalSystem.connection, hc, hd, map_zero]
    exact Submodule.zero_mem _

/-- The constant polarized variation of weight one over `E`: the constant local system `ℚ²`,
the symplectic form, and the constant filtration with `F¹ = ℂ · (e₀ + i e₁)`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1 (constant variations); Carlson--Müller-Stach--
Peters, *Period Mappings and Period Domains*, ch. 4. -/
def d1_constVHS : d1_PolarizedVHS E E where
  L := d1_constLocalSystem E W2
  weight := 1
  F p _ := d1_weightOneFiltration p
  Q _ := d1_sympForm
  holomorphic p := d1_const_isHolomorphicSubbundle W2 E (d1_weightOneFiltration p)
  transversal := d1_constWeightOne_transversal E
  flat _ _ _ _ _ := rfl
  polarized _ := d1_weightOneFiltration_isPolarized

example : d1_PolarizedVHS ℂ ℂ := d1_constVHS ℂ

example (b : E) : d1_hodgeNumbers (d1_constVHS E) b 0 = 2 := by
  have h : d1_weightOneFiltration 0 = ⊤ := by simp [d1_weightOneFiltration]
  show Module.finrank ℂ (d1_weightOneFiltration 0) = 2
  rw [h, finrank_top, Module.finrank_baseChange, Module.finrank_fin_fun]

end ConstantExample

end HodgeLean.Foundations.Program
