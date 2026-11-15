import HodgeLean.Foundations.MatrixAlgGroupLieProofs

/-!
# Matrix algebraic groups and their Lie algebras (FROZEN SPEC)

Each theorem is the matching `_aux` theorem of `MatrixAlgGroupLieProofs.lean`.

Scope. A group is a `MatrixAlgGroup k n` (the wave-0 core: an ideal of equations and its zero
set in `GL_n(k)`, which is a subgroup). Nothing else is stored: the Lie algebra `g1_lieAlgebra G`
is constructed from the differentials at `1` of the **vanishing ideal** `g1_vanishingIdeal G`,
and the identity component `g1_identityComponent G` and connectedness `g1_IsConnected G` are
constructed from the Zariski topology `g1_zariski k n`. The statements are the classical
facts on Lie algebras of linear algebraic groups over an algebraically closed field `k`
(Borel, *Linear Algebraic Groups*, Ch. I), with characteristic zero where Borel needs it
(intersections, centralizers, recovery of a connected group from its Lie algebra). The
intersection statement carries Cartier's theorem: it is stated outright, with no smoothness
premise, so its proof has to derive the needed reducedness. The last statement is an
implication from `HodgeLieIsGk` to the equality of two connected matrix groups whose Lie
algebras are the complex spans of `hodgeLieAlgebra` and `gkLie`.

Not claimed: group schemes, non-reduced structure, quotients, the existence of an algebraic
group with a prescribed Lie algebra, or anything about the geometric Mumford–Tate group of an
abelian variety. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations

open MvPolynomial HodgeLean.Foundations.Program
open scoped TensorProduct

variable {k : Type*} [Field k] {n : ℕ}

/-- **Monotonicity.** A smaller group has a smaller Lie algebra.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.5 and AG.16.2. -/
theorem g1_lie_mono (G H : MatrixAlgGroup k n) (h : G.carrier ≤ H.carrier) :
    g1_lieAlgebra G ≤ g1_lieAlgebra H :=
  g1_lie_mono_aux G H h

example : g1_lieAlgebra (g1_SL k n) ≤ g1_lieAlgebra (g1_GL k n) :=
  g1_lie_mono _ _ le_top

/-- **Finite groups have zero Lie algebra.** This refutes the first draft's counterexample
(a): the group `{1}` presented by `(x - 1)²` has Lie algebra `0`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.5 (`dim 𝔤 = dim G`) and AG.16.2. -/
theorem g1_lieAlgebra_eq_bot_of_finite (G : MatrixAlgGroup k n) [Finite G.carrier] :
    g1_lieAlgebra G = ⊥ :=
  g1_lieAlgebra_eq_bot_of_finite_aux G

example : g1_lieAlgebra (g1_squareGroup k) = ⊥ :=
  g1_lieAlgebra_eq_bot_of_finite _

/-- **Finite connected groups are trivial.** This refutes the first draft's counterexample
(b): a finite group is not Zariski-connected unless it is `{1}`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2 (points are closed, `G°` has finite
index). -/
theorem g1_isConnected_iff_of_finite (G : MatrixAlgGroup k n) [Finite G.carrier] :
    g1_IsConnected G ↔ G.carrier = ⊥ :=
  g1_isConnected_iff_of_finite_aux G

example : g1_IsConnected (g1_squareGroup k) :=
  (g1_isConnected_iff_of_finite _).mpr rfl

/-- **The Lie algebra of `GL_n`** is all of `𝔤𝔩_n` over an infinite field.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.9 (`𝔤𝔩_n`). -/
theorem g1_lieAlgebra_GL [Infinite k] : g1_lieAlgebra (g1_GL k n) = ⊤ :=
  g1_lieAlgebra_GL_aux

example : g1_lieAlgebra (g1_GL ℂ 1) ≠ g1_lieAlgebra (g1_squareGroup ℂ) := by
  rw [g1_lieAlgebra_GL, g1_lieAlgebra_eq_bot_of_finite]
  exact top_ne_bot

/-- **The Lie algebra is a Lie subalgebra** of `𝔤𝔩_n`: it is closed under the commutator
bracket `⁅X, Y⁆ = XY - YX`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.5 and §3.9; Humphreys, *Linear Algebraic
Groups*, §9.1 and §9.2. -/
theorem g1_lie_mem [IsAlgClosed k] (G : MatrixAlgGroup k n)
    (X Y : Matrix (Fin n) (Fin n) k) (hX : X ∈ g1_lieAlgebra G) (hY : Y ∈ g1_lieAlgebra G) :
    X * Y - Y * X ∈ g1_lieAlgebra G :=
  g1_lie_mem_aux G X Y hX hY

example (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X ∈ g1_lieAlgebra (g1_SL ℂ n))
    (hY : Y ∈ g1_lieAlgebra (g1_SL ℂ n)) : X * Y - Y * X ∈ g1_lieAlgebra (g1_SL ℂ n) :=
  g1_lie_mem _ X Y hX hY

/-- **The identity component is algebraic:** the Zariski connected component of `1` is the
point set of a matrix algebraic group.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2; Humphreys, *Linear Algebraic Groups*,
§7.3. -/
theorem g1_exists_identityComponent [IsAlgClosed k] (G : MatrixAlgGroup k n) :
    ∃ I : MatrixAlgGroup k n, (I.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) =
      g1_identityComponent G :=
  g1_exists_identityComponent_aux G

example (Ω : Matrix (Fin n) (Fin n) ℂ) : ∃ I : MatrixAlgGroup ℂ n,
    (I.carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) =
      g1_identityComponent (g1_isometryGroup Ω) :=
  g1_exists_identityComponent _

/-- **The identity component has the same Lie algebra** as the group.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2 (`G°` is open in `G`) and §3.5 (the
tangent space at `e` depends only on a neighbourhood of `e`). -/
theorem g1_lie_identityComponent [IsAlgClosed k] (G : MatrixAlgGroup k n) :
    g1_lieOfSet (g1_identityComponent G) = g1_lieAlgebra G :=
  g1_lie_identityComponent_aux G

example : g1_lieOfSet (g1_identityComponent (g1_isometryGroup (1 : Matrix (Fin n) (Fin n) ℂ))) =
    g1_lieAlgebra (g1_isometryGroup (1 : Matrix (Fin n) (Fin n) ℂ)) :=
  g1_lie_identityComponent _

/-- **Centralizers are algebraic:** the centralizer in `G` of any set of invertible matrices is
the point set of a matrix algebraic group.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.7; Humphreys, *Linear Algebraic Groups*,
§8.2. -/
theorem g1_exists_centralizer (G : MatrixAlgGroup k n)
    (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    ∃ C : MatrixAlgGroup k n, C.carrier = G.carrier ⊓ Subgroup.centralizer S :=
  g1_exists_centralizer_aux G S

example (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    ∃ C : MatrixAlgGroup k n, C.carrier = (g1_GL k n).carrier ⊓ Subgroup.centralizer S :=
  g1_exists_centralizer _ S

/-- **Lie algebra of an intersection** in characteristic zero: `𝔩𝔦𝔢(G ∩ H) = 𝔤 ∩ 𝔥`.
No smoothness premise: the proof has to supply Cartier's reducedness.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §6.12; Humphreys, *Linear Algebraic Groups*,
§12.5 and §13.1; Cartier's reducedness theorem (Demazure–Gabriel, *Groupes algébriques*, II.6.1.1;
Oort, *Algebraic group schemes in characteristic zero are reduced*, Invent. Math. 2 (1966)). -/
theorem g1_lie_inf [IsAlgClosed k] [CharZero k] (G H I : MatrixAlgGroup k n)
    (hI : I.carrier = G.carrier ⊓ H.carrier) :
    g1_lieAlgebra I = g1_lieAlgebra G ⊓ g1_lieAlgebra H :=
  g1_lie_inf_aux G H I hI

example (g : ℕ) (I : MatrixAlgGroup ℂ (g + g))
    (hI : I.carrier = (g1_Sp ℂ g).carrier ⊓ (g1_diagTorus ℂ (g + g)).carrier) :
    g1_lieAlgebra I = g1_lieAlgebra (g1_Sp ℂ g) ⊓ g1_lieAlgebra (g1_diagTorus ℂ (g + g)) :=
  g1_lie_inf _ _ I hI

/-- **Lie algebra of a centralizer** in characteristic zero: it is the set of elements of `𝔤`
commuting with `S`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.11 and §9.1; Humphreys, *Linear Algebraic
Groups*, §13.4. -/
theorem g1_lie_centralizer [IsAlgClosed k] [CharZero k] (G C : MatrixAlgGroup k n)
    (S : Set (Matrix.GeneralLinearGroup (Fin n) k))
    (hC : C.carrier = G.carrier ⊓ Subgroup.centralizer S) :
    g1_lieAlgebra C = g1_lieAlgebra G ⊓ g1_lieCentralizer S :=
  g1_lie_centralizer_aux G C S hC

example (C : MatrixAlgGroup ℂ n) (S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hC : C.carrier = (g1_SL ℂ n).carrier ⊓ Subgroup.centralizer S) :
    g1_lieAlgebra C = g1_lieAlgebra (g1_SL ℂ n) ⊓ g1_lieCentralizer S :=
  g1_lie_centralizer _ C S hC

/-- **A connected group is determined by its Lie algebra** in characteristic zero.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §7.1; Humphreys, *Linear Algebraic Groups*,
§13.1. -/
theorem g1_eq_of_lie_eq [IsAlgClosed k] [CharZero k] (G H : MatrixAlgGroup k n)
    (hG : g1_IsConnected G) (hH : g1_IsConnected H)
    (hlie : g1_lieAlgebra G = g1_lieAlgebra H) : G.carrier = H.carrier :=
  g1_eq_of_lie_eq_aux G H hG hH hlie

example (G : MatrixAlgGroup ℂ n) (hG : g1_IsConnected G) (hGL : g1_IsConnected (g1_GL ℂ n))
    (hlie : g1_lieAlgebra G = ⊤) : G.carrier = ⊤ :=
  g1_eq_of_lie_eq G (g1_GL ℂ n) hG hGL (hlie.trans g1_lieAlgebra_GL.symm)

/-- **Adapter to `HodgeLieIsGk`.** In a basis `b` of `V_ℂ`, a connected matrix group whose Lie
algebra is the complex span of `hodgeLieAlgebra` equals a connected matrix group whose Lie
algebra is the complex span of `gkLie`, whenever `HodgeLieIsGk` holds. This is the implication
from the Lie-algebra equality `HodgeLieIsGk` to the group equality `Hg = G_k`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §7.1; Moonen, *An introduction to
Mumford–Tate groups* (2004), §2; PW v0.3, §2.3. -/
theorem g1_hodgeGroup_eq_gkGroup {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)}
    (hH : DirectSum.IsInternal H) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) {m : ℕ}
    (b : Module.Basis (Fin m) ℂ (ℂ ⊗[ℚ] V)) (Hg Gk : MatrixAlgGroup ℂ m)
    (hHg : g1_IsConnected Hg) (hGk : g1_IsConnected Gk)
    (hHgLie : g1_lieAlgebra Hg =
      (complexSpan (hodgeLieAlgebra H hH).toSubmodule).map (LinearMap.toMatrix b b).toLinearMap)
    (hGkLie : g1_lieAlgebra Gk =
      (complexSpan (gkLie E R J).toSubmodule).map (LinearMap.toMatrix b b).toLinearMap)
    (hIs : HodgeLieIsGk H hH E R J) : Hg.carrier = Gk.carrier :=
  g1_hodgeGroup_eq_gkGroup_aux hH E R J b Hg Gk hHg hGk hHgLie hGkLie hIs

example {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} (hH : DirectSum.IsInternal H)
    (E : LinearMap.BilinForm ℚ V) (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    {m : ℕ} (b : Module.Basis (Fin m) ℂ (ℂ ⊗[ℚ] V)) (Hg Gk : MatrixAlgGroup ℂ m)
    (hHg : g1_IsConnected Hg) (hGk : g1_IsConnected Gk)
    (hHgLie : g1_lieAlgebra Hg =
      (complexSpan (hodgeLieAlgebra H hH).toSubmodule).map (LinearMap.toMatrix b b).toLinearMap)
    (hGkLie : g1_lieAlgebra Gk =
      (complexSpan (gkLie E R J).toSubmodule).map (LinearMap.toMatrix b b).toLinearMap)
    (hIs : HodgeLieIsGk H hH E R J) : Hg.carrier = Gk.carrier :=
  g1_hodgeGroup_eq_gkGroup hH E R J b Hg Gk hHg hGk hHgLie hGkLie hIs

end HodgeLean.Foundations
