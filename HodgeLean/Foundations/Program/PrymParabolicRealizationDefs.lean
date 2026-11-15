import HodgeLean.Foundations.Program.PrymFamilyB4Defs

/-! # Definitions for stage H3b: cellular homology of the lifted complex of G32 Figure 1

For a group `G` and a tuple `g₀, …, g_{r−1}` in `G`, the lifted Δ-complex `X̃(g)` of stage H3a
(`docs/specs/PrymParabolicComparison.md`): vertices `b₀(x)`, `b_∞(x)` and `p_i(x⟨g_i⟩)`, edges
`e_i(x) : b₀(x) → p_i(x⟨g_i⟩)`, `f_i(x) : b₀(x) → b_∞(x Q_i⁻¹)`,
`h_i(x) : p_i(x⟨g_i⟩) → b_∞(x Q_i⁻¹)`, triangles `A_i(x)` with faces `h_i(x), f_i(x), e_i(x)` and
`B_i(x)` with faces `h_i(x g_i⁻¹), f_{i+1}(x), e_i(x)`. The cell definitions below repeat those of
`PrymParabolicComparisonDefs` clause by clause, under the prefix `hg2_`. H3a is on `main`
(F-2205); these definitions agree definitionally, so identification need not wait for the
marked root cover.

New here: integral (and `R`-linear) cellular chains, the boundary maps `∂₁, ∂₂`, cellular `H₁`,
the deck action on chains and on `H₁`, the orientation chain `Σ_x Σ_i (A_i(x) − B_i(x))`, the
evaluation pairing of cochains with chains, and the B6-3b primitive projector
`Σ_h b4b_projectorCoeff h · h_*` on cellular `H₁(X̃(b4b_root); ℤ)`.

Nothing here identifies the realization of `X̃(g)` with a marked cover of the punctured sphere,
or cellular with singular homology. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Program

/-! ## The cells (as in stage H3a) -/

/-- The vertices of the lifted complex: `b₀(x)` (`Sum.inl x`), `b_∞(x)` (`Sum.inr (Sum.inl x)`)
and `p_i(x⟨g_i⟩)` (`Sum.inr (Sum.inr ⟨i, x⟨g_i⟩⟩)`); the same type as `hg_Vert` of stage H3a.
Source: G32 v0.16, Lemma 6.2 and Figure 1; Hatcher, *Algebraic Topology*, §2.1 and §1.3. -/
abbrev hg2_Vert {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : Type _ :=
  G ⊕ G ⊕ (Σ i : Fin r, G ⧸ Subgroup.zpowers (g i))

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (x : G) : hg2_Vert g := Sum.inl x

/-- The edges of the lifted complex: `e_i(x)` (`Sum.inl (i, x)`), `f_i(x)`
(`Sum.inr (Sum.inl (i, x))`) and `h_i(x)` (`Sum.inr (Sum.inr (i, x))`); as `hg_Edge`.
Source: G32 v0.16, Lemma 6.2 and Figure 1; Hatcher, §2.1. -/
abbrev hg2_Edge (G : Type*) (r : ℕ) : Type _ := (Fin r × G) ⊕ (Fin r × G) ⊕ (Fin r × G)

example (G : Type*) (x : G) : hg2_Edge G 1 := Sum.inl (0, x)

/-- The triangles of the lifted complex: `A_i(x)` (`Sum.inl (i, x)`) and `B_i(x)`
(`Sum.inr (i, x)`), with vertices `[b₀, p_i, b_∞]`; as `hg_Tri`.
Source: G32 v0.16, Lemma 6.2 and Figure 1; Hatcher, §2.1. -/
abbrev hg2_Tri (G : Type*) (r : ℕ) : Type _ := (Fin r × G) ⊕ (Fin r × G)

example (G : Type*) (x : G) : hg2_Tri G 1 := Sum.inr (0, x)

/-- `Q_i = g₀ ⋯ g_{i−1}` in `G`; as `hg_Q`.
Source: G32 v0.16, before Lemma 6.2. -/
def hg2_Q {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) : G :=
  (((List.finRange r).filter fun j => j < i).map g).prod

example {G : Type*} [Group G] {r : ℕ} (g : Fin (r + 1) → G) : hg2_Q g 0 = 1 := by
  simp [hg2_Q]

/-- The initial vertex of an edge; as `hg_src`.
Source: G32 v0.16, Figure 1; Hatcher, §2.1. -/
def hg2_src {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : hg2_Edge G r → hg2_Vert g
  | Sum.inl (_, x) => Sum.inl x
  | Sum.inr (Sum.inl (_, x)) => Sum.inl x
  | Sum.inr (Sum.inr (i, x)) => Sum.inr (Sum.inr ⟨i, (x : G ⧸ Subgroup.zpowers (g i))⟩)

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) (x : G) :
    hg2_src g (Sum.inl (i, x)) = Sum.inl x := rfl

/-- The terminal vertex of an edge; as `hg_tgt`.
Source: G32 v0.16, Figure 1; Hatcher, §2.1. -/
def hg2_tgt {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : hg2_Edge G r → hg2_Vert g
  | Sum.inl (i, x) => Sum.inr (Sum.inr ⟨i, (x : G ⧸ Subgroup.zpowers (g i))⟩)
  | Sum.inr (Sum.inl (i, x)) => Sum.inr (Sum.inl (x * (hg2_Q g i)⁻¹))
  | Sum.inr (Sum.inr (i, x)) => Sum.inr (Sum.inl (x * (hg2_Q g i)⁻¹))

example {G : Type*} [Group G] (g : Fin 1 → G) (x : G) :
    hg2_tgt g (Sum.inr (Sum.inl (0, x))) = Sum.inr (Sum.inl x) := by
  simp [hg2_tgt, hg2_Q]

/-- Face `0` of a triangle, the edge `[v₁, v₂]`; as `hg_face0`.
Source: G32 v0.16, Figure 1; Hatcher, §2.1. -/
def hg2_face0 {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : hg2_Tri G r → hg2_Edge G r
  | Sum.inl (i, x) => Sum.inr (Sum.inr (i, x))
  | Sum.inr (i, x) => Sum.inr (Sum.inr (i, x * (g i)⁻¹))

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r) :
    hg2_face0 g (Sum.inr (i, g i)) = Sum.inr (Sum.inr (i, 1)) := by
  simp [hg2_face0]

/-- Face `1` of a triangle, the edge `[v₀, v₂]`, the index taken mod `r`; as `hg_face1`.
Source: G32 v0.16, Figure 1; Hatcher, §2.1. -/
def hg2_face1 {G : Type*} {r : ℕ} : hg2_Tri G r → hg2_Edge G r
  | Sum.inl (i, x) => Sum.inr (Sum.inl (i, x))
  | Sum.inr (i, x) => Sum.inr (Sum.inl (finRotate r i, x))

example {G : Type*} (x : G) :
    hg2_face1 (Sum.inr ((1 : Fin 2), x)) = Sum.inr (Sum.inl (0, x)) := rfl

/-- Face `2` of a triangle, the edge `[v₀, v₁]`; as `hg_face2`.
Source: G32 v0.16, Figure 1; Hatcher, §2.1. -/
def hg2_face2 {G : Type*} {r : ℕ} : hg2_Tri G r → hg2_Edge G r
  | Sum.inl (i, x) => Sum.inl (i, x)
  | Sum.inr (i, x) => Sum.inl (i, x)

example {G : Type*} {r : ℕ} (i : Fin r) (x : G) :
    hg2_face2 (Sum.inr (i, x)) = hg2_face2 (G := G) (Sum.inl (i, x)) := rfl

/-- The deck action on vertices, by left multiplication on labels and cosets; as `hg_actVert`.
Source: Hatcher, §1.3 (deck transformations of a normal covering). -/
def hg2_actVert {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h : G) :
    hg2_Vert g → hg2_Vert g
  | Sum.inl x => Sum.inl (h * x)
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (h * x))
  | Sum.inr (Sum.inr ⟨i, c⟩) => Sum.inr (Sum.inr ⟨i, h • c⟩)

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (x : G) :
    hg2_actVert g 1 (Sum.inl x) = Sum.inl x := by
  simp [hg2_actVert]

/-- The deck action on edges, by left multiplication on labels; as `hg_actEdge`.
Source: Hatcher, §1.3. -/
def hg2_actEdge {G : Type*} [Group G] {r : ℕ} (h : G) : hg2_Edge G r → hg2_Edge G r
  | Sum.inl (i, x) => Sum.inl (i, h * x)
  | Sum.inr (Sum.inl (i, x)) => Sum.inr (Sum.inl (i, h * x))
  | Sum.inr (Sum.inr (i, x)) => Sum.inr (Sum.inr (i, h * x))

example {G : Type*} [Group G] {r : ℕ} (i : Fin r) (h x : G) :
    hg2_actEdge h (Sum.inl (i, x)) = Sum.inl (i, h * x) := rfl

/-- The deck action on triangles, by left multiplication on labels.
Source: Hatcher, §1.3. -/
def hg2_actTri {G : Type*} [Group G] {r : ℕ} (h : G) : hg2_Tri G r → hg2_Tri G r
  | Sum.inl (i, x) => Sum.inl (i, h * x)
  | Sum.inr (i, x) => Sum.inr (i, h * x)

example {G : Type*} [Group G] {r : ℕ} (i : Fin r) (h x : G) :
    hg2_actTri h (Sum.inr (i, x)) = Sum.inr (i, h * x) := rfl

/-! ## The deck action commutes with the incidences -/

/-- The terminal vertex map is equivariant. -/
theorem hg2_tgt_act {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h : G)
    (ε : hg2_Edge G r) : hg2_tgt g (hg2_actEdge h ε) = hg2_actVert g h (hg2_tgt g ε) := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hg2_tgt, hg2_actEdge, hg2_actVert, mul_assoc, MulAction.Quotient.smul_mk]

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (ε : hg2_Edge G r) :
    hg2_tgt g (hg2_actEdge 1 ε) = hg2_actVert g 1 (hg2_tgt g ε) := hg2_tgt_act g 1 ε

/-- The initial vertex map is equivariant. -/
theorem hg2_src_act {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h : G)
    (ε : hg2_Edge G r) : hg2_src g (hg2_actEdge h ε) = hg2_actVert g h (hg2_src g ε) := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hg2_src, hg2_actEdge, hg2_actVert, MulAction.Quotient.smul_mk]

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (ε : hg2_Edge G r) :
    hg2_src g (hg2_actEdge 1 ε) = hg2_actVert g 1 (hg2_src g ε) := hg2_src_act g 1 ε

/-- The face maps are equivariant. -/
theorem hg2_face_act {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h : G)
    (τ : hg2_Tri G r) :
    hg2_face0 g (hg2_actTri h τ) = hg2_actEdge h (hg2_face0 g τ) ∧
      hg2_face1 (hg2_actTri h τ) = hg2_actEdge h (hg2_face1 τ) ∧
      hg2_face2 (hg2_actTri h τ) = hg2_actEdge h (hg2_face2 τ) := by
  rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hg2_face0, hg2_face1, hg2_face2, hg2_actTri, hg2_actEdge, mul_assoc]

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (τ : hg2_Tri G r) :
    hg2_face2 (hg2_actTri 1 τ) = hg2_actEdge 1 (hg2_face2 τ) := (hg2_face_act g 1 τ).2.2

/-! ## Cellular cochains (as in stage H3a) -/

/-- The cellular coboundary `δ⁰ : C⁰ → C¹`, `(δ⁰φ)(ε) = φ(tgt ε) − φ(src ε)`; as `hg_delta0`.
Source: Hatcher, §2.1 and §3.1. -/
def hg2_delta0 (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (hg2_Vert g → M) →ₗ[R] (hg2_Edge G r → M) :=
  LinearMap.funLeft R M (hg2_tgt g) - LinearMap.funLeft R M (hg2_src g)

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    hg2_delta0 R R g (fun _ => 1) = 0 := by
  ext ε
  simp [hg2_delta0, LinearMap.funLeft]

/-- The cellular coboundary `δ¹ : C¹ → C²`, `(δ¹c)(τ) = c(face₀ τ) − c(face₁ τ) + c(face₂ τ)`;
as `hg_delta1`.
Source: Hatcher, §2.1 and §3.1. -/
def hg2_delta1 (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (hg2_Edge G r → M) →ₗ[R] (hg2_Tri G r → M) :=
  LinearMap.funLeft R M (hg2_face0 g) - LinearMap.funLeft R M hg2_face1 +
    LinearMap.funLeft R M hg2_face2

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (c : hg2_Edge G r → R) (i : Fin r) (x : G) :
    hg2_delta1 R R g c (Sum.inl (i, x)) =
      c (Sum.inr (Sum.inr (i, x))) - c (Sum.inr (Sum.inl (i, x))) + c (Sum.inl (i, x)) := rfl

/-- Cellular `H¹` with coefficients in a field `K`, `ker δ¹ / (ker δ¹ ∩ range δ⁰)`; as `hg_H1`.
Source: Hatcher, §3.1. -/
abbrev hg2_coH1 (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : Type _ :=
  LinearMap.ker (hg2_delta1 K K g) ⧸
    (LinearMap.range (hg2_delta0 K K g)).comap (LinearMap.ker (hg2_delta1 K K g)).subtype

example (K : Type*) [Field K] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    Module K (hg2_coH1 K g) := inferInstance

/-! ## Cellular chains and homology -/

/-- The cellular boundary `∂₁ : C₁ → C₀` with coefficients in a commutative ring `R`,
`∂₁ ε = tgt ε − src ε`, on finitely supported chains.
Source: Hatcher, §2.1 (simplicial chains of a Δ-complex). -/
def hg2_bd1 (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (hg2_Edge G r →₀ R) →ₗ[R] (hg2_Vert g →₀ R) :=
  Finsupp.lmapDomain R R (hg2_tgt g) - Finsupp.lmapDomain R R (hg2_src g)

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r)
    (x : G) :
    hg2_bd1 R g (Finsupp.single (Sum.inl (i, x)) 1) =
      Finsupp.single (hg2_tgt g (Sum.inl (i, x))) 1 - Finsupp.single (Sum.inl x) 1 := by
  simp [hg2_bd1, hg2_src]

/-- The cellular boundary `∂₂ : C₂ → C₁`, `∂₂ τ = face₀ τ − face₁ τ + face₂ τ`.
Source: Hatcher, §2.1 (`∂[v₀, v₁, v₂] = [v₁, v₂] − [v₀, v₂] + [v₀, v₁]`). -/
def hg2_bd2 (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (hg2_Tri G r →₀ R) →ₗ[R] (hg2_Edge G r →₀ R) :=
  Finsupp.lmapDomain R R (hg2_face0 g) - Finsupp.lmapDomain R R hg2_face1 +
    Finsupp.lmapDomain R R hg2_face2

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (i : Fin r)
    (x : G) :
    hg2_bd2 R g (Finsupp.single (Sum.inl (i, x)) 1) =
      Finsupp.single (Sum.inr (Sum.inr (i, x))) 1 - Finsupp.single (Sum.inr (Sum.inl (i, x))) 1 +
        Finsupp.single (Sum.inl (i, x)) 1 := by
  simp [hg2_bd2, hg2_face0, hg2_face1, hg2_face2]

/-- Cellular `H₁` of the lifted complex with coefficients in `R`:
`ker ∂₁ / (ker ∂₁ ∩ range ∂₂)`.
Source: Hatcher, §2.1 (simplicial homology). -/
abbrev hg2_H1 (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    Type _ :=
  LinearMap.ker (hg2_bd1 R g) ⧸
    (LinearMap.range (hg2_bd2 R g)).comap (LinearMap.ker (hg2_bd1 R g)).subtype

example {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) : Module ℤ (hg2_H1 ℤ g) := inferInstance

/-- The orientation chain `Σ_i Σ_x (A_i(x) − B_i(x))`, the cellular model of the fundamental
class (H3a's `hg_fundEval` is evaluation on it).
Source: Hatcher, §3.3 (fundamental class of a compact orientable surface without boundary);
G32 v0.16, Figure 1. -/
def hg2_orient {G : Type*} [Fintype G] {r : ℕ} : hg2_Tri G r →₀ ℤ :=
  ∑ i : Fin r, ∑ x : G, (Finsupp.single (Sum.inl (i, x)) 1 - Finsupp.single (Sum.inr (i, x)) 1)

example {G : Type*} [Fintype G] : hg2_orient (G := G) (r := 0) = 0 := by
  simp [hg2_orient]

/-! ## The deck action on chains and on `H₁` -/

/-- The deck action on `1`-chains, `h_*`.
Source: Hatcher, §2.1 (functoriality of simplicial chains), §1.3. -/
def hg2_chainAct1 (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (h : G) :
    (hg2_Edge G r →₀ R) →ₗ[R] (hg2_Edge G r →₀ R) :=
  Finsupp.lmapDomain R R (hg2_actEdge h)

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (i : Fin r) (h x : G) :
    hg2_chainAct1 R h (Finsupp.single (Sum.inl (i, x)) (1 : R)) =
      Finsupp.single (Sum.inl (i, h * x)) 1 := by
  simp [hg2_chainAct1, hg2_actEdge]

/-- `∂₁` commutes with the deck action. -/
theorem hg2_bd1_act (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (h : G) (z : hg2_Edge G r →₀ R) :
    hg2_bd1 R g (hg2_chainAct1 R h z) =
      Finsupp.lmapDomain R R (hg2_actVert g h) (hg2_bd1 R g z) := by
  have h1 : hg2_tgt g ∘ hg2_actEdge h = hg2_actVert g h ∘ hg2_tgt g := funext (hg2_tgt_act g h)
  have h2 : hg2_src g ∘ hg2_actEdge h = hg2_actVert g h ∘ hg2_src g := funext (hg2_src_act g h)
  simp only [hg2_bd1, hg2_chainAct1, LinearMap.sub_apply, map_sub, Finsupp.lmapDomain_apply,
    ← Finsupp.mapDomain_comp, h1, h2]

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (z : hg2_Edge G r →₀ R) :
    hg2_bd1 R g (hg2_chainAct1 R 1 z) =
      Finsupp.lmapDomain R R (hg2_actVert g 1) (hg2_bd1 R g z) := hg2_bd1_act R g 1 z

/-- `∂₂` commutes with the deck action. -/
theorem hg2_bd2_act (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (h : G) (w : hg2_Tri G r →₀ R) :
    hg2_bd2 R g (Finsupp.lmapDomain R R (hg2_actTri h) w) =
      hg2_chainAct1 R h (hg2_bd2 R g w) := by
  have h0 : hg2_face0 g ∘ hg2_actTri h = hg2_actEdge h ∘ hg2_face0 g :=
    funext fun τ => (hg2_face_act g h τ).1
  have h1 : hg2_face1 ∘ hg2_actTri h = hg2_actEdge h ∘ hg2_face1 (G := G) (r := r) :=
    funext fun τ => (hg2_face_act g h τ).2.1
  have h2 : hg2_face2 ∘ hg2_actTri h = hg2_actEdge h ∘ hg2_face2 (G := G) (r := r) :=
    funext fun τ => (hg2_face_act g h τ).2.2
  simp only [hg2_bd2, hg2_chainAct1, LinearMap.add_apply, LinearMap.sub_apply, map_add,
    map_sub, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp, h0, h1, h2]

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (w : hg2_Tri G r →₀ R) :
    hg2_bd2 R g (Finsupp.lmapDomain R R (hg2_actTri 1) w) =
      hg2_chainAct1 R 1 (hg2_bd2 R g w) := hg2_bd2_act R g 1 w

/-- The deck action `h_*` on cellular `H₁`, induced by the action on `1`-chains.
Source: Hatcher, §2.1 (a chain map induces a map on homology), §1.3. -/
def hg2_H1act (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G)
    (h : G) : hg2_H1 R g →ₗ[R] hg2_H1 R g :=
  Submodule.mapQ _ _
    ((hg2_chainAct1 R h).restrict (p := LinearMap.ker (hg2_bd1 R g))
      (q := LinearMap.ker (hg2_bd1 R g)) fun z hz => by
        rw [LinearMap.mem_ker] at hz ⊢
        rw [hg2_bd1_act, hz, map_zero])
    (by
      intro z hz
      simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range] at hz ⊢
      obtain ⟨w, hw⟩ := hz
      refine ⟨Finsupp.lmapDomain R R (hg2_actTri h) w, ?_⟩
      rw [hg2_bd2_act, hw]
      rfl)

example (R : Type*) [CommRing R] {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (h : G)
    (z : LinearMap.ker (hg2_bd1 R g)) :
    (hg2_H1act R g h (Submodule.Quotient.mk z) : hg2_H1 R g) =
      Submodule.Quotient.mk ⟨hg2_chainAct1 R h z.1, by
        rw [LinearMap.mem_ker, hg2_bd1_act, LinearMap.mem_ker.mp z.2, map_zero]⟩ := rfl

/-- The evaluation pairing `⟨c, z⟩ = Σ_ε z(ε) c(ε)` of a `1`-cochain with values in a field `K`
and an integral `1`-chain.
Source: Hatcher, §3.1 (the universal coefficient theorem, the evaluation map). -/
def hg2_pair (K : Type*) [Field K] {G : Type*} {r : ℕ} (c : hg2_Edge G r → K)
    (z : hg2_Edge G r →₀ ℤ) : K :=
  z.sum fun ε n => (n : K) * c ε

example (K : Type*) [Field K] {G : Type*} {r : ℕ} (c : hg2_Edge G r → K) :
    hg2_pair K c 0 = 0 := by
  simp [hg2_pair]

/-! ## The B6-3b projector on the G32 complex -/

/-- The B6-3b primitive projector `Σ_h b4b_projectorCoeff h · h_*` (`b4_groupEnd` with the
coefficients `6 Re ρ(h⁻¹)₀₀`) on cellular `H₁(X̃(b4b_root); ℤ)`.
Source: G32 v0.16, Definition 3.2; `b4b_projectorCoeff`, `b4_groupEnd`. -/
def hg2_projector : hg2_H1 ℤ b4b_root →ₗ[ℤ] hg2_H1 ℤ b4b_root :=
  ∑ h : b4b_Group, b4b_projectorCoeff h • hg2_H1act ℤ b4b_root h

example (z : hg2_H1 ℤ b4b_root) :
    hg2_projector z = ∑ h : b4b_Group, b4b_projectorCoeff h • hg2_H1act ℤ b4b_root h z := by
  simp [hg2_projector]

end HodgeLean.Foundations.Program
