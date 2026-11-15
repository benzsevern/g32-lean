import HodgeLean.Papers.G34Family

/-! # G34 Theorem A, stage 3: the supply premise

The direct Proposition 4.6 premise for stage 3 of the G34 route at `(n, δ) = (4, [1])`: algebraicity
of the Weil classes on every fibre of a `g34h_PrymFamily`. It is the output of G34 Proposition 4.6
and Corollary 4.7, recorded as one named premise because the repository has no carriers for the
Jacobian factors, products, Künneth, correspondences or pushforward used by their proofs (see
`docs/specs/G34Supply.md`). HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Papers

/-- Proposition 4.6 and Corollary 4.7's cycle-supplier output for every fibre: the Weil classes of
each Prym–Tyurin factor `A_σ(C_s)` are algebraic.
Source: G34 v1.5, Proposition 4.6 (`prop:supply`) and Corollary 4.7 (`cor:everymember`), with
condition (L) from Theorem 5.1 (`thm:brauer`, Brauer's induction theorem, Serre, *Linear
representations of finite groups*, §10.5, Theorem 20); Schoen, *Hodge classes on self-products of a
variety with an automorphism*, Compositio Math. 65 (1988), Theorem 2.0 and Corollary 3.1, with
G34 Lemma 4.4 (`lem:schoenR`) for exponents `m/2`; Milne, *Lefschetz classes on abelian varieties*,
Duke Math. J. 96 (1999), Theorem 3.2. -/
def g34s_Prop46 (P : g34h_PrymFamily) : Prop :=
  ∀ s, wtr_WeilAlg (P.fiber s)

example {P : g34h_PrymFamily} (h46 : g34s_Prop46 P) (s : P.S) : wtr_WeilAlg (P.fiber s) :=
  h46 s

end HodgeLean.Papers
