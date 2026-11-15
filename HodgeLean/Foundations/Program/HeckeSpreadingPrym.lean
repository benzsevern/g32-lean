import HodgeLean.Foundations.Program.HeckeSpreadingPrymProofs

/-! # Hecke spreading S7 on the Prym fibres (FROZEN SPEC)

Stage S7 of `docs/specs/G32RemainingPremises.md`, §2.3, as fixed by the S7 note and the review
section of `docs/specs/HeckeSpreading.md`. Each theorem restates the matching `_aux` theorem in
`HeckeSpreadingPrymProofs.lean`.

The dominance isogenies of `g32r_dominant` run from a Prym fibre to a universal fibre, while
`g32tr_weilAlg_pullback` moves Weil algebraicity from target to source only. S7 bridges the two
with one explicit binder, the **restricted forward-transport binder**
`hfwd : ∀ p ∈ hk7_pairs P, g32t_WeilAlg (P.fiber p.2) → g32t_WeilAlg (b60b_univ p.1)`:
Lemma 2.2 of G32 in the direction from source to target, only at dominance pairs. It is a
geometric input about isogenies; it says nothing about a fibre that is not the target of a
Prym fibre, and it does not assume algebraicity of any universal fibre.

What is claimed:
* S7a, S7b: the implication from `hfwd` (with stage 3 and stage 4) to algebraicity at every
  point of `𝓗₃`, and to the exact shape of the field `spread` of `g32a_premises` for
  `F.univ = b60b_univ`, with `C = {univ}`;
* S7c: reverse isogenies at the dominance pairs give `hfwd`, through `g32tr_weilAlg_pullback`;
* S7d: morphism-level quasi-inverse witnesses (Mumford §4) for the morphisms from Prym fibres
  to universal fibres give those reverse isogenies, with no discriminant input;
* S7e: the field `reverse` of `g32n_premises` gives them only together with the stage-5 input
  `hpol`, which makes the Prym fibres members (H7);
* S7f, S7g: the field `spread` from the witness route and from the `g32n_premises` route.

What is not claimed: the existence of quasi-inverse witnesses, of reverse isogenies, or of a
period map; forward transport itself; anything about a universal family other than one with
`F.univ = b60b_univ`. No statement uses the field `spread` of any bundle. HC no distance; AV
milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-! ## Non-degeneracy of the dominance pairs -/

/-- Every period map gives a dominance pair, so the binders below range over a nonempty set of
pairs: `hfwd` is not vacuous for a Prym family with a period map. -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (P : g32h_PrymFamily)
    (R : g32r_PeriodMap F P) : (hk7_pairs P).Nonempty := by
  obtain ⟨U, -, ⟨m, hm⟩, hUs⟩ := g32r_dominant F P R
  obtain ⟨s, hs⟩ := hUs m hm
  refine ⟨(m, s), ?_⟩
  simp only [hk7_pairs, Set.mem_ofPred_eq]
  rw [← hF]
  exact hs

/-- Both ends of a dominance pair are sixfolds, not rank-zero objects. -/
example (P : g32h_PrymFamily) (p : g32m_Domain × P.S) :
    dim (P.fiber p.2).X.left = 6 ∧ dim (b60b_univ p.1).X.left = 6 :=
  ⟨(g32h_fiber_polarized P p.2).dim_eq, (b60b_member p.1).dim_eq⟩

/-! ## S7a, S7b: from the forward binder to the field `spread` -/

/-- **S7a.** The implication from forward transport at the dominance pairs, over a nonempty
open set of dominance, to Weil algebraicity of `b60b_univ` at every point of `𝓗₃`.
Source: G32 v0.16, Lemma 2.2 (direction from source to target), Proposition 4.6
(`g32s_fiber_alg`) and the proof of Theorem 7.2; S6 `hk_weilAlg_of_open`. -/
theorem hk7_algLocus_eq_univ (P : g32h_PrymFamily) (h46 : g32s_Prop46 P)
    {U : Set g32m_Domain} (hU : IsOpen U) (hne : U.Nonempty)
    (hdom : ∀ m ∈ U, ∃ s, (m, s) ∈ hk7_pairs P)
    (hfwd : ∀ p ∈ hk7_pairs P, g32t_WeilAlg (P.fiber p.2) → g32t_WeilAlg (b60b_univ p.1)) :
    hk7_algLocus = Set.univ :=
  hk7_algLocus_eq_univ_aux P h46 hU hne hdom hfwd

example (P : g32h_PrymFamily) (h46 : g32s_Prop46 P)
    (hdom : ∀ m, ∃ s, (m, s) ∈ hk7_pairs P)
    (hfwd : ∀ p ∈ hk7_pairs P, g32t_WeilAlg (P.fiber p.2) → g32t_WeilAlg (b60b_univ p.1))
    (τ : g32m_Domain) : g32t_WeilAlg (b60b_univ τ) := by
  have h := hk7_algLocus_eq_univ P h46 isOpen_univ ⟨⟨0, g32m_zero_mem⟩, trivial⟩
    (fun m _ => hdom m) hfwd
  have hτ : τ ∈ hk7_algLocus := h ▸ Set.mem_univ τ
  simpa only [hk7_algLocus, Set.mem_ofPred_eq] using hτ

/-- **S7b.** For the concrete universal family, the period map, stage 3 and the forward binder
give the exact shape of the field `spread` of `g32a_premises`, with `C = {univ}`.
Source: G32 v0.16, Lemma 2.2, Corollary 5.11, Proposition 4.6 and the proof of Theorem 7.2;
`g32r_dominant`; S7a. -/
theorem hk7_spread (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (P : g32h_PrymFamily) (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hfwd : ∀ p ∈ hk7_pairs P, g32t_WeilAlg (P.fiber p.2) → g32t_WeilAlg (b60b_univ p.1)) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C :=
  hk7_spread_aux F hF P h46 R hfwd

/-- Chain check: the field `transport` of a `g32a_premises` bundle supplies the forward binder
(its first direction, at the dominance pairs), and S7b then gives the field `spread` without
reading `B.spread`. -/
example (B : g32a_premises) (hF : B.F.univ = b60b_univ) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧
      {m | g32t_WeilAlg (B.F.univ m)} = ⋃₀ C :=
  hk7_spread B.F hF B.P B.h46 B.R fun p hp h => by
    have hp' : g32t_KIsog (B.P.fiber p.2) (B.F.univ p.1) := by rw [hF]; exact hp
    have := (B.transport _ _ hp').1 h
    rwa [hF] at this

/-- Chain check: from every field of `g32a_premises` except `spread`, S7b builds the whole
bundle. -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (P : g32h_PrymFamily)
    (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    g32a_premises :=
  { F, P, h46, R, hpol, transport
    spread := hk7_spread F hF P h46 R fun p hp h => by
      have hp' : g32t_KIsog (P.fiber p.2) (F.univ p.1) := by rw [hF]; exact hp
      have := (transport _ _ hp').1 h
      rwa [hF] at this }

/-! ## S7c, S7d, S7e: sources of the forward binder -/

/-- **S7c.** Reverse isogenies at the dominance pairs give the forward binder: algebraicity of
the Prym fibre pulls back along `b60b_univ m → P.fiber s`.
Source: G32 v0.16, Lemma 2.2 (pullback direction), through `g32tr_weilAlg_pullback`, with
`b60b_member` and `g32h_fiber_polarized` (G32 Lemma 3.6) for its two Weil-type hypotheses. -/
theorem hk7_forward_of_reverse (P : g32h_PrymFamily)
    (hrev : ∀ p ∈ hk7_pairs P, g32t_KIsog (b60b_univ p.1) (P.fiber p.2)) :
    ∀ p ∈ hk7_pairs P, g32t_WeilAlg (P.fiber p.2) → g32t_WeilAlg (b60b_univ p.1) :=
  hk7_forward_of_reverse_aux P hrev

/-- The reverse binder is satisfiable on the universal side: the Hecke isogeny of the identity
(S5) runs in both directions between `b60b_univ τ` and itself. -/
example (τ : g32m_Domain) : g32t_KIsog (b60b_univ τ) (b60b_univ τ) :=
  hk_hecke_isog (g := 1) (by simp [hk_group, hk_unitary])
    (by simp [hk_moves, hk_ratCast, hk_toC, Matrix.toLin_one])

/-- **S7d.** Morphism-level quasi-inverse witnesses for the morphisms from Prym fibres to
universal fibres give reverse `K`-linear polarized isogenies at every dominance pair. No
discriminant of the Prym fibre is used.
Source: Mumford, *Abelian Varieties*, §4 (quasi-inverse of an isogeny), through
`qinv_KIsog_reverse_of_witness`. -/
theorem hk7_reverse_of_witness (P : g32h_PrymFamily)
    (hw : ∀ (m : g32m_Domain) (s : P.S) (f : (P.fiber s).X ⟶ (b60b_univ m).X),
      IsMonHom f → ccm2_IsogenyOnPoints f →
        Nonempty (qinv_Witness (P.fiber s) (b60b_univ m) f)) :
    ∀ p ∈ hk7_pairs P, g32t_KIsog (b60b_univ p.1) (P.fiber p.2) :=
  hk7_reverse_of_witness_aux P hw

/-- The witness binder is the classical premise `qinv_premise` restricted to morphisms from
Prym fibres to universal fibres. -/
example (h : qinv_premise) (P : g32h_PrymFamily) :
    ∀ p ∈ hk7_pairs P, g32t_KIsog (b60b_univ p.1) (P.fiber p.2) :=
  hk7_reverse_of_witness P fun _ _ f hf hi => h _ _ f hf hi

/-- **S7e.** The field `reverse` of `g32n_premises` gives reverse isogenies at the dominance
pairs once the Prym fibres are members, which the stage-5 input `hpol` supplies (discriminant
`[-2]`, H7). `hpol` alone gives no reverse isogeny; `hrev` alone does not apply to a Prym fibre.
Source: G32 v0.16, Proposition 6.3 (`g32a_fiber_disc`) and Lemma 3.6 (`g32h_fiber_polarized`);
`g32t_isMember_iff`; `b60b_member`. -/
theorem hk7_reverse_of_members (P : g32h_PrymFamily)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (hrev : ∀ A B, g32t_IsMember A → g32t_IsMember B → g32t_KIsog A B → g32t_KIsog B A) :
    ∀ p ∈ hk7_pairs P, g32t_KIsog (b60b_univ p.1) (P.fiber p.2) :=
  hk7_reverse_of_members_aux P hpol hrev

example (B : g32n_premises) :
    ∀ p ∈ hk7_pairs B.P, g32t_KIsog (b60b_univ p.1) (B.P.fiber p.2) :=
  hk7_reverse_of_members B.P B.hpol B.reverse

/-! ## S7f, S7g: the field `spread` along the two reverse routes -/

/-- **S7f.** The field `spread` for the concrete universal family from quasi-inverse witnesses,
with no discriminant input and no transport field.
Source: S7b, S7c, S7d; Mumford, *Abelian Varieties*, §4; G32 v0.16, Lemma 2.2 (pullback
direction) and the proof of Theorem 7.2. -/
theorem hk7_spread_of_witness (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (P : g32h_PrymFamily) (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hw : ∀ (m : g32m_Domain) (s : P.S) (f : (P.fiber s).X ⟶ (b60b_univ m).X),
      IsMonHom f → ccm2_IsogenyOnPoints f →
        Nonempty (qinv_Witness (P.fiber s) (b60b_univ m) f)) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C :=
  hk7_spread_of_witness_aux F hF P h46 R hw

/-- Chain check: the field `qinv` of a `qinv_premises` bundle gives its field `spread` for the
concrete family, without reading `B.spread`. -/
example (B : qinv_premises) (hF : B.F.univ = b60b_univ) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧
      {m | g32t_WeilAlg (B.F.univ m)} = ⋃₀ C :=
  hk7_spread_of_witness B.F hF B.P B.h46 B.R fun _ _ f hf hi => B.qinv _ _ f hf hi

/-- **S7g.** The field `spread` for the concrete universal family from the other fields of
`g32n_premises`: the reverse field with the stage-5 input.
Source: S7b, S7c, S7e; G32 v0.16, Lemma 2.2 (pullback direction), Proposition 6.3 and the
proof of Theorem 7.2. -/
theorem hk7_spread_of_members (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (P : g32h_PrymFamily) (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (hrev : ∀ A B, g32t_IsMember A → g32t_IsMember B → g32t_KIsog A B → g32t_KIsog B A) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C :=
  hk7_spread_of_members_aux F hF P h46 R hpol hrev

/-- Chain check: from every field of `g32n_premises` except `spread`, S7g builds the whole
bundle. -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (P : g32h_PrymFamily)
    (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (reverse : ∀ A B, g32t_IsMember A → g32t_IsMember B → g32t_KIsog A B → g32t_KIsog B A) :
    g32n_premises :=
  { F, P, h46, R, hpol, reverse
    spread := hk7_spread_of_members F hF P h46 R hpol reverse }

end HodgeLean.Foundations.Program
