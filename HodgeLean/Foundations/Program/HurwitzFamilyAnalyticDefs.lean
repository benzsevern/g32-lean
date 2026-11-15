import HodgeLean.Foundations.Program.HurwitzTransport
import HodgeLean.Foundations.Program.HurwitzPrymRexFillMain

/-! # B6-2b: coordinate maps for moving branched covers

Implication from branch parameters to explicit local power maps and a transported
sphere projection. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Program

/-- The finite local model, including its ten parameter coordinates.
Source: Fulton, *Hurwitz schemes and irreducibility of moduli of algebraic curves*,
Ann. Math. 90 (1969), 542–575; Harris–Morrison, *Moduli of Curves*, §1.G. -/
def b6a_power (i : Fin 10) (e : ℕ) (q : (Fin 10 → ℂ) × ℂ) : (Fin 10 → ℂ) × ℂ :=
  (q.1, q.1 i + q.2 ^ e)

example (i : Fin 10) (e : ℕ) (t : Fin 10 → ℂ) (w : ℂ) :
    b6a_power i e (t, w) = (t, t i + w ^ e) := rfl

/-- Inverse centred coordinates at all thirteen marks; infinity uses sphere inversion.
Source: `b6_branch`, `b4cov_sphInv`; Harris–Morrison, *Moduli of Curves*, §1.G. -/
def b6a_value (t : Fin 10 → ℂ) (j : Fin 13) (w : ℂ) : OnePoint ℂ :=
  if h : j.val < 10 then ((t ⟨j.val, h⟩ + w : ℂ) : OnePoint ℂ)
  else if j.val = 10 then (w : OnePoint ℂ)
  else if j.val = 11 then ((1 + w : ℂ) : OnePoint ℂ)
  else b4cov_sphInv (w : OnePoint ℂ)

example (t : Fin 10 → ℂ) (w : ℂ) :
    b6a_value t 0 w = ((t 0 + w : ℂ) : OnePoint ℂ) := rfl

/-- The sphere projection on the product with a fixed filled central surface.
Source: `b6t_sphere`; topological marking in the local Hurwitz construction,
Fulton, Ann. Math. 90 (1969), 542–575. -/
def b6a_map (b : Fin 10 → ℂ) {C : Type} (f : C → OnePoint ℂ)
    (q : b6t_polydisc b × C) : OnePoint ℂ := b6t_sphere b q.1.val (f q.2)

example (b : Fin 10 → ℂ) {C : Type} (f : C → OnePoint ℂ)
    (t : b6t_polydisc b) (x : C) : b6a_map b f (t, x) = b6t_sphere b t.val (f x) := rfl

end HodgeLean.Foundations.Program
