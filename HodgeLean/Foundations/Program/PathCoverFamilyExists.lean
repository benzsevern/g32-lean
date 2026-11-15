import HodgeLean.Foundations.Program.PathCoverFamilyExistsProofs

/-! # B6-5: the retained cover family at an admissible centre

Implication from an admissible centre and a tuple in the G32 Nielsen class to a retained analytic
Galois family over the polydisc about it (the `rf8_SharedFamily` construction at an arbitrary
centre).

Not claimed: a specified based monodromy on named loops. The punctured cover of the family is
pinned only through the presentation loops of `b4_punctured_presentation`, which are
existential; the identification at the G32 centre is set aside in
`docs/specs/PathCoverFamily.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- **The retained cover family at an admissible centre.** For every configuration `c` in the
normalized chart and every tuple `g` in the G32 Nielsen class of the class datum, there is a
retained family over `b6t_polydisc c`: one surface with the G32 action, the punctured Galois cover
at `c`, its filling, the analytic atlas over the polydisc and the fibre structures, with ordered
branch points `b6_branch t` and rotation generators `g j`, and the integral data `Q₀, Q, P, A`.
This generalizes the construction of `rf8_shared_root` from `(mr_base, b4b_root)` to `(c, g)`.
Source: Riemann existence (Forster, *Lectures on Riemann Surfaces*, Theorem 8.4; Völklein,
*Groups as Galois Groups*, Theorem 2.13), as in `b6_fiber_geometry`; `b6t_cover`,
`b6a_fill_transport`, `b6a_analytic_atlas` (Fulton, Ann. Math. 90 (1969), 542–575;
Harris–Morrison, *Moduli of Curves*, §1.G); `rf8_shared_root`; G32 v0.16, §3.1 and
Definition 3.5. -/
theorem b65z_family_exists (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) :
    Nonempty (b65z_SharedFamily c g) :=
  b65z_family_exists_aux c hc g hg

example := @b65z_family_exists

end HodgeLean.Foundations.Program
