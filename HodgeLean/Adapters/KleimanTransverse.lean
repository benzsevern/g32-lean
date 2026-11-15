import HodgeLean.Adapters.KleimanTransverseProofs

/-!
# Translation transversality on group varieties (FROZEN SPEC)

This specification gives implications from the difference map on pairs of component closures to
a dense Zariski open set of transverse translations. It does not give intersection multiplicities or
cycle-class multiplicativity. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Adapters

/-- The fibre of the difference map is the scheme-theoretic translated intersection.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), proof of Theorem 2. -/
alias hc9k_actionFiber_iso_intersection := hc9k_actionFiber_iso_intersection_aux

example := hc9k_actionFiber_iso_intersection

/-- Smoothness of the regular difference-map fibre gives smoothness of the translated
intersection away from the two singular loci.
Source: Hartshorne, *Algebraic Geometry*, III.10.1 and III.10.8. -/
alias hc9k_smooth_fiber_gives_transverse_off_singular :=
  hc9k_smooth_fiber_gives_transverse_off_singular_aux

example := hc9k_smooth_fiber_gives_transverse_off_singular

/-- A general translated intersection has the expected component coheight.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), Theorem 2(i). -/
alias hc9k_genericFiber_expected_coheight := hc9k_genericFiber_expected_coheight_aux

example := hc9k_genericFiber_expected_coheight

/-- The product of the two regular loci has smooth fibres over a dense Zariski open set of
translation parameters.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), Theorem 2(ii); Hartshorne, *Algebraic Geometry*, III.10.7. -/
alias hc9k_regular_intersection_generically_transverse :=
  hc9k_regular_intersection_generically_transverse_aux

example := hc9k_regular_intersection_generically_transverse

/-- Intersections involving either component's singular locus have coheight strictly above the
expected component coheight on a common dense Zariski open set.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), Theorem 2(i). -/
alias hc9k_singular_intersections_smaller := hc9k_singular_intersections_smaller_aux

example := hc9k_singular_intersections_smaller

/-- Every point in the nonsmooth or singular part of a general translated intersection has
strictly larger coheight than its expected component coheight.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), Theorem 2; Hartshorne, *Algebraic Geometry*, II.3. -/
alias hc9k_badLocus_strict_coheight := hc9k_badLocus_strict_coheight_aux

example := hc9k_badLocus_strict_coheight

/-- A dense Zariski open maps into the transverse-translation locus for one component pair.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), Theorem 2. -/
alias hc9k_transverseLocus_contains_nonempty_open :=
  hc9k_transverseLocus_contains_nonempty_open_aux

example := hc9k_transverseLocus_contains_nonempty_open

/-- One dense Zariski open works for every component pair in two rational cycles.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28
(1974), Theorem 2; Fulton, *Intersection Theory*, second edition, §1.3. -/
alias hc9k_transverseLocus_finite_family := hc9k_transverseLocus_finite_family_aux

example := hc9k_transverseLocus_finite_family

end HodgeLean.Adapters
