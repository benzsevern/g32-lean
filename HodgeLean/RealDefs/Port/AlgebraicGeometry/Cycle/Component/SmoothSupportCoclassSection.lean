/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
import HodgeLean.RealDefs.Port.AlgebraicTopology.Support.RelativeCohomologyOpenTransport

/-! Ported, with modifications (imports rewritten to this repository's modules, the `module`
header dropped, public/expose section markers removed; the upstream licence and notice are in
`HodgeLean/RealDefs/Port/LICENSE` and `NOTICE`), from upstream's `Other/AlgebraicGeometry/Cycle/Component/SmoothSupportCoclassSection.lean`
at `2ead713`. -/

/-!
# The normalized component coclass on the original ambient smooth-support open

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

section Component

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Restriction to each image neighborhood agrees with transport of the
constructed auxiliary normalized section. No ambient section comparison is supplied. -/
theorem cycleComponentSmoothSupportCoclassSection_restrict
    (V : Opens (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
    (hV : (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj V ≤
      cycleComponentSmoothSupportAmbientOpen X x) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * p)).obj.map (homOfLE hV).op
        (cycleComponentSmoothSupportCoclassSection X x hx) =
    (supportRelativeCohomologySheafOpenIso (cycleComponentSmoothClosedLiftAmbientMap X x)
      (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
      (cycleComponentSupport X x)
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
      (cycleComponentSmoothClosedLiftAmbientMap_support X x) (2 * p)).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
        (2 * p)).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (cycleComponentSmoothClosedLiftCoclassSection X x hx)) :=
  supportRelativeCohomologySectionOnOpen_restrict
    (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x)
    (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
    (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (cycleComponentSmoothClosedLiftCoclassSection X x hx) V hV

end Component

end AlgebraicGeometry.ComplexPoint
