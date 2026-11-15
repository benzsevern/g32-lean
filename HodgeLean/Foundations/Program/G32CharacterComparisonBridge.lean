import HodgeLean.Foundations.Program.G32PropFourSixPacked0451

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32cc_label_eq (D : g32p_familiesClassData)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (g : g32p_G) :
    D.label g = g32p_integrationLabel g := by
  apply g32p_literalRepresentative_classes_injective
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr
    ((hconj g).symm.trans (g32p_integrationLabel_conj g))

end HodgeLean.Foundations.Program
