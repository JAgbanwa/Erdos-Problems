import PaperIV.RootEdgeSplit
import PaperIV.PaddedEquitableColouring
import PaperIV.NearH1PromotionAccounts
import PaperIV.NearH1FinalScalars
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-!
# Root regularization for the near H1 constructor

This is the graph-theoretic adapter between the calibrated maximum clique and
the already formalized RD09 phase-I interface.  It carries the literal
output consumed by the RD09 phase-I interface; the construction that produces it
lives in `PaperIV.RootRegularizationBridge`.
-/

namespace PaperIV.NearH1RootRegularization

open PaperIV.RootVocab
open PaperIV.PaddedEquitableColouring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The literal output needed by the rooted RD09 phase-I adapter. -/
structure RegularizedRoot (G : SimpleGraph V) [DecidableRel G.Adj] where
  reference : Finset V
  root : Finset V
  isClique : G.IsClique (root : Set V)
  reference_large : 1024 ≤ reference.card
  card_ge : 1000 ≤ root.card
  root_le_outside : root.card ≤ (outsideVertices root).card
  outside_two : 2 ≤ (outsideVertices root).card
  root_lower_ratio : 99 * reference.card ≤ 100 * root.card
  root_ratio : 100 * root.card ≤ 101 * reference.card
  outside_ratio : 87947 * reference.card ≤
    44352 * (outsideVertices root).card
  slack_ratio : 48 * (2 * root.card - (outsideVertices root).card) ≤ reference.card
  maxMissing_ratio : 3 * maxMissingColumn G root ≤ reference.card
  outside_edges_small : 400 * (outsideEdges G root).card < reference.card ^ 2
  mass_envelope : 2000 * (missingIncidences G root +
    2 * (outsideEdges G root).card) ≤ 11 * reference.card ^ 2
  palette : 40 * paddedPaletteSize (outsideGraph G root) root.card ≤ 73 * root.card
  width : 40 * ((outsideGraph G root).cliqueNum - 1) ≤ 3 * root.card

end PaperIV.NearH1RootRegularization
