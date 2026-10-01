import PaperIV.HybridDichotomy

/-!
# Clean aggregate of the hybrid Erdős #81 route

This is the only aggregate of the hybrid route.  It imports exactly the module
that declares the three public results

* `PaperIV.HybridDichotomy.chordal_far_or_nearStructure`,
* `PaperIV.HybridDichotomy.chordal_near_extremal_stability`,
* `PaperIV.HybridDichotomy.erdos81_of_structuralDichotomy`,

and therefore exactly their true dependency cone.  In particular it does *not*
import `PaperIV.lean`, the numerical near route
(`PaperIV.NearH1GlobalAssembly`, `PaperIV.NearH1TargetAssembly`), or any module
that already asserts Erdős #81.
-/
