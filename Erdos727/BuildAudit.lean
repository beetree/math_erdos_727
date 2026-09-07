import Erdos727.AxiomCheck
import Erdos727.Final

/-!
# Build-time axiom audit

Enforces that the endpoints depend solely on the standard foundations `propext`,
`Classical.choice`, `Quot.sound`.  Any other transitive dependency (in particular `sorryAx`)
makes `lake build` fail with an elaboration error.  The `#print axioms` lines record the verified
dependency lists in the build log.
-/

assert_standard_axioms Erdos727.mertensAP_210
assert_standard_axioms Erdos727.k3_of_mertensAP
assert_standard_axioms Erdos727.k2_of_mertensAP
assert_standard_axioms Erdos727.erdos727_k3
assert_standard_axioms Erdos727.erdos727_k2

#print axioms Erdos727.erdos727_k3
#print axioms Erdos727.erdos727_k2
