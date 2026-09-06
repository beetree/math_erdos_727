import Erdos727.Main
import Erdos727.Analytic.MertensAP

/-!
# Unconditional endpoints

These discharge the analytic hypothesis with `mertensAP_210`; they are unconditional exactly
when that obligation is proved (see `Erdos727/Analytic/MertensAP.lean`).
-/

namespace Erdos727

/-- **Erdős Problem 727, `k = 3`**: infinitely many `n` satisfy `((n+3)!)² ∣ (2n)!`. -/
theorem erdos727_k3 : formalConjecturesStatement_k3 := k3_of_mertensAP mertensAP_210

/-- **Erdős Problem 727, `k = 2`**: infinitely many `n` satisfy `((n+2)!)² ∣ (2n)!`. -/
theorem erdos727_k2 : formalConjecturesStatement_k2 := k2_of_mertensAP mertensAP_210

end Erdos727
