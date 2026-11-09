```
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
```
# `KleeneAlgebra.Reductions`

| File | Contents |
|---|---|
| `SelfHalt_to_TermEq.lean` | **No Turing machine decides equality** on `T Σ̈` and `K Σ̈`, over `{0, 1}` and `ℕ` |
| `Halt_to_TermEq.lean` | The race, and `HALT ⪯ₘ` equality over `ℕ` |
| `Halt_to_TermEqBool.lean` | `HALT ⪯ₘ` equality over `{0, 1}`, and the failure of equality on `L Σ̈` |
| `SelfOut_to_ModelLe.lean` | `kaRed`, `haltRed`, and `HALT ⪯ₘ` the failure of language inclusion |
| `SelfOut_to_Eq.lean` | The paper's Theorem 18, as separation statements |
| `Sigma1.lean` | The same argument on a machine's own code. Conditional, and not used by the results above |

Supporting files:

| File | Contents |
|---|---|
| `Instance.lean` | `rInst`, the instance of a machine on empty input |
| `InstanceCode.lean` | `instCode`: computing that instance, primitive recursively |
| `ExprCode.lean` | `rc`: expressions as natural numbers |
| `ProofSearch.lean` | `Checks`: provable equality as a search over a primitive recursive test |
| `BinarySubst.lean` | Substituting the code `1ⁿ0` for letters, on terms, languages and codes |

The statements in `SelfOut_to_ModelLe.lean` and `SelfOut_to_Eq.lean` about machine codes depend on
`encodeBoolTM`, which is not faithful. See `../GAPS.md`, item 0.
