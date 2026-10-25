# Verified NSE Fefferman A–D source anchor

Both Linux and Windows passed [Actions run 40174041653](https://github.com/randogelist/stokes-conditional/actions/runs/40174041653).

Verified source commit: `26bc074c2b8ebf57fa0fabcf9b8263673de9d80b`  
Verified source tree: `28e66960e32b1253927c982e217ffbb6bca399df`

GitHub tested the pull-request merge commit `2ba3f5bc4a7b74b75db1f58d0ff9552045002f44`; its tree is exactly the same as the verified source tree.

Each platform compiled **59 modules**, audited **3,245 declarations**, and checked **1,476 theorem declarations**, including generated lemmas. The audit covers all 649 explicit source theorem/lemma declarations. It permits only `propext`, `Classical.choice`, and `Quot.sound`.

- [Run identity and artifact digests](40174041653/run.json)
- [Original Linux receipt](40174041653/linux/anchor-receipt.json)
- [Original Windows receipt](40174041653/windows/anchor-receipt.json)
- [Source consolidation PR](https://github.com/randogelist/stokes-conditional/pull/1)

The receipt bytes, source/settings/provenance hashes, log hashes, and downloaded artifact digests were independently checked. The receipts are retained in git because Actions artifacts have limited retention. This evidence branch adds only evidence files to the verified source commit; it does not claim that its later evidence commit was the one compiled by that run.

These are compiled conditional results and internal endpoint equivalences. Physical Fefferman A, B, C, and D remain **OPEN**; the boundary-time derivative alignment and cross-branch physical realization remain unresolved. Source-inspection reports under `provenance/` predate this fresh CI verification.
