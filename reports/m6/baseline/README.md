# M6 completion: baseline (implementation at b29ab03)

Reproduced on the reviewed baseline before any change of the implementation tree (only tests,
fixtures and scripts added). Runs bound to the implementation tree hash recorded in each file.

| Run | Result |
|---|---|
| `scripts/test-all` (`test_all.json`) | 18/18 suites PASS |
| `scripts/m6-finishtime-gate` (`finishtime_gate.json`) | FAIL (expected): the four historical roots TRANSLATED_AND_CHECKED, `completes_at_finish_time` BLOCKED_DEPENDENCY |
| `scripts/test-m6-prosa` (`m6_prosa_results.json`) | behavior61 (closure 426), finishtime4 (123), holdout13_prosa (411), holdout14_mathcomp (132) VERIFIED; the original holdout20_prosa request 13/20 roots translated, reported AUDIT_REJECTED (never VERIFIED while roots are blocked) |
| `tests/m6/blocker_graph.py` (`completes_blocker_graph.json`) | closure 1716, 792 accepted; 34 leaves (30 missing feature, 1 exporter/metadata defect, 3 universe solving); 890 pending only through dependencies |

Fixed request manifests (not reports): `fixtures/m6/regression/*.json`.
