# codex-sol-tools — GPT-6.1-Sol

NIGHT-VERIFY source `9d17e3356`: repair verification now requires the named
assertion at base, an identical head regression transplanted into tests/ on both
revisions, identical executed test IDs/source hashes, and a clean head without
skips/errors/expected failures. Complete observations are archived before ok;
archive unavailability preserves semantic_ok separately. Explicit prose-only
claims retain scope/forbidden/budget checks. Exact field filters exclude untagged
items. Existing test claims need harness/expected assertion fields before rerun.

Validation: `python3 -m unittest tests.test_repair_verify`: 19 passed. Self
verification against `30529279e`: exact intended assertion (`True is not false`)
fails on old missing-module red classification and passes on the new verifier.
Evidence: `planning/evidence/repair/NIGHT-VERIFY-f596713e338f4e709b90452bac5c0eca.json`,
sha256 `1b5470639501e5f97826475ffa773026f10ec26974886a948508c26a93c29ad9`.
No ACL2 books, host behavior, native images or deployments changed. Registries
and current-view require no capability edits. Integrator reviews/merges source.

Next per groundwork: fix the stale developer-selectors HANDLE harness after the
wrapper's control section conversion, coordinating Runtime's real API; then
stabilize lock finding identities under line shifts without baseline inflation.
S141 duplicate-load gate and useful historical harvest remain after these
consumer blockers. No subagents spawned. No source obstruction on NIGHT-VERIFY.
