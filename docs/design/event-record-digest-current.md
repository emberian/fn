# Actual journal reader digest continuation

Source candidate on cold `1c70451f05150456c4f8663b22522af5260a11d9`.
The shared fetch leaf is the exact root-integrated `146d3cbcf` implementation;
its qualification does not qualify this different cold dependency closure.

`fn2-event-read-format-core` formerly called the full 32-byte fetch immediately
after semantic seal verification. That format visit had already spent its
supplied budget. It now captures the decoded record-digest offset, initializes
next/accumulator, enters RECORD-DIGEST and returns MORE. The next visit dispatches
before namespace/context setup or `fn2-format-run`, calls `fn2-rec-fetch-step`
once, and permits READ-RECORDS only on OK, next=32 and accumulator=0. No member
parser or physical records read runs during this continuation.

The continuation adds only next:u8, accumulator:u32 and offset:u32 to the one
existing reader row. The request/source identity stays in that row. Normal
OPEN accepts IDLE/NEXT; issue accepts READ-SEAL/READ-RECORDS; harvest accepts
matching WAIT phases; member processing accepts MEMBERS; producer rearm accepts
COMPLETE/IDLE. Those faces cannot replace this reader during RECORD-DIGEST.
Cold JOURNAL-BIND immediately enters JOURNAL. Its format branch returns without
changing that control phase; only successful terminal member processing returns
to JOURNAL-BIND. Raw restore BEGIN has no independent phase rejection: its sole
actual boot wrapper checks the machine's EVENTS-BEGIN phase/generation. The
composed lifecycle, rather than a duplicate shadow row, supplies this exclusion.

Each resumed visit checks the decoded Ref's slot/generation/offset/length,
authenticated semantic result, retained body window and valid partial-word
state. Live FORMAT-STEP retains its actual snapshot owner/source-held checks;
cold journal-step retains candidate/map generation/current-source binding.
The pool reader rechecks the actual generation and owner on each consumed byte.
FORMAT-STEP retains owner/source refusal precedence; valid zero work yields MORE
before expected-seal lookup. Invalid budget or non-format phase returns STATE
without those writes. Core zero-budget behavior remains STATE; its two actual
callers yield before invoking it with zero.

The variable fetch consumes at most the supplied byte cursor budget, clips to
the remaining 32 bytes and writes only complete U32 words. This is not a theorem
about total wrapper memory visits: existing fixed source/seal checks remain,
including up to two eight-word archived seal loads. The eight-word helper now
returns immediately outside its declared natural-index guard, closing its
negative-index termination stutter without changing any guarded call.

Nine direct Python source controls pass, including structural transformation
replay/idempotence and byte-identical legacy fetch. `event-read-verified-unit`
retains its actual admitted writer, simulated disk and semantic verifier. Its
new checks cover 32 separate budget-1 visits, no premature READ-RECORDS, zero and
invalid budget, public issue/member/reopen refusal with full output snapshots,
and actual pool-loan release after byte1 preserving the partial digest while
entering UNCERTAIN. `event-read-digest-cold-unit` produces a persisted checkpoint,
crashes, waits for selected boot's genuine semantic-success continuation,
checks public boot BEGIN and JOURNAL-BIND rejection with full output snapshots,
and drives the real cold journal-step through all32 byte visits. A separate
local digest instance runs the unchanged legacy fetch on the authenticated
source Ref before those visits; the final target must equal that oracle,
differ from its prefetch value, and preserve every other digest cell/scalar. Both new ACL2
consumer controls are UNRUN; guards/refinement and composed qualification remain
required. These are registered certification roots, not execution evidence.

Current literal closures: reader133, live fixture422, cold fixture448; no missing
local books or literal include cycles. No old whole-lane import, archive authority, hold release or FREE
activation is included. Lossless original-frame reconstruction, complete-prefix
LIVE obligation transfer and successive-checkpoint physical reuse remain open
in the broader D13 work.
