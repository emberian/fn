# zero-copy-commit (2026-09-28): article credits, admitted before the body is retained

Lane zero-copy-commit (Claude Opus 5.5). PRF-377, SCN-193; requirement HST-024.
Coordinates: lane/zero-copy-commit 0132d90b8 (the change), merged with origin/dev at 484bf4241.

## 1. The finding that re-aimed the lane

The brief's motive was F8: "init reserves 1,187 MB against a 256 MB bar, and the per-connection reserve at the
article limit is the largest term". It is not a term at all. Evaluated in ACL2 (persvati REPL on
books/heap-reservation at origin/dev aa52ba4d6; the small preset, T = 16,384, H = 8 MiB, R = 196,608, HDR = 16,384,
A = 32,768; the F8 run's core 214,012,928 octets):

| term of init's 1,187 MiB | MiB |
|---|---|
| threads, 30 x (1,024 KiB stack + 4 MiB runtime), outside the heap | 150 |
| core file, outside the heap | 204 |
| heap: the full store's `:run` figure | ~833 |
| of which records, 2 x T x 12 KiB | 384 |
| of which the open's transient (chunk lists 76, 2H 16, 2 x 1,024 x T 32) | 124 |
| of which the image's dynamic content | ~138 |
| of which in flight (2 x capture budget 48, request lists 7.5) | 56 |
| of which memberships 16, arena 8.3, handles 0.75, collector room ~95 | |
| connections | **0** |

`fn-cbud-launch-decide`, the one function that added connection room to a heap figure, had no caller since lane
reservation-figure. The per-connection heap part entered only `fn-cbud-run-decide`, against the MACHINE. So the
F8 "reserved" clause cannot move with this lane, and core + threads alone (354 MiB) exceed its 256 MB: the metric's
definition went to ember (the coordinator's write-up; lane f8-reservation owns the budget model).

The real defect was the opposite one: a connection mid-article retains its body as octet lists (16 octets of heap
per octet, twice for the collector: 383,345 KiB a connection at A = 11 MiB) that the dynamic space never held, so
enough concurrent posters of large articles exhausted the heap (exit 4).

## 2. What the lane did (the credit path)

- **The pool** (books/heap-store-figure.lisp). One credit, `fn-heap-article-reserve-octets` = 2 x 16 x (512 + A +
  HDR): what an admitted article retains at most, first as the wire's body lists (within the body limit A and a
  line), then as its submission (the injected article within A and its groups within HDR, as lists). The pool
  `fn-heap-articles-octets` = max(r, min(32 r, 64 MiB)) is a term of the figure's base and of the need (inside the
  collector-room fixed point); `fn-heap-article-slots` = floor(pool / r), in [1, 32]. KEYSTONE
  `fn-heap-article-slots-are-held`. Small preset: 32 credits of 1,589,248 octets (48.5 MiB); A = 4 MiB: one
  credit; A = 600,000: three.
- **Admission before retention** (books/owner-article-slots.lisp, new). The host's served read is now
  `fn-oas-read-span` (host/owner-host.lisp `fn-owner-chunk-span-at`; the slots installed by
  `fn-owner-connection-budget` from the store's profile). It is `fn-otm-read-span` exactly unless the read leaves
  its connection newly in article mode with the owner holding more than the slots (`fn-oas-held`: connections in
  article mode + queued submissions + the batch in flight); then the read is re-run with the connection's posting
  bit off: a POST is answered `440 posting not permitted now; the articles in flight fill the memory, try again
  later` at the command (RFC 3977 6.3.1: nothing is sent), and an IHAVE/TAKETHIS that still enters article mode is
  answered `400 the articles in flight fill the memory; try again later` and closed, its wire dropped (RFC 3977
  3.2.1). KEYSTONE `fn-oas-read-span-admits-within-the-slots` (no hypothesis).
- **The credit moves with the request**: held in article mode, in the owner's queue, in the batch in flight;
  released when the commit answers. A client that vanishes mid-article drops its wire (nothing else owns the
  lists); a queued submission of a vanished client stays counted.
- **Completion policy: RESERVE-TO-FINISH.** A credit is the whole article's worst case (past the body limit the
  wire closes, 441), so an admitted connection's reads are never refused by the slots: KEYSTONE
  `fn-oas-read-span-never-blocks-an-admitted-article` (its read IS `fn-otm-read-span`). Partial uploads cannot
  hold the pool while each needs more of it; a stalled one holds its credit until its connection's idle timeout.
- books/connection-budget.lisp: the per-connection parser term is the command line only (the body moved to the
  pool); `fn-cbud-launch-decide` deleted. The friend's-node witness: 2,057 TLS-capable connections (was 619),
  441 KiB each (was 1,465).

## 3. Teeth

tests/acl2/owner-article-slots-tests.lisp, the host's call on live stobjs over owner-reader-read-tests' owner
(connection 0 with a posting configuration): reachable positive witness (one slot, POST offered 340, one held:
both antecedents and the conclusion); a CONSTRUCTED state (a queued submission) in which the read before this
lane offers the POST with two held in one slot (MUTATION: the old host call violates the conclusion) and the host's
call answers the memory 440, command consumed, posting bit restored; hypothesis removal for the admission keystone
(a connection already mid-article, zero slots: held 1 > 0); the never-blocks keystone's witness (that read equals
the read before this lane) and its hypothesis removal (not mid-article: the host's call differs). The pinned
figures of heap-figure-tests, heap-reservation-tests and connection-budget-tests re-taken (small preset
1,088 -> 1,137 MB on the 69046a76 core); heap-reservation-tests' growth theorem gained the A hypothesis and its
single-hypothesis counterexample (A raised to 64 KiB).

## 4. Runs

- Certification (persvati): certify-20260928T170547Z-326567, 11 passed (the affected roots: heap-store-figure,
  heap-figure, heap-open-nursery, heap-reservation, connection-budget, owner-article-slots and their tests),
  manifest in planning/evidence/manifests/. heap-figure 11.2 s and heap-store-figure 10.3 s at 8 jobs (baselines
  9.6 s and 8.1 s at 2 jobs; the lane's own forms add under 0.5 s).
- Recertified after depth_check's two loop twins (fn-oas-article-conns, fn-oas-post-effects):
  certify-20260928T173234Z-581479 (4 passed).
- Native (hbox /tank/fn/scratch/zero-copy-commit/native-s1, commit 0132d90b8, developer and production images):
  tests.test_native_article_slots 2/2 OK (SCN-193: five posters answered the memory 440 while one 4 MiB article
  was in flight, all six then accepted; three partial uploads holding the whole pool of three credits, two posters
  refused 440, the three finished last-admitted-first and all five accepted; the node never stopped), and
  tests.test_native_mux 4/4 OK (SCN-153; per-connection figure 313 KiB, measured 30.2 kB resident).
  The loop twins after it change no reply (the same functions as loops).
- Measurement: none (ember 18:15Z: no measurement campaigns during development; consed/POST and the reserved figure
  are measured at convergence).

## 5. Copies, honestly

Nothing here is zero-copy yet. A POSTed body is still copied: kernel -> the loop's read buffer (TLS: decrypted by
OpenSSL into it) -> fn-octets -> the wire's line and body lists (one cons per octet) -> the article event's lines ->
fn-post-body-octets' flat list -> the injection's parse and render -> the decision's list (queued) -> a byte vector
(fnn-owner-taken-octets) -> fn-octets -> (fn-octets-list) once more for the record -> the arena's seal -> the log's
write (and the digest reads it). The lane bounds how many of these can be alive at once (the credits) and charges
them to the dynamic space; it does not remove any.

## 6. Open

- **The body in bounded pooled chunks** (the credit's representation step): the wire in article mode names spans of
  the read for the host to append to per-request chunks from a shared pool (one octet a byte, not 32), ACL2
  deciding every span; boundary theorem: the staged octets equal `fn-post-body-octets` of the model's lines; then
  the decision over the chunks (header parse bounded by HDR, body a reference), the submission naming chunks, the
  seal from them. That lowers the credit about 32-fold (small preset 1.59 MB -> ~50 KB). High fan-in: the wire
  state is stated in books/wire*.lisp, served.lisp, transit-bound and the owner invariants.
- A frame theorem: one connection's read leaves every other connection's wire mode as it was (the invariant
  "held <= slots between reads" needs it beside the per-read keystone).
- The reply term (2A + 1,024 a connection) is still charged to the machine only: many readers of the largest
  article at once can still exhaust the heap until replies are rendered in windows (PKT-644).
