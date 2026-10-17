# Web lane — GPT-6.1 Sol

Owner: deputy_web. Worktree codex-sol-web, base origin/dev 041fceb1a.
Owns native web-host; agreed shared transport leaf fnn-socket-write-now in
io.lisp and delegation fnn-mux-write-now only, plus web ACL2 wrappers/tests.
Runtime owns owner/mux lifecycle; Served owns fifth render cold-read result.

Actual work underway: one registered I/O actor and fixed semantic worker, profile-bounded HTTP
records; private web octet stobjs, incremental request framing, TLS-now, async
POST completion mailbox/wake pipe, handle-chunk-step and cold-read render/poll,
per-session flow lease, partial output offsets and 4KiB HTTP body windows.
Host-called web session/reset mutations now enter reader sections.

Source changes are not an image or proof completion claim. HTML and NNTP reply
are still materialized in core web buffers; pre-materialization funding and
streamed rendering remain the output contract work coordinated with Foundations
and Served. No live deployment. Discriminating raw/native tests in preparation.

Raw witness passed at current source: actual semantic worker blocked alongside
healthy I/O event, independent socket close and deferred once semantic custody.
WEB-006/SCN-1099 claimed and specified. Archived record/log indexed in
planning/evidence-index.tsv. Native image tests are pending Integration.
Host bare load currently in progress; no certification/image claim.

Lifetime followups: 8e37db4f2 sole disposal claimant; assembler e822 actual forward transport name and second-finish fixture PASS. Receipt report planning/evidence/web-continuations-2026-10-03-lifetime.md archived; no image or funding claim.
