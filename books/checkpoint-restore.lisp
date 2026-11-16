; Recovery input frontier over actual B-format bytes. No serving/readiness or
; allocator mutation occurs here. Boot must finish candidate selection, roots,
; exact allocator restore, reachability protections and ordered suffix replay.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint")
(include-book "checkpoint-anchor-input")
(include-book "checkpoint-descriptor-input")
(include-book "checkpoint-restore-read")
(include-book "checkpoint-geometry")
(fn2-book-layer :b)

; Private scratch references must be beyond the candidate reference bank.
; Capturing a link never overwrites an authenticated descriptor root.


; Bounded anchor hash/framing check and candidate capture are inseparable.
; ROW's location is the actual anchor slot; its geometry digest must be loaded
; from the bootstrap-owned geometry before this call. This does not select a
; winner: every structurally valid target, including a singleton, must be read.


; Read planner for the descriptor or an authenticated descriptor root. The
; target is returned from the candidate's concrete Ref, never recomputed by
; the host. A 64KiB page is consumed through sector-sized reads by the boot
; machine; this leaf returns one sector and the caller's next byte cursor.


; Load one immutable expected digest into checker-owned input storage. The
; stripe's FC-HASH region is outside its hash-engine mutable result/frontier.
