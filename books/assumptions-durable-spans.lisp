; fn: adapter A4 of the spans landing, a named assumption (AGENTS.md: an
; encapsulate with a local witness, and the theorems that use it mention it).
;
; A-ARENA-SPAN-INTO.  The served ARTICLE path reads a payload window into a
; workspace `fn-octets' instead of as a list: `(fn-arena-get-span-into h at n
; fn-arena fn-octets)' appends to the buffer exactly the octets
; `fn-arena-get-span' answers for the same window.  The host implementation
; (host/native/extent.lisp) checks AT + N against the payload's length at
; entry; for an extent entry it runs the run loop of
; fnn-extent-window-realize-span with one `replace' per decided run from the
; trailer-verified window (fnn-extent-entry's check stays before any byte is
; exposed) into the buffer's array, and builds no list; every other entry kind
; writes `fn-arena$x-get' octet by octet into the buffer, likewise no list.  The family's native test asserts byte
; equality with `fn-arena-get-span' on the same window over every entry kind.
;
; Owner: Builder C.  Retired when Builder A's leased-handle read
; (fn-rtc-st$a-splice, books/runtime-contract-pool-impl.lisp on lane/vertical)
; is on dev and the served window reads through it (coordinator rulings (a)
; and (a'), 2026-10-09).

(in-package "ACL2")
(include-book "payload-arena")
(include-book "octets-stobj")

(local
 (defun fn-arena-span-into-ind (at n)
   (if (zp n) at (fn-arena-span-into-ind (+ 1 at) (1- n)))))

; A window inside a payload is octets, so the witness's append is guarded.
(defthm fn-arena-get-span-octets
  (implies (and (fn-arena-p fn-arena) (natp h) (< h (fn-arena-count fn-arena))
                (natp at) (natp n) (<= (+ at n) (fn-arena-payload-len h fn-arena)))
           (fn-cbor-octet-listp (fn-arena-get-span h at n fn-arena)))
  :hints (("Goal" :induct (fn-arena-span-into-ind at n)
                  :in-theory (enable fn-arena-get-span-is-the-gets))))

(encapsulate
  (((fn-arena-get-span-into * * * fn-arena fn-octets) => fn-octets
    :formals (h at n fn-arena fn-octets)
    :guard (and (natp h) (< h (fn-arena-count fn-arena))
                (natp at) (natp n)
                (<= (+ at n) (fn-arena-payload-len h fn-arena)))))

  (local (defun fn-arena-get-span-into (h at n fn-arena fn-octets)
           (declare (xargs :stobjs (fn-arena fn-octets)
                           :guard (and (natp h) (< h (fn-arena-count fn-arena))
                                       (natp at) (natp n)
                                       (<= (+ at n) (fn-arena-payload-len h fn-arena)))))
           (fn-octets-append-list (fn-arena-get-span h at n fn-arena) fn-octets)))

  (defthm fn-arena-get-span-into-is-append-list
    (equal (fn-arena-get-span-into h at n fn-arena fn-octets)
           (fn-octets-append-list (fn-arena-get-span h at n fn-arena) fn-octets))))
