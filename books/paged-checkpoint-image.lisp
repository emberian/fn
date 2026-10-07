; fn: the staged keystone's pre-state is the previous commit's image (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM-20261006.md section 3.3, phase 2c).
;
; STATEMENTS (written first; the proofs follow in this file).
;
; `fn-pck-x-stage-is-the-dirty' (paged-checkpoint-stage.lisp) assumes a mem0
; whose dirty pages hold the prefix tail then zeros, resident.  Here that state
; is derived from the image the previous commit left.
;
;   (pcki-img PW pgs-mem)   the tape invariant: pages 8..V-1 are all resident
;       (vi = 2); the arrays have the image's lengths (d = V, w = 2048 V); the
;       tape window (words 16384 .. 2048 V) is PW followed by zeros.
;
;   fn-pck-x-prestate   (pcki-img PW mem), the image grown to NPN pages
;       (`pgs-x-grow-image', zero pages, resident) with NPN covering
;       the last tape page of PW ++ a WL-word delta:
;         (pcks-res CNT (+ CNT WL) mem2)   -- every delta position is writable
;         (pgs-x-abs-dirty LP mem2) = (pck-shift 8 (adt-tp-dirty-at CNT TAIL zeros(WL)))
;       with CNT = (len PW), TAIL = PW's last partial page, LP the pages of that
;       set.  These are exactly premises (1) and (2) of the keystone.  The tail
;       page needs no separate read: the invariant holds it resident.
;
;   fn-pck-x-image-after-commit   the invariant is the loop's: from
;       (pcki-img PW mem), growing, staging the delta rows and
;       `pgs-x-commit-durable' on the tape's dirty pages leave
;       (pcki-img PW' mem4) with PW' the words of (prefix ++ delta); the
;       staging answers :ok.  So a store opened (every tape page filled and
;       verified) establishes the invariant once, and each publication keeps it.
;
; Not here (owed, PCK-STAGE-NEED-PAGE): a tail page that is not resident
; (lazy open) answers (:need-page LP); that path fills the page and retries.
