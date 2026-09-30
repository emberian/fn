; Witnesses and teeth for books/deflate-pool (the served read's pooled
; payload decoder, lane compress-3, PRF-949).  The payload is the held-out
; 1993 article and zlib's stream against the 2,749-octet dictionary from
; tests/acl2/payload-lz-record-tests.lisp.
(in-package "ACL2")
(include-book "../../books/deflate-pool-check")
(include-book "payload-deflate-vectors")
(include-book "must-fail-checked")

; Reads over one buffer set: POOLED = the pool the first read starts from is
; the host's NIL, the second read's the first's answer; FORGED = a first read
; over the empty dictionary (so the window has the length the fast branch
; checks), then a read from the pool (DICT 0 0), which claims the window is
; DICT's with no preset: (list A1 P1 OUT1 A2 P2 OUT2 REUSE2 C1 C2 CM CF),
; the C's `fn-zpl-pool-check' EVALUATED on the real window: C1 of the first
; read's pool, C2 of the second's, CM of the second's after one cell above
; its DIRTY bound is flipped, CF of the forged pool on the first's window.
; Flip the window cell at 40000 (above any DIRTY bound a 750-octet read
; leaves) and run the check again: (mv CHECK fn-zin-win).
(defun dpt-flip-check (pool fn-zin-win)
  (declare (xargs :stobjs fn-zin-win))
  (let ((fn-zin-win
         (if (< 40000 (fn-zin-win-len fn-zin-win))
             (fn-zin-win-put 40000 (if (equal (fn-zin-win-get 40000 fn-zin-win) 0) 1 0)
                             fn-zin-win)
           fn-zin-win)))
    (mv (fn-zpl-pool-check pool fn-zin-win) fn-zin-win)))

(defun dpt-reads (forged dict c n)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c) (natp n))))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (with-local-stobj fn-zin-win
        (mv-let (r fn-zin-win fn-octets)
          (with-local-stobj fn-zin-tab
            (mv-let (r fn-zin-tab fn-zin-win fn-octets)
              (with-local-stobj fn-zin-out
                (mv-let (r fn-zin-out fn-zin-tab fn-zin-win fn-octets)
                  (let ((fn-octets (fn-octets-from-list c fn-octets)))
                    (mv-let (a1 p1 fn-zin-win fn-zin-tab fn-zin-out)
                      (fn-zpl-decode-bufs nil (if forged nil dict) (fn-octets-len fn-octets) n
                                          fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                      (let ((out1 (fn-zin-out-list fn-zin-out))
                            (p (if forged (list dict 0 0) p1))
                            (c1 (fn-zpl-pool-check p1 fn-zin-win))
                            (cf (fn-zpl-pool-check (list dict 0 0) fn-zin-win)))
                        (let ((reuse (fn-zpl-reusep p dict fn-zin-win)))
                          (mv-let (a2 p2 fn-zin-win fn-zin-tab fn-zin-out)
                            (fn-zpl-decode-bufs p dict (fn-octets-len fn-octets) n
                                                fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                            (let ((c2 (fn-zpl-pool-check p2 fn-zin-win)))
                              (mv-let (cm fn-zin-win)
                                (dpt-flip-check p2 fn-zin-win)
                                (mv (list a1 p1 out1 a2 p2 (fn-zin-out-list fn-zin-out) reuse
                                          c1 c2 cm cf)
                                    fn-zin-out fn-zin-tab fn-zin-win fn-octets))))))))
                  (mv r fn-zin-tab fn-zin-win fn-octets)))
              (mv r fn-zin-win fn-octets)))
          (mv r fn-octets)))
      r)))

(defconst *dpt-pooled* (dpt-reads nil *plz-dict* *plz-dict-block* 750))
(defconst *dpt-forged* (dpt-reads t *plz-dict* *plz-dict-block* 750))

; KEYSTONE fn-zpl-decode-bufs-is-decode, reachable: both reads (the second
; from the first's pool, through the reuse branch) answer the decoder's
; status and its octets, the article; the pool each returns names the
; dictionary, its preset length and the cells the read wrote (750 < 32 KiB).
(defthm dpt-pooled-witness
  (let ((d (fn-pzd-decode *plz-dict* *plz-dict-block* 750)))
    (and (fn-cbor-octet-listp *plz-dict-block*) (natp 750) (fn-cbor-octet-listp *plz-dict*)
         (fn-zpl-pool-okp nil fn-zin-win)
         (equal d (list :ok *plz-article*))
         (equal (car (nth 0 *dpt-pooled*)) (car d))
         (equal (nth 2 *dpt-pooled*) (cadr d))
         (equal (nth 1 *dpt-pooled*) (list *plz-dict* 2749 750))
         (equal (nth 6 *dpt-pooled*) t)
         (equal (car (nth 3 *dpt-pooled*)) (car d))
         (equal (nth 5 *dpt-pooled*) (cadr d))
         (equal (nth 4 *dpt-pooled*) (list *plz-dict* 2749 750))))
  :hints (("Goal" :in-theory (enable (:e fn-pzd-decode))))
  :rule-classes nil)

; Without the pool invariant: the forged pool's H is not the dictionary's
; preset length, so fn-zpl-pool-okp fails; every other hypothesis holds; the
; read takes the reuse branch and does not answer the decoder's octets.
(defthm dpt-forged-without-pool-okp
  (let ((d (fn-pzd-decode *plz-dict* *plz-dict-block* 750)))
    (and (fn-cbor-octet-listp *plz-dict-block*) (natp 750) (fn-cbor-octet-listp *plz-dict*)
         (not (fn-zpl-pool-okp (list *plz-dict* 0 0) fn-zin-win))
         (equal (nth 6 *dpt-forged*) t)
         (not (and (equal (car (nth 3 *dpt-forged*)) (car d))
                   (equal (nth 5 *dpt-forged*) (cadr d))))))
  :hints (("Goal" :in-theory (e/d (fn-zpl-pool-okp (:e fn-pzd-decode)) (fn-zpl-ready-h))))
  :rule-classes nil)

(must-fail-checked
 (defthm dpt-decode-bufs-no-pool-okp
   (implies (and (fn-cbor-octet-listp c) (natp n) (fn-cbor-octet-listp dict))
            (let ((r (fn-zpl-decode-bufs pool dict (len c) n c fn-zin-win fn-zin-tab fn-zin-out)))
              (implies (equal (car (fn-pzd-decode dict c n)) :ok)
                       (equal (mv-nth 4 r) (cadr (fn-pzd-decode dict c n))))))
   :hints (("Goal" :do-not-induct t))))

; KEYSTONE fn-zpl-pool-check-is-pool-okp (books/deflate-pool-check), with
; fn-zpl-decode-bufs-is-decode's pool conclusion, evaluated: the invariant
; holds of the pool and window each pooled read returned (C1, C2), and the
; check is the invariant, so each is fn-zpl-pool-okp of a returned pool.
(defthm dpt-pool-check-witness
  (and (equal (nth 7 *dpt-pooled*) t)
       (equal (nth 8 *dpt-pooled*) t)
       (equal (nth 1 *dpt-pooled*) (list *plz-dict* 2749 750))
       (equal (nth 4 *dpt-pooled*) (list *plz-dict* 2749 750))
       (equal (fn-zpl-pool-check nil fn-zin-win) (fn-zpl-pool-okp nil fn-zin-win))
       (fn-zpl-pool-check nil fn-zin-win))
  :rule-classes nil)

; Corrupted-state witness (labelled): one window cell at 40000 >= DIRTY
; (750) flipped after the second read, and the check refuses (CM).  The
; forged pool (H = 0 against a 2,749-octet preset) is refused on the real
; window too (CF): the check has teeth on both H and the cells.
(defthm dpt-pool-check-corrupted
  (and (equal (nth 9 *dpt-pooled*) nil)
       (equal (nth 10 *dpt-pooled*) nil))
  :rule-classes nil)
