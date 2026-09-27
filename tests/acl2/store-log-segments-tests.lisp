; Witnesses and teeth for books/store-log-segments.lisp (lane log-recovery):
; the segment names, the open's plan, the chain-broken classification, the
; rotation kernel and T8 (fn-lg-segment-drop-preserves-the-open) over a
; two-segment ground log of the log core's workload records.
(in-package "ACL2")
(include-book "../../books/store-log-segments")
(include-book "../../books/frame-trailer")
(include-book "must-fail-checked")
; The record codec seam's attachment: the log's txid reads the record through
; fn-record-decode-exact (books/store-log-txid.lisp).
(include-book "../../books/codec-attach")

; -----------------------------------------------------------------------------
; Names.

(assert-event (equal (fn-lgs-segment-name 1) "000001.log"))
(assert-event (equal (fn-lgs-segment-name 42) "000042.log"))
(assert-event (equal (fn-lgs-segment-name 999999) "999999.log"))
(assert-event (equal (fn-lgs-segment-index "000001.log") 1))
(assert-event (equal (fn-lgs-segment-index "000042.log") 42))
(assert-event (equal (fn-lgs-segment-index "000000.log") nil))
(assert-event (equal (fn-lgs-segment-index "00001.log") nil))
(assert-event (equal (fn-lgs-segment-index "00000a.log") nil))
(assert-event (equal (fn-lgs-segment-index "000001.lo") nil))
(assert-event (equal (fn-lgs-segment-index "000001.log.new") nil))
(assert-event (equal (fn-lgs-segment-index 7) nil))
(assert-event (equal (fn-lgs-next-segment 1) 2))
(assert-event (equal (fn-lgs-next-segment 999999) nil))

; -----------------------------------------------------------------------------
; The open's plan.

(assert-event (equal (fn-lgs-open-plan '("000001.log" "000002.log") nil)
                     '(:scan (1 2) nil)))
(assert-event (equal (fn-lgs-open-plan '("000002.log" "000001.log" "x.tmp") 2)
                     '(:scan (2) (1))))
(assert-event (equal (fn-lgs-open-plan '("000003.log" "000002.log") 2)
                     '(:scan (2 3) nil)))
; the drop was interrupted between two unlinks: the covered one left is
; dropped again and the scan is unchanged
(assert-event (equal (fn-lgs-open-plan '("000002.log" "000003.log" "000004.log") 3)
                     '(:scan (3 4) (2))))
(assert-event (equal (fn-lgs-open-plan '("000003.log" "000004.log") 3)
                     '(:scan (3 4) nil)))
; refusals by name
(assert-event (equal (fn-lgs-open-plan '("000002.log" "000003.log") nil)
                     '(:refused :checkpoint-damaged)))
(assert-event (equal (fn-lgs-open-plan '("000002.log" "000004.log") 2)
                     '(:refused :history-short-of-checkpoint)))
(assert-event (equal (fn-lgs-open-plan '("000002.log") 3)
                     '(:refused :history-short-of-checkpoint)))
(assert-event (equal (fn-lgs-open-plan '("000001.log" "000003.log") nil)
                     '(:refused :history-short-of-checkpoint)))
(assert-event (equal (fn-lgs-open-plan nil nil)
                     '(:refused :no-segment)))
(assert-event (equal (fn-lgs-open-plan '("x.tmp") 2)
                     '(:refused :history-short-of-checkpoint)))

; -----------------------------------------------------------------------------
; A two-segment ground log.  Segment 1 holds records at txids 1 and 2, segment
; 2 (rotated from segment 1: its genesis is segment 1's last trailer) the
; record at txid 3; each is preallocated with zeros past its entries.

(defconst *slst-unit* 4096)
(defconst *slst-max* 65536)
(defconst *slst-r1* (fn-lg-workload-record 1 100))
(defconst *slst-r2* (fn-lg-workload-record 2 100))
(defconst *slst-r3* (fn-lg-workload-record 3 100))
(defconst *slst-g0* *fn-lg-genesis*)
; Segment 1 holds two entries, one record each (two batches: since log-2 an
; entry carries a whole batch, so one fn-lg-log of both would be ONE entry and
; the torn-tail case below would tear the only entry).
(make-event `(defconst *slst-g01* ',(fn-lg-last-trailer (list *slst-r1*) *slst-g0*)))
(make-event `(defconst *slst-g1* ',(fn-lg-last-trailer (list *slst-r2*) *slst-g01*)))
(make-event `(defconst *slst-seg1* ',(append (fn-lg-log (list *slst-r1*) *slst-g0* *slst-unit*)
                              (fn-lg-log (list *slst-r2*) *slst-g01* *slst-unit*)
                              (fn-bs-zeros *slst-unit*))))
(make-event `(defconst *slst-seg2* ',(append (fn-lg-log (list *slst-r3*) *slst-g1* *slst-unit*)
                              (fn-bs-zeros *slst-unit*))))
; a stale segment 2: the same record chained from the genesis instead
(make-event `(defconst *slst-stale2* ',(append (fn-lg-log (list *slst-r3*) *slst-g0* *slst-unit*)
                                (fn-bs-zeros *slst-unit*))))

(assert-event (equal (fn-lgs-chain-records (list *slst-seg1*) *slst-g0* *slst-unit* *slst-max*)
                     (list *slst-r1* *slst-r2*)))
(assert-event (equal (fn-lgs-chain-last (list *slst-seg1*) *slst-g0* *slst-unit* *slst-max*)
                     *slst-g1*))
(assert-event (equal (fn-lgs-chain-records (list *slst-seg1* *slst-seg2*) *slst-g0*
                                           *slst-unit* *slst-max*)
                     (list *slst-r1* *slst-r2* *slst-r3*)))

; The chain's stops: an honest segment ends in zeros (not broken); the stale
; segment scanned from the right genesis stops at its first entry, which
; validates under another predecessor: refused log-chain-broken, never read
; as a torn tail.  A torn tail (the second entry's frame cut short) is not.
(assert-event (not (fn-lgs-chain-broken-p *slst-seg1* *slst-g0* *slst-unit* *slst-max*)))
(assert-event (not (fn-lgs-chain-broken-p *slst-seg2* *slst-g1* *slst-unit* *slst-max*)))
(assert-event (equal (car (fn-lg-scan *slst-stale2* *slst-g1* *slst-unit* *slst-max*)) nil))
(assert-event (fn-lgs-chain-broken-p *slst-stale2* *slst-g1* *slst-unit* *slst-max*))
(make-event `(defconst *slst-torn1* ',(append (fn-bs-take (+ *slst-unit* 50) *slst-seg1*)
          (fn-bs-zeros (- (len *slst-seg1*) (+ *slst-unit* 50))))))
(assert-event (equal (car (fn-lg-scan *slst-torn1* *slst-g0* *slst-unit* *slst-max*))
                     (list *slst-r1*)))
(assert-event (not (fn-lgs-chain-broken-p *slst-torn1* *slst-g0* *slst-unit* *slst-max*)))

; -----------------------------------------------------------------------------
; Rotation: the kernel of segment 1 recovered, rotated, is the kernel recovery
; derives from segment 2's zeros with segment 1's last trailer.

(make-event `(defconst *slst-ks1* ',(fn-lgk-recover *slst-seg1* *slst-g0* *slst-unit* *slst-max* 3)))
(assert-event (fn-lgs-rotate-admitsp *slst-ks1*))
(assert-event (equal (fn-lgk-last *slst-ks1*) *slst-g1*))
(assert-event (equal (fn-lgs-rotate *slst-ks1*)
                     (fn-lgk-recover (fn-bs-zeros *slst-unit*) *slst-g1* *slst-unit* *slst-max* 3)))
(assert-event (not (fn-lgs-rotate-admitsp (fn-lgk-prepare *slst-ks1* *slst-r3*))))
(assert-event (fn-lgs-rotate-needed-p *slst-ks1*))
(assert-event (not (fn-lgs-rotate-needed-p (fn-lgs-rotate *slst-ks1*))))

; -----------------------------------------------------------------------------
;; T8, reachable, over the host's fold (fn-lg-open-kernel per segment, read
; as a string): the checkpoint at the rotation captures segment 1's records,
; its F row's genesis is segment 1's last trailer; the drop leaves segment 2
; and the history the open replays is the full fold's.
(defun slst-chars (octets)
  (if (consp octets) (cons (code-char (nfix (car octets))) (slst-chars (cdr octets))) nil))
(defun slst-text (octets) (coerce (slst-chars octets) 'string))
(make-event `(defconst *slst-t1* ',(slst-text *slst-seg1*)))
(make-event `(defconst *slst-t2* ',(slst-text *slst-seg2*)))
(defconst *slst-prefix* (list *slst-r1* *slst-r2*))
; The host's string classifier is the model's (fn-lgs-chain-broken-string-p-
; is-the-model), at the honest and the stale segment.
(make-event `(defconst *slst-t-stale2* ',(slst-text *slst-stale2*)))
(assert-event (not (fn-lgs-chain-broken-string-p *slst-t1* *slst-g0* *slst-unit* *slst-max*)))
(assert-event (not (fn-lgs-chain-broken-string-p *slst-t2* *slst-g1* *slst-unit* *slst-max*)))
(assert-event (fn-lgs-chain-broken-string-p *slst-t-stale2* *slst-g1* *slst-unit* *slst-max*))
(assert-event (fn-lgs-octets-of (list *slst-t1* *slst-t2*)))
(assert-event (equal (fn-lgs-octets-of (list *slst-t1* *slst-t2*)) (list *slst-seg1* *slst-seg2*)))
(assert-event
 (and (equal *slst-prefix* (fn-lgs-open-chain-records (list *slst-t1*) *slst-g0* *slst-unit* *slst-max*))
      (equal *slst-g1* (fn-lgs-open-chain-last (list *slst-t1*) *slst-g0* *slst-unit* *slst-max*))
      (equal (append *slst-prefix*
                     (fn-lgs-open-chain-records (list *slst-t2*) *slst-g1* *slst-unit* *slst-max*))
             (fn-lgs-open-chain-records (list *slst-t1* *slst-t2*) *slst-g0* *slst-unit* *slst-max*))
      (equal (fn-lgs-open-chain-records (list *slst-t1* *slst-t2*) *slst-g0* *slst-unit* *slst-max*)
             (list *slst-r1* *slst-r2* *slst-r3*))))

; Without the genesis hypothesis: the F row names the zero genesis; the prefix
; hypothesis holds, the genesis one fails, the suffix scans to nothing and the
; conclusion fails.
(assert-event (equal *slst-prefix* (fn-lgs-open-chain-records (list *slst-t1*) *slst-g0* *slst-unit* *slst-max*)))
(assert-event (not (equal *slst-g0* (fn-lgs-open-chain-last (list *slst-t1*) *slst-g0* *slst-unit* *slst-max*))))
(assert-event
 (not (equal (append *slst-prefix*
                     (fn-lgs-open-chain-records (list *slst-t2*) *slst-g0* *slst-unit* *slst-max*))
             (fn-lgs-open-chain-records (list *slst-t1* *slst-t2*) *slst-g0* *slst-unit* *slst-max*))))
(must-fail-checked
 (with-prover-step-limit
  20000
  (defthm slst-t8-without-genesis
    (implies (equal prefix (fn-lgs-open-chain-records covered genesis0 unit max))
             (equal (append prefix (fn-lgs-open-chain-records remaining genesis unit max))
                    (fn-lgs-open-chain-records (append covered remaining) genesis0 unit max)))
    :hints (("Goal" :in-theory (disable fn-lgs-open-chain-records fn-lgs-open-chain-last))))))

; Without the prefix hypothesis: the checkpoint captured record 1 only; the
; genesis hypothesis holds, the prefix one fails, the history misses record 2.
(assert-event (equal *slst-g1* (fn-lgs-open-chain-last (list *slst-t1*) *slst-g0* *slst-unit* *slst-max*)))
(assert-event (not (equal (list *slst-r1*)
                          (fn-lgs-open-chain-records (list *slst-t1*) *slst-g0* *slst-unit* *slst-max*))))
(assert-event
 (not (equal (append (list *slst-r1*)
                     (fn-lgs-open-chain-records (list *slst-t2*) *slst-g1* *slst-unit* *slst-max*))
             (fn-lgs-open-chain-records (list *slst-t1* *slst-t2*) *slst-g0* *slst-unit* *slst-max*))))
(must-fail-checked
 (with-prover-step-limit
  20000
  (defthm slst-t8-without-prefix
    (implies (equal genesis (fn-lgs-open-chain-last covered genesis0 unit max))
             (equal (append prefix (fn-lgs-open-chain-records remaining genesis unit max))
                    (fn-lgs-open-chain-records (append covered remaining) genesis0 unit max)))
    :hints (("Goal" :in-theory (disable fn-lgs-open-chain-records fn-lgs-open-chain-last))))))

; -----------------------------------------------------------------------------
; fn-lgs-open-plan-scan-ignores-covered (the drop's crash points).

; Reachable: segment 1 left by a drop cut, the checkpoint names segment 2.
(assert-event (and (posp 2) (fn-lgs-all-below-p (fn-lgs-indices '("000001.log")) 2)))
(assert-event (equal (fn-lgs-open-plan (append '("000001.log") '("000002.log" "000003.log")) 2)
                     '(:scan (2 3) (1))))
(assert-event (equal (cadr (fn-lgs-open-plan '("000002.log" "000003.log") 2)) '(2 3)))
; Without all-below: a "covered" segment at the first suffix segment itself.
(assert-event (posp 2))
(assert-event (not (fn-lgs-all-below-p (fn-lgs-indices '("000002.log")) 2)))
(assert-event (not (equal (car (fn-lgs-open-plan (append '("000002.log") '("000003.log")) 2))
                          (car (fn-lgs-open-plan '("000003.log") 2)))))
(must-fail-checked
 (with-prover-step-limit
  20000
 (defthm slst-plan-without-below
   (implies (posp first)
            (equal (car (fn-lgs-open-plan (append covered names) first))
                   (car (fn-lgs-open-plan names first)))))))
; Without posp first: no checkpoint names a first segment; segment 1 decides.
(assert-event (not (posp nil)))
(assert-event (fn-lgs-all-below-p (fn-lgs-indices nil) nil))
(assert-event (not (equal (car (fn-lgs-open-plan (append '("000001.log") '("000002.log")) nil))
                          (car (fn-lgs-open-plan '("000002.log") nil)))))
(must-fail-checked
 (with-prover-step-limit
  20000
 (defthm slst-plan-without-first
   (implies (fn-lgs-all-below-p (fn-lgs-indices covered) first)
            (equal (car (fn-lgs-open-plan (append covered names) first))
                   (car (fn-lgs-open-plan names first)))))))
