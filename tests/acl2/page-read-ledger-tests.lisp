(in-package "ACL2")
(include-book "../../books/page-read-ledger")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *prl-budget* '(10000 0 2 1 10))
(defconst *prl-empty*
  (mv-nth 1 (mv-list 2 (fn-prl-register (fn-prl-make *prl-budget*) 11 '(8 0 1 0 0)))))
(defconst *prl-worker* '(4000 0 0 1 1))
(defconst *prl-native* '(3000 0 0 1 0))
(defconst *prl-read*
  (mv-list 3 (fn-prl-admit *prl-empty* 7 11 200 64 999 *prl-worker* *prl-native*)))
(defconst *prl-token* (mv-nth 1 *prl-read*))
(defconst *prl-issued* (mv-nth 2 *prl-read*))

(assert! (equal *prl-token* '(0 7 11 200 64 999)))
; Literal complete positive for funded admission.
(assert!
 (and (equal (mv-nth 0 *prl-read*) :admitted)
      (fn-prs-fundedp *prl-budget* '(0 0 0 0 0) '(0 0 0 0 0)
                     (fn-prl-nth 1 *prl-issued*))))
 ; Hypothesis removal for funded admission: the omitted :admitted
; hypothesis fails, and so does funding, with the malformed supplied pool.
(assert!
 (let* ((bad (fn-prl-make nil))
        (r (mv-list 3 (fn-prl-admit bad 7 11 200 64 999 *prl-worker* *prl-native*))))
   (and (not (equal (mv-nth 0 r) :admitted))
        (not (fn-prs-fundedp nil '(0 0 0 0 0) '(0 0 0 0 0)
                            (fn-prl-nth 1 (mv-nth 2 r)))))))
; No worker slot remains. Refusal creates no token and changes no state.
(assert!
 (equal (mv-list 3 (fn-prl-admit *prl-issued* 8 11 200 64 999 *prl-worker* *prl-native*))
        (list :read-resources-unavailable nil *prl-issued*)))
; A complete immutable token match is required: trailer, offset, file,
; client and ID changes are stale, even when other coordinates match.
(assert!
 (and (equal (mv-list 2 (fn-prl-settle *prl-issued* '(0 7 11 200 64 1000) nil))
             (list :stale *prl-issued*))
      (equal (mv-list 2 (fn-prl-settle *prl-issued* '(0 7 11 201 64 999) nil))
             (list :stale *prl-issued*))
      (equal (mv-list 2 (fn-prl-settle *prl-issued* '(0 7 12 200 64 999) nil))
             (list :stale *prl-issued*))
      (equal (mv-list 2 (fn-prl-settle *prl-issued* '(0 8 11 200 64 999) nil))
             (list :stale *prl-issued*))
      (equal (mv-list 2 (fn-prl-settle *prl-issued* '(1 7 11 200 64 999) nil))
             (list :stale *prl-issued*))))

(defconst *prl-finished* (mv-list 2 (fn-prl-settle *prl-issued* *prl-token* nil)))
; Literal complete positive for unconditional exactly-once replay.
(assert!
 (and (equal (mv-nth 0 *prl-finished*) :settled)
      (equal (mv-list 2 (fn-prl-settle (mv-nth 1 *prl-finished*) *prl-token* nil))
             (list :stale (mv-nth 1 *prl-finished*)))))
(assert! (equal (fn-prl-nth 1 (mv-nth 1 *prl-finished*)) '(8 0 1 0 1)))
(assert! (equal (fn-prl-nth 2 (mv-nth 1 *prl-finished*)) 1))

; A verified buffer published in the cache keeps its memory charged until
; actual eviction. Completion frees native thread/slot, not cached bytes.
(defconst *prl-published* (mv-list 2 (fn-prl-settle *prl-issued* *prl-token* t)))
(assert! (equal (fn-prl-nth 1 (mv-nth 1 *prl-published*)) '(1008 0 1 0 1)))
(assert!
 (and (equal (mv-nth 0 *prl-published*) :settled)
      (equal (mv-list 2 (fn-prl-settle (mv-nth 1 *prl-published*) *prl-token* t))
             (list :stale (mv-nth 1 *prl-published*)))))
(defconst *prl-evicted* (mv-list 2 (fn-prl-evict (mv-nth 1 *prl-published*) *prl-token*)))
(assert! (equal (fn-prl-nth 1 (mv-nth 1 *prl-evicted*)) '(8 0 1 0 1)))
(assert!
 (equal (mv-list 2 (fn-prl-evict (mv-nth 1 *prl-evicted*) *prl-token*))
        (list :stale (mv-nth 1 *prl-evicted*))))
(assert!
 (equal (mv-list 2 (fn-prl-evict *prl-issued* *prl-token*)) (list :stale *prl-issued*)))
; A subsequent request receives a fresh ID despite refundable completion.
(assert!
 (equal (mv-nth 1 (mv-list 3 (fn-prl-admit (mv-nth 1 *prl-finished*) 7 11 200 64 999
                                         *prl-worker* *prl-native*)))
        '(1 7 11 200 64 999)))
; Corrupted demand cannot claim a native refund larger than its charge.
(assert!
 (equal (mv-list 3 (fn-prl-admit *prl-empty* 7 11 200 64 999
                               *prl-worker* '(5000 0 0 1 0)))
        (list :invalid-read-demand nil *prl-empty*)))

; Incarnation credit is once per shared FD, independent of reader count.
(assert! (equal (mv-list 2 (fn-prl-register *prl-empty* 11 '(8 0 1 0 0)))
                (list :registered *prl-empty*)))
(assert! (equal (mv-list 2 (fn-prl-close *prl-issued* 11))
                (list :read-file-held *prl-issued*)))
(assert! (equal (mv-list 2 (fn-prl-close (mv-nth 1 *prl-published*) 11))
                (list :read-file-held (mv-nth 1 *prl-published*))))
(defconst *prl-closed* (mv-list 2 (fn-prl-close (mv-nth 1 *prl-finished*) 11)))
(assert! (equal (fn-prl-nth 1 (mv-nth 1 *prl-closed*)) '(0 0 0 0 1)))
(assert! (equal (mv-list 2 (fn-prl-close (mv-nth 1 *prl-closed*) 11))
                (list :stale (mv-nth 1 *prl-closed*))))
; An unregistered file cannot borrow another incarnation's descriptor.
(assert! (equal (mv-list 3 (fn-prl-admit *prl-empty* 7 12 200 64 999
                                      *prl-worker* *prl-native*))
                (list :invalid-read-demand nil *prl-empty*)))

(assert! (equal (fn-prl-close-preview *prl-issued* 11) :read-file-held))
(assert! (equal (fn-prl-close-preview (mv-nth 1 *prl-published*) 11) :read-file-held))
(assert! (equal (fn-prl-close-preview (mv-nth 1 *prl-finished*) 11) :closable))
(assert! (equal (fn-prl-close-preview (mv-nth 1 *prl-closed*) 11) :stale))
