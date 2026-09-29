; Witnesses and teeth for books/deflate-inflate (the COMPRESS DEFLATE
; inflater; lane compress, PRF-909 and PRF-910).
;
; The streams are zlib's (tests/acl2/deflate-inflate-vectors.lisp, generated
; by planning/evidence/compress-2026-09-28/zin_vectors.py over fn's own
; text): a client session flushed per command (fixed blocks and the sync
; flush's empty stored blocks), prose in a dynamic block with a second
; message reaching into the window, stored blocks, a finished stream, the
; bomb, and one hand-built stream per malformation.
(in-package "ACL2")
(include-book "../../books/deflate-inflate")
(include-book "deflate-inflate-vectors")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; Helpers over local buffers.  `dzt-feed' runs one host call from a state
; given as its twenty fields, over the octets C from START, with the
; output OUT (a list) and bound LIM: (list STATUS B2 IP FIELDS OUT).

(defun dzt-load (i fields fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard (and (natp i) (nat-listp fields))
                  :measure (nfix (- 20 (nfix i)))))
  (if (and (natp i) (< i 20))
      (let ((fn-zin-st (fn-zin-set i (nfix (nth i fields)) fn-zin-st)))
        (dzt-load (1+ i) fields fn-zin-st))
    fn-zin-st))

(defun dzt-feed (b fields c start lim out)
  (declare (xargs :guard (and (natp b) (nat-listp fields) (fn-cbor-octet-listp c)
                              (natp start) (natp lim) (fn-cbor-octet-listp out))))
  (with-local-stobj fn-zin-st
    (mv-let (r fn-zin-st)
      (with-local-stobj fn-octets
        (mv-let (r fn-octets fn-zin-st)
          (with-local-stobj fn-zin-win
            (mv-let (r fn-zin-win fn-octets fn-zin-st)
              (with-local-stobj fn-zin-tab
                (mv-let (r fn-zin-tab fn-zin-win fn-octets fn-zin-st)
                  (with-local-stobj fn-zin-out
                    (mv-let (r fn-zin-out fn-zin-tab fn-zin-win fn-octets fn-zin-st)
                      (let* ((fn-zin-st (dzt-load 0 fields fn-zin-st))
                             (fn-octets (fn-octets-from-list c fn-octets))
                             (fn-zin-out (fn-zin-out-from-list out fn-zin-out)))
                        (mv-let (fn-zin-win fn-zin-tab) (fn-zin-buffers-ready fn-zin-win fn-zin-tab)
                          (mv-let (st b2 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                            (fn-zin-feed b fn-zin-st start (fn-octets-len fn-octets) lim
                                         fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                            (mv (list st b2 ip (fn-zin-fields-list 0 fn-zin-st)
                                      (fn-zin-out-list fn-zin-out))
                                fn-zin-out fn-zin-tab fn-zin-win fn-octets fn-zin-st))))
                      (mv r fn-zin-tab fn-zin-win fn-octets fn-zin-st)))
                  (mv r fn-zin-win fn-octets fn-zin-st)))
              (mv r fn-octets fn-zin-st)))
          (mv r fn-zin-st)))
      r)))

(defconst *dzt-initial*
  ; fn-zin-reset's fields: the Huffman length (field 11) starts at 1
  '(0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0))

(defun dzt-reset-fields ()
  (declare (xargs :guard t))
  (with-local-stobj fn-zin-st
    (mv-let (r fn-zin-st)
      (let ((fn-zin-st (fn-zin-reset fn-zin-st)))
        (mv (fn-zin-fields-list 0 fn-zin-st) fn-zin-st))
      r)))

(assert-event (equal (dzt-reset-fields) *dzt-initial*))

; -----------------------------------------------------------------------------
; The positive witnesses: every zlib stream inflates to exactly its text.

(assert-event
 (and (equal (fn-zin-inflate 100000 *dzv-session-z* 100000)
             (list :more *dzv-session* (third (fn-zin-inflate 100000 *dzv-session-z* 100000))))
      (equal (cadr (fn-zin-inflate 100000 *dzv-session-z* 100000)) *dzv-session*)
      (equal (car (fn-zin-inflate 100000 *dzv-prose-z* 100000)) :more)
      (equal (cadr (fn-zin-inflate 100000 *dzv-prose-z* 100000)) *dzv-prose*)
      (equal (car (fn-zin-inflate 100000 *dzv-stored-z* 100000)) :more)
      (equal (cadr (fn-zin-inflate 100000 *dzv-stored-z* 100000)) *dzv-session*)))

; The prose really is a dynamic block (HLIT recorded, field 14) and the
; session's first flush a fixed one (no HLIT).
(assert-event
 (and (< 256 (nth 14 (third (fn-zin-inflate 100000 *dzv-prose-z* 100000))))
      (equal (nth 14 (third (fn-zin-inflate 100000 *dzv-session-z* 100000))) 0)))

; A finished stream: every octet, then refused by name (the RFC 8054 layer
; never ends; a final block closes the connection).
(assert-event
 (let ((r (fn-zin-inflate 100000 *dzv-final-z* 100000)))
   (and (equal (car r) '(:refused :stream-ended))
        (equal (cadr r) *dzv-session*))))

; -----------------------------------------------------------------------------
; The refusals, each by its own name, before any wrong octet.

(assert-event
 (and (equal (fn-zin-inflate 1000 *dzv-bad-type* 1000)
             (list '(:refused :block-type) nil (third (fn-zin-inflate 1000 *dzv-bad-type* 1000))))
      (equal (car (fn-zin-inflate 1000 *dzv-bad-stored* 1000)) '(:refused :stored-length))
      (equal (car (fn-zin-inflate 1000 *dzv-bad-counts* 1000)) '(:refused :code-counts))
      (equal (car (fn-zin-inflate 1000 *dzv-bad-clcode* 1000)) '(:refused :code-length-code))
      (equal (car (fn-zin-inflate 1000 *dzv-too-far* 1000)) '(:refused :distance-too-far))
      (equal (fn-zin-inflate 1000 *dzv-bad-length* 1000)
             (list '(:refused :length-code) '(65) (third (fn-zin-inflate 1000 *dzv-bad-length* 1000))))
      (equal (cadr (fn-zin-inflate 1000 *dzv-bad-distance* 1000)) '(65))
      (equal (car (fn-zin-inflate 1000 *dzv-bad-distance* 1000)) '(:refused :distance-code))
      (equal (car (fn-zin-inflate 1000 *dzv-bad-repeat* 1000)) '(:refused :repeat-without-length))
      (equal (car (fn-zin-inflate 1000 *dzv-bad-code* 1000)) '(:refused :bad-code))
      (equal (cadr (fn-zin-inflate 1000 *dzv-bad-code* 1000)) nil)
      ; a table that is not ready is refused, not read
      (equal (car (dzt-feed 10 *dzt-initial* '(0 0 0 255 255) 0 10 nil))
             :more)))

(assert-event
 (and (stringp (fn-zin-refusal-text :bomb))
      (not (equal (fn-zin-refusal-text :bomb) (fn-zin-refusal-text :bad-code)))
      (not (equal (fn-zin-refusal-text :stream-ended) (fn-zin-refusal-text :bad-code)))))

; -----------------------------------------------------------------------------
; The bomb (PRF-910): 1 MiB of zeros in 1,037 octets is refused once the
; output reaches exactly 256 x (octets read) + 65,536, and not before.

(assert-event
 (let* ((r (fn-zin-inflate 10000000 *dzv-bomb-z* 10000000))
        (fields (third r)))
   (and (equal (car r) '(:refused :bomb))
        (equal (len (cadr r)) (nth 6 fields))
        (equal (nth 6 fields) (+ (* 256 (nth 7 fields)) 65536))
        (< (nth 7 fields) (len *dzv-bomb-z*))
        (not (member-equal 1 (cadr r))))))

; KEYSTONE fn-zin-feed-bomb-bound (hypothesis: the state within the bound).
; Witness: the bomb's state within the bound, one more call; the bound holds
; after it and the appended octets and the octets read are what the totals
; count.
(defun dzt-bomb-bound-holds (fields r out)
  (declare (xargs :guard (and (nat-listp fields) (true-listp r) (true-listp out))
                  :verify-guards nil))
  (let ((f2 (nth 3 r)))
    (and (<= (nth 6 f2) (+ (* 256 (nth 7 f2)) 65536))
         (equal (- (len (nth 4 r)) (len out)) (- (nth 6 f2) (nth 6 fields))))))

(assert-event
 (let* ((fields '(8 0 0 0 0 0 1000 5 0 0 0 1 0 0 0 0 0 0 0 0))
        (r (dzt-feed 1000 fields *dzv-session-z* 0 100000 nil)))
   (and (<= (nth 6 fields) (+ (* 256 (nth 7 fields)) 65536))
        (dzt-bomb-bound-holds fields r nil))))

; Without the hypothesis: a state already past the bound (70,000 octets out,
; none read) stays past it: the first octet is refused, the conclusion fails.
(assert-event
 (let* ((fields (update-nth 6 70000 *dzt-initial*))
        (r (dzt-feed 1000 fields *dzv-session-z* 0 100000 nil)))
   (and (not (<= (nth 6 fields) (+ (* 256 (nth 7 fields)) 65536)))
        (equal (car r) '(:refused :bomb))
        (not (<= (nth 6 (nth 3 r)) (+ (* 256 (nth 7 (nth 3 r))) 65536))))))

(must-fail-checked
 (defthm dzt-bomb-bound-without-okp
   (fn-zin-bomb-okp
    (mv-nth 3 (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-zin-feed-out-bound (hypothesis: (true-listp out)).  Witness:
; LIM 10 over the session: ten octets appended to three, the three kept.
; Removal: from the improper output (7 . 8) the answer's prefix is (7).

(assert-event
 (let ((r (dzt-feed 1000 *dzt-initial* *dzv-session-z* 0 13 '(1 2 3))))
   (and (true-listp '(1 2 3))
        (equal (car r) :full)
        (equal (len (nth 4 r)) 13)
        (equal (take 3 (nth 4 r)) '(1 2 3))
        (equal (nthcdr 3 (nth 4 r)) (take 10 *dzv-session*)))))

(defthm dzt-out-bound-improper-list
  (let ((r (fn-zin-feed 0 (list (make-list 20 :initial-element 0)) 0 0 0 nil
                        (make-list 65536 :initial-element 0)
                        (make-list 1446 :initial-element 0) '(7 . 8))))
    (and (not (true-listp '(7 . 8)))
         (equal (mv-nth 6 r) '(7 . 8))
         (not (true-listp (mv-nth 6 r)))))
  :rule-classes nil)

(must-fail-checked
 (defthm dzt-out-bound-without-true-listp
   (true-listp (mv-nth 6 (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win
                                      fn-zin-tab fn-zin-out)))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; Resumption, over zlib's streams.  The network's cuts: the session split at
; EVERY octet into two reads (the second a new buffer, as the host holds
; it) inflates to the session.  The quanta: seven actions per call.  The
; host's output bound: ten octets per call, the output cleared between.

(defun dzt-two-reads (c k)
  ; (list status out): C's first K octets in one call, the rest in a second
  ; call over a reloaded buffer, the same window, table and state.
  (declare (xargs :guard (and (fn-cbor-octet-listp c) (natp k) (<= k (len c)))
                  :verify-guards nil))
  (with-local-stobj fn-zin-st
    (mv-let (r fn-zin-st)
      (with-local-stobj fn-octets
        (mv-let (r fn-octets fn-zin-st)
          (with-local-stobj fn-zin-win
            (mv-let (r fn-zin-win fn-octets fn-zin-st)
              (with-local-stobj fn-zin-tab
                (mv-let (r fn-zin-tab fn-zin-win fn-octets fn-zin-st)
                  (with-local-stobj fn-zin-out
                    (mv-let (r fn-zin-out fn-zin-tab fn-zin-win fn-octets fn-zin-st)
                      (let* ((fn-zin-st (fn-zin-reset fn-zin-st))
                             (fn-octets (fn-octets-from-list (take k c) fn-octets)))
                        (mv-let (fn-zin-win fn-zin-tab) (fn-zin-buffers-ready fn-zin-win fn-zin-tab)
                          (mv-let (st1 b2 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                            (fn-zin-feed 1000000 fn-zin-st 0 k 1000000 fn-octets fn-zin-win
                                         fn-zin-tab fn-zin-out)
                            (declare (ignore b2 ip))
                            (let ((fn-octets (fn-octets-from-list (nthcdr k c) fn-octets)))
                              (mv-let (st2 b2 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                                (fn-zin-feed 1000000 fn-zin-st 0 (- (len c) k) 1000000
                                             fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                                (declare (ignore b2 ip))
                                (mv (list st1 st2 (fn-zin-out-list fn-zin-out))
                                    fn-zin-out fn-zin-tab fn-zin-win fn-octets fn-zin-st))))))
                      (mv r fn-zin-tab fn-zin-win fn-octets fn-zin-st)))
                  (mv r fn-zin-win fn-octets fn-zin-st)))
              (mv r fn-octets fn-zin-st)))
          (mv r fn-zin-st)))
      r)))

(defun dzt-every-cut (c k text)
  (declare (xargs :guard (and (fn-cbor-octet-listp c) (natp k))
                  :measure (nfix (- (1+ (len c)) (nfix k)))
                  :verify-guards nil))
  (if (and (natp k) (<= k (len c)))
      (and (equal (dzt-two-reads c k) (list :more :more text))
           (dzt-every-cut c (1+ k) text))
    t))

(assert-event (dzt-every-cut *dzv-session-z* 0 *dzv-session*))
(assert-event (dzt-every-cut (take 300 *dzv-prose-z*) 0
                             (cadr (fn-zin-inflate 100000 (take 300 *dzv-prose-z*) 100000))))

(defun dzt-quanta-loop (q fuel ip end lim clearp acc fn-octets fn-zin-st fn-zin-win fn-zin-tab
                           fn-zin-out)
  ; Host calls of Q actions and output bound LIM over one set of buffers,
  ; until the stream stops for want of input or is refused; CLEARP clears
  ; the output between calls, as the host does, accumulating it in ACC.
  (declare (xargs :stobjs (fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (posp q) (natp fuel) (natp ip) (natp end) (natp lim)
                              (<= end (fn-octets-len fn-octets)) (true-listp acc))
                  :measure (nfix fuel) :verify-guards nil))
  (if (zp fuel)
      (mv (list :fuel nil 0) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (mv-let (st b2 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (fn-zin-feed q fn-zin-st ip end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)
      (declare (ignore b2))
      (let ((acc (if clearp (append acc (fn-zin-out-list fn-zin-out)) acc)))
        (if (member-equal st '(:yield :full))
            (let ((fn-zin-out (if clearp (fn-zin-out-clear fn-zin-out) fn-zin-out)))
              (mv-let (r fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                (dzt-quanta-loop q (1- fuel) (nfix ip) end lim clearp acc fn-octets fn-zin-st
                                 fn-zin-win fn-zin-tab fn-zin-out)
                (mv (list (car r) (cadr r) (1+ (nfix (caddr r))))
                    fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
          (mv (list st (if clearp acc (fn-zin-out-list fn-zin-out)) 1)
              fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))))

(defun dzt-quanta (q c lim clearp)
  (declare (xargs :guard (and (posp q) (fn-cbor-octet-listp c) (natp lim)) :verify-guards nil))
  (with-local-stobj fn-zin-st
    (mv-let (r fn-zin-st)
      (with-local-stobj fn-octets
        (mv-let (r fn-octets fn-zin-st)
          (with-local-stobj fn-zin-win
            (mv-let (r fn-zin-win fn-octets fn-zin-st)
              (with-local-stobj fn-zin-tab
                (mv-let (r fn-zin-tab fn-zin-win fn-octets fn-zin-st)
                  (with-local-stobj fn-zin-out
                    (mv-let (r fn-zin-out fn-zin-tab fn-zin-win fn-octets fn-zin-st)
                      (let* ((fn-zin-st (fn-zin-reset fn-zin-st))
                             (fn-octets (fn-octets-from-list c fn-octets)))
                        (mv-let (fn-zin-win fn-zin-tab) (fn-zin-buffers-ready fn-zin-win fn-zin-tab)
                          (mv-let (r fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                            (dzt-quanta-loop q 100000 0 (len c) lim clearp nil fn-octets fn-zin-st
                                             fn-zin-win fn-zin-tab fn-zin-out)
                            (mv r fn-zin-out fn-zin-tab fn-zin-win fn-octets fn-zin-st))))
                      (mv r fn-zin-tab fn-zin-win fn-octets fn-zin-st)))
                  (mv r fn-zin-win fn-octets fn-zin-st)))
              (mv r fn-octets fn-zin-st)))
          (mv r fn-zin-st)))
      r)))

(assert-event
 (let ((r (dzt-quanta 7 *dzv-session-z* 100000 nil)))
   (and (equal (car r) :more) (equal (cadr r) *dzv-session*) (< 30 (caddr r)))))

(assert-event
 (let ((r (dzt-quanta 1000000 *dzv-prose-z* 10 t)))
   (and (equal (car r) :more) (equal (cadr r) *dzv-prose*) (< 150 (caddr r)))))

; -----------------------------------------------------------------------------
; The resumption keystones' hypotheses.  Each is a theorem about the loop
; (fn-zin-feed-unfolds equates it with the host entry).  The removal
; witnesses are ground terms in the logic: the buffers as lists.

(defconst *dzt-win* (make-list 65536 :initial-element 0))
(defconst *dzt-tab* (make-list 1446 :initial-element 0))
(defconst *dzt-st* (list *dzt-initial*))

; fn-zin-loop-split-budget without (equal (car r1) :yield): a first call
; that stopped for input (:more) keeps its budget; the "resumed" call from
; its state with B2 more is not the call with B1 + B2 (the budgets left
; differ).
(defthm dzt-split-budget-without-yield
  (let* ((r1 (fn-zin-loop 1000 0 0 100 *dzt-st* nil *dzt-win* *dzt-tab* nil))
         (r2 (fn-zin-loop 5 (mv-nth 2 r1) 0 100 (mv-nth 3 r1) nil
                          (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))))
    (and (natp 1000) (natp 5)
         (equal (car r1) :more)
         (not (equal (fn-zin-loop 1005 0 0 100 *dzt-st* nil *dzt-win* *dzt-tab* nil) r2))))
  :rule-classes nil)

(must-fail-checked
 (defthm dzt-split-budget-without-the-yield
   (implies (and (natp b1) (natp b2))
            (equal (fn-zin-loop (+ b1 b2) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                fn-zin-out)
                   (let ((r (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out)))
                     (fn-zin-loop b2 (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                                  (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
   :hints (("Goal" :do-not-induct t))))

; Without (natp b2): B2 = -1 resumes with no budget (:yield) while the
; whole call, with B1 - 1, is the first call's own :yield state earlier.
(defthm dzt-split-budget-without-natp
  (let* ((r1 (fn-zin-loop 3 0 5 100 *dzt-st* '(0 5 0 250 255) *dzt-win* *dzt-tab* nil))
         (r2 (fn-zin-loop -1 (mv-nth 2 r1) 5 100 (mv-nth 3 r1) '(0 5 0 250 255)
                          (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))))
    (and (equal (car r1) :yield)
         (not (natp -1))
         (not (equal (fn-zin-loop 2 0 5 100 *dzt-st* '(0 5 0 250 255) *dzt-win* *dzt-tab* nil)
                     r2))))
  :rule-classes nil)

; fn-zin-loop-split-input without (<= m end): the first call ran on to M
; past END, so it read octets the whole call never sees.
(defthm dzt-split-input-without-order
  (let* ((c '(0 5 0 250 255 1 2 3 4 5))
         (r1 (fn-zin-loop 1000 0 10 100 *dzt-st* c *dzt-win* *dzt-tab* nil))
         (r2 (fn-zin-loop (mv-nth 1 r1) (mv-nth 2 r1) 5 100 (mv-nth 3 r1) c
                          (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))))
    (and (equal (car r1) :more)
         (not (<= 10 5))
         (equal (mv-nth 6 r1) '(1 2 3 4 5))
         (not (equal (fn-zin-loop 1000 0 5 100 *dzt-st* c *dzt-win* *dzt-tab* nil) r2))))
  :rule-classes nil)

; fn-zin-loop-split-input without the :more: a first call that REFUSED
; (BTYPE 3), "resumed", refuses again one action later: the budgets left
; differ from the whole call's.
(defthm dzt-split-input-without-more
  (let* ((c '(6))
         (r1 (fn-zin-loop 10 0 1 100 *dzt-st* c *dzt-win* *dzt-tab* nil))
         (r2 (fn-zin-loop (mv-nth 1 r1) (mv-nth 2 r1) 1 100 (mv-nth 3 r1) c
                          (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))))
    (and (equal (car r1) '(:refused :block-type))
         (<= 1 1)
         (not (equal (fn-zin-loop 10 0 1 100 *dzt-st* c *dzt-win* *dzt-tab* nil) r2))))
  :rule-classes nil)

(must-fail-checked
 (defthm dzt-split-input-without-the-more
   (implies (<= (nfix m) (nfix end))
            (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                   (let ((r (fn-zin-loop b ip m lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out)))
                     (fn-zin-loop (mv-nth 1 r) (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                                  (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
   :hints (("Goal" :do-not-induct t))))

; fn-zin-run-append: the witness is the session's stream cut after the
; first command's flush; without the :more (the first part ends inside a
; stored block's header, so the run of A alone... still :more) the
; hypothesis is the one a budget cut breaks: see the split-input witness.
(assert-event
 (let* ((c *dzv-session-z*)
        (k 20)
        (a (take k c)) (rest (nthcdr k c)))
   (and (true-listp a) (true-listp rest)
        (equal (append a rest) c)
        (equal (dzt-two-reads c k) (list :more :more *dzv-session*)))))

; fn-zin-loop-is-run without (<= end (len x)): cells past the buffer read
; as nil (the loop stops at the buffer's end), while the list model's take
; pads with nil and reads them as octets 0.
(defthm dzt-is-run-past-the-buffer
  (let* ((x '(0 5 0 250))
         (lhs (fn-zin-loop 1000 0 6 100 *dzt-st* x *dzt-win* *dzt-tab* nil))
         (rhs (fn-zin-run 1000 *dzt-st* (take 6 (nthcdr 0 x)) 100 *dzt-win* *dzt-tab* nil)))
    (and (not (<= 6 (len x)))
         (not (equal lhs (list (car rhs) (mv-nth 1 rhs) (+ 0 (mv-nth 2 rhs)) (mv-nth 3 rhs)
                               (mv-nth 4 rhs) (mv-nth 5 rhs) (mv-nth 6 rhs))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; A preset dictionary (RFC 1950 section 2.2's FDICT; the stored payloads'
; shipped dictionary): zlib's stream over an article whose header lines are
; the dictionary's decodes with the preset loaded, and without it the first
; match reaches before the stream's first octet and is refused by name.
(assert-event
 (let ((r (fn-zin-inflate-with 100000 *dzv-dict* *dzv-dict-z* 100000)))
   (and (equal (car r) :more)
        (equal (cadr r) *dzv-dict-article*)
        (equal (nth 18 (caddr r)) (len *dzv-dict*)))))
(assert-event
 (equal (car (fn-zin-inflate 100000 *dzv-dict-z* 100000))
        '(:refused :distance-too-far)))
; The preset is the dictionary's LAST 32 KiB: a longer one keeps its tail.
(assert-event
 (let ((r (fn-zin-inflate-with 100000 (append (make-list 40000 :initial-element 32) *dzv-dict*)
                               *dzv-dict-z* 100000)))
   (and (equal (cadr r) *dzv-dict-article*)
        (equal (nth 18 (caddr r)) 32768))))
