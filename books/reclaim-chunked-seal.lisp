; fn: pass 3 of the chunked reclaim (books/reclaim-chunked-walk.lisp): the
; rewritten chunks predicted into held rows from a carried handle and
; extended into the rebuilt capture; the rebuild over that capture is the
; owner the full open of the predicted history installs (lane reclaim,
; 2026-10-04, PRF-1315).
;
; KEYSTONES:
;   fn-rcw-predict-acc-steps-is-predict: the prediction chunk by chunk, each
;     from the handle the previous chunks' sealed payloads left, is :bad
;     exactly when fn-orcs-predict of the whole history is, and otherwise
;     finishes to the capture of fn-orcs-predict's rows, with the seal
;     payloads in order and the final handle H0 + their count;
;   fn-rcw-rebuild-of-the-chunked-capture-is-the-full-open: the host's
;     rebuild (fn-owner-orcp-rebuild) of that capture is the full open of
;     the predicted history (fn-ock-recover-full), the statement
;     fn-orcp-rebuild-is-the-full-open makes of the whole-list rebuild.
(in-package "ACL2")
(include-book "reclaim-chunked-walk")
(include-book "owner-reclaim-seal")
(include-book "owner-reclaim-carry")
(include-book "store-checkpoint-arena-writer")
(include-book "served-catalog-owner-keyed")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; 1. The prediction over a concatenation.

(local
 (defthm fn-rcw-predict-rows-of-append
   (implies (natp h)
            (equal (fn-orcs-predict-rows (append a b) keyring generation h)
                   (append (fn-orcs-predict-rows a keyring generation h)
                           (fn-orcs-predict-rows b keyring generation
                                                 (+ h (len (fn-orcs-payloads a)))))))
   :hints (("Goal" :in-theory (disable fn-orcs-held-of fn-record-p)))))

(local
 (defthm fn-rcw-payloads-of-append
   (equal (fn-orcs-payloads (append a b))
          (append (fn-orcs-payloads a) (fn-orcs-payloads b)))
   :hints (("Goal" :in-theory (disable fn-record-p)))))

(local
 (defthm fn-rcw-has-bad-of-append
   (equal (fn-orcs-has-bad (append a b))
          (or (fn-orcs-has-bad a) (fn-orcs-has-bad b)))))

(local
 (defthm fn-rcw-predict-of-true-list-fix
   (and (equal (fn-orcs-predict-rows (true-list-fix rows) keyring generation h)
               (fn-orcs-predict-rows rows keyring generation h))
        (equal (fn-orcs-payloads (true-list-fix rows)) (fn-orcs-payloads rows))
        (equal (fn-orcs-has-bad (true-list-fix rows)) (fn-orcs-has-bad rows)))
   :hints (("Goal" :in-theory (disable fn-orcs-held-of fn-record-p)))))

(local
 (defthm fn-rcw-predict-rows-true-listp
   (true-listp (fn-orcs-predict-rows rows keyring generation h))
   :rule-classes :type-prescription))

; -----------------------------------------------------------------------------
; 2. The host's call per chunk of pass 3: :bad when a row IS the intern's
; refusal word (fn-orcs-predict answers (:bad nil) then), else (ACC' H'
; PAYLOADS): ACC extended by the chunk's predicted rows from H, H advanced by
; the chunk's sealed payloads, which are returned for the swap's seal.
(defun fn-rcw-predict-acc-step (acc configs chunk keyring generation h)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-orcs-has-bad chunk)
      :bad
    (let ((rows (fn-orcs-predict-rows chunk keyring generation (nfix h)))
          (payloads (fn-orcs-payloads chunk)))
      (list (fn-rcw-acc-step acc configs rows)
            (+ (nfix h) (len payloads))
            payloads))))

(local
 (defthm fn-rcw-predict-acc-step-parts
   (and (equal (equal (fn-rcw-predict-acc-step acc configs chunk keyring generation h) :bad)
               (if (fn-orcs-has-bad chunk) t nil))
        (equal (car (fn-rcw-predict-acc-step acc configs chunk keyring generation h))
               (if (fn-orcs-has-bad chunk)
                   nil
                 (fn-rcw-acc-step acc configs
                                  (fn-orcs-predict-rows chunk keyring generation (nfix h)))))
        (equal (cadr (fn-rcw-predict-acc-step acc configs chunk keyring generation h))
               (if (fn-orcs-has-bad chunk) nil (+ (nfix h) (len (fn-orcs-payloads chunk)))))
        (equal (caddr (fn-rcw-predict-acc-step acc configs chunk keyring generation h))
               (if (fn-orcs-has-bad chunk) nil (fn-orcs-payloads chunk))))
   :hints (("Goal" :in-theory (union-theories '(fn-rcw-predict-acc-step car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(local (in-theory (disable fn-rcw-predict-acc-step fn-rcw-acc-step)))

; The steps, and the payloads they return in order (the host nconcs them).
(defun fn-rcw-predict-acc-steps (acc configs chunks keyring generation h payloads)
  (declare (xargs :guard t :verify-guards nil :measure (len chunks)))
  (if (consp chunks)
      (let ((r (fn-rcw-predict-acc-step acc configs (car chunks) keyring generation h)))
        (if (eq r :bad)
            :bad
          (fn-rcw-predict-acc-steps (car r) configs (cdr chunks) keyring generation
                                    (cadr r) (append payloads (caddr r)))))
    (list acc h payloads)))

(local
 (defun fn-rcw-predict-ind (acc configs chunks keyring generation h payloads prefix)
   (declare (xargs :verify-guards nil :measure (len chunks)))
   (if (consp chunks)
       (let ((r (fn-rcw-predict-acc-step acc configs (car chunks) keyring generation h)))
         (if (eq r :bad)
             (list prefix)
           (fn-rcw-predict-ind (car r) configs (cdr chunks) keyring generation
                               (cadr r) (append payloads (caddr r))
                               (append prefix (true-list-fix (car chunks))))))
     (list acc h payloads prefix))))

(local
 (defthm fn-rcw-predict-steps-from
   (implies (and (fn-rcw-accp acc) (natp h0) (natp h)
                 (not (fn-orcs-has-bad prefix))
                 (equal h (+ h0 (len (fn-orcs-payloads prefix))))
                 (equal payloads (fn-orcs-payloads prefix))
                 (equal (fn-rcw-acc-finish acc)
                        (fn-sco-capture configs
                                        (fn-orcs-predict-rows prefix keyring generation h0))))
            (let ((r (fn-rcw-predict-acc-steps acc configs chunks keyring generation h payloads))
                  (all (append prefix (fn-rcw-concat chunks))))
              (and (equal (equal r :bad) (if (fn-orcs-has-bad all) t nil))
                   (implies (not (equal r :bad))
                            (and (equal (fn-rcw-acc-finish (car r))
                                        (fn-sco-capture configs
                                                        (fn-orcs-predict-rows all keyring
                                                                              generation h0)))
                                 (equal (cadr r) (+ h0 (len (fn-orcs-payloads all))))
                                 (equal (caddr r) (fn-orcs-payloads all)))))))
   :hints (("Goal" :induct (fn-rcw-predict-ind acc configs chunks keyring generation h
                                               payloads prefix)
            :in-theory (disable fn-rcw-acc-finish fn-rcw-accp fn-sco-capture fn-sco-extend
                                fn-orcs-held-of fn-record-p))
           ("Subgoal *1/2" :use ((:instance fn-sco-extend-of-capture
                                            (prefix (fn-orcs-predict-rows prefix keyring
                                                                          generation h0))
                                            (suffix (fn-orcs-predict-rows (car chunks) keyring
                                                                          generation h)))
                                 (:instance fn-rcw-finish-of-step
                                            (chunk (fn-orcs-predict-rows (car chunks) keyring
                                                                         generation h))))
            :in-theory (e/d (fn-rcw-concat)
                            (fn-rcw-acc-finish fn-rcw-accp fn-sco-capture fn-sco-extend
                             fn-orcs-held-of fn-record-p))))))

(local
 (defthm fn-rcw-predict-of-atom
   (implies (atom rows)
            (and (equal (fn-orcs-predict-rows rows keyring generation h) nil)
                 (equal (fn-orcs-payloads rows) nil)
                 (equal (fn-orcs-has-bad rows) nil)))))

; KEYSTONE.  Pass 3 over the host's chunks from the empty capture and the
; base handle H0 is fn-orcs-predict over the whole rewritten history.
(defthm fn-rcw-predict-acc-steps-is-predict
  (implies (natp h0)
           (let ((r (fn-rcw-predict-acc-steps (fn-rcw-acc-init configs) configs chunks
                                              keyring generation h0 nil))
                 (all (fn-rcw-concat chunks)))
             (and (equal (equal r :bad) (if (fn-orcs-has-bad all) t nil))
                  (implies (not (equal r :bad))
                           (and (equal (fn-rcw-acc-finish (car r))
                                       (fn-sco-capture configs
                                                       (car (fn-orcs-predict all keyring
                                                                             generation h0))))
                                (equal (caddr r)
                                       (cadr (fn-orcs-predict all keyring generation h0)))
                                (equal (cadr r) (+ h0 (len (caddr r)))))))))
  :hints (("Goal" :use ((:instance fn-rcw-predict-steps-from
                                   (acc (fn-rcw-acc-init configs)) (h h0) (payloads nil)
                                   (prefix nil)))
           :in-theory (e/d (fn-orcs-predict)
                           (fn-rcw-acc-init fn-rcw-acc-finish fn-rcw-predict-acc-steps
                            fn-sco-capture fn-rcw-accp fn-orcs-predict-rows
                            fn-orcs-payloads fn-orcs-has-bad)))))

; -----------------------------------------------------------------------------
; 3. The rebuild.

; KEYSTONE.  The host's rebuild (fn-owner-orcp-rebuild) of the capture pass 3
; finishes is the owner the full open of the predicted rewritten history
; installs: the statement fn-orcp-rebuild-is-the-full-open makes of the
; whole-list rebuild, over the chunked form the host calls.
(defthm fn-rcw-rebuild-of-the-chunked-capture-is-the-full-open
  (implies (and (natp h0)
                (not (equal (fn-rcw-predict-acc-steps (fn-rcw-acc-init configs) configs chunks
                                                      keyring generation h0 nil)
                            :bad)))
           (equal (cadr (fn-owner-orcp-rebuild
                         (fn-rcw-acc-finish
                          (car (fn-rcw-predict-acc-steps (fn-rcw-acc-init configs) configs chunks
                                                         keyring generation h0 nil)))
                         configs frontier max-conns))
                  (fn-ock-recover-full configs frontier
                                       (car (fn-orcs-predict (fn-rcw-concat chunks) keyring
                                                             generation h0))
                                       max-conns)))
  :hints (("Goal" :use (fn-rcw-predict-acc-steps-is-predict
                        (:instance fn-owner-orcp-rebuild-of-capture-is-the-full-open
                                   (rows (car (fn-orcs-predict (fn-rcw-concat chunks) keyring
                                                               generation h0)))))
                  :in-theory (e/d (fn-orcs-predict)
                                  (fn-rcw-acc-init fn-rcw-acc-finish fn-rcw-predict-acc-steps
                                   fn-sco-capture fn-owner-orcp-rebuild fn-orcs-predict-rows
                                   fn-orcs-payloads fn-orcs-has-bad
                                   fn-rcw-predict-acc-steps-is-predict
                                   fn-owner-orcp-rebuild-of-capture-is-the-full-open)))))

; -----------------------------------------------------------------------------
; 4. Pass 2's writer walk, chunk by chunk.
;
; The checkpoint writer's inputs are the sealed payloads' lengths and
; sources, reversed (host/native/io.lisp fnn-checkpoint-walk: bounded
; fn-scka-srcs-n calls over one list).  Pass 2 calls fn-scka-srcs-n on each
; rewritten chunk whole, carrying the two accumulators.

(defun fn-rcw-srcs-steps (chunks lacc sacc fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp chunks)
      (let ((st (fn-scka-srcs-n (car chunks) (len (car chunks)) lacc sacc fn-arena)))
        (fn-rcw-srcs-steps (cdr chunks) (nth 1 st) (nth 2 st) fn-arena))
    (list nil lacc sacc)))

(local
 (defthm fn-rcw-canon-lens-srcs-of-append
   (and (equal (fn-scka-canon-lens (append a b) fn-arena)
               (append (fn-scka-canon-lens a fn-arena) (fn-scka-canon-lens b fn-arena)))
        (equal (fn-scka-canon-srcs (append a b) fn-arena)
               (append (fn-scka-canon-srcs a fn-arena) (fn-scka-canon-srcs b fn-arena))))
   :hints (("Goal" :in-theory (disable fn-scka-src-of fn-row-wire-of fn-scka-sealsp
                                       fn-scka-payload-of fn-scka-canon-lens-is-lens)))))

(local
 (defthm fn-rcw-true-listp-concat
   (true-listp (fn-rcw-concat chunks))
   :hints (("Goal" :in-theory (enable fn-rcw-concat)))))

(local
 (defthm fn-rcw-revappend-append
   (equal (revappend (append a b) acc)
          (revappend b (revappend a acc)))))

(local
 (defthm fn-rcw-canon-lens-srcs-of-atom
   (implies (atom rows)
            (and (equal (fn-scka-canon-lens rows fn-arena) nil)
                 (equal (fn-scka-canon-srcs rows fn-arena) nil)))))

(local
 (defthm fn-rcw-srcs-steps-is-revappend
   (implies (true-list-listp chunks)
            (equal (fn-rcw-srcs-steps chunks lacc sacc fn-arena)
                   (list nil
                         (revappend (fn-scka-canon-lens (fn-rcw-concat chunks) fn-arena) lacc)
                         (revappend (fn-scka-canon-srcs (fn-rcw-concat chunks) fn-arena) sacc))))
   :hints (("Goal" :in-theory (e/d (fn-rcw-concat)
                                   (fn-scka-src-of fn-row-wire-of fn-scka-sealsp
                                    fn-scka-payload-of fn-scka-canon-lens-is-lens
                                    fn-scka-canon-lens fn-scka-canon-srcs fn-scka-srcs-n))))))

; KEYSTONE.  The chunked writer walk is the host's one walk over the whole
; rewritten history (fnn-checkpoint-walk's bounded calls compose to it,
; fn-scka-srcs-n-compose).
(defthm fn-rcw-srcs-steps-is-the-walk
  (implies (true-list-listp chunks)
           (equal (fn-rcw-srcs-steps chunks lacc sacc fn-arena)
                  (fn-scka-srcs-n (fn-rcw-concat chunks) (len (fn-rcw-concat chunks))
                                  lacc sacc fn-arena)))
  :hints (("Goal" :in-theory (disable fn-rcw-srcs-steps fn-scka-srcs-n fn-scka-canon-lens
                                      fn-scka-canon-srcs fn-scka-canon-lens-is-lens)
                  :use (fn-rcw-srcs-steps-is-revappend
                        (:instance fn-scka-srcs-n-complete
                                   (rows (fn-rcw-concat chunks))
                                   (n (len (fn-rcw-concat chunks))))))))

; -----------------------------------------------------------------------------
; 5. The fresh catalog under the ring's key: the keyed clear, then the
; chunks, is the keyed open the pass called over the whole list.
(defthm fn-rcw-load-chunks-keyed-is-keyed-load
  (equal (fn-rcw-load-chunks chunks view-index fn-arena (fn-cat-clear-keyed key fn-cat))
         (fn-sca-load-held-rows-keyed key (fn-rcw-concat chunks) view-index fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-sca-load-held-rows-keyed fn-rcw-load-chunks-is-available-from)
                                  (fn-sca-load-held-rows-keyed-is-load-held-rows
                                   fn-sca-load-held-available-from fn-cat-clear-keyed
                                   fn-rcw-load-chunks)))))
