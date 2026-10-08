; P12 named resource refusal (PRF-1073): refusal before allocating a cold
; dependency is not a deadline observation. RFC 3977 section 3.2.1 code 403.
(in-package "ACL2")
(include-book "owner-cold-line")
(include-book "failure-scope")
(include-book "page-read-executor")

(defun fn-orln-refusalp (word)
  (declare (xargs :guard t))
  (and (member-equal word '(:read-resources-unavailable :read-identities-exhausted)) t))

(defun fn-orln-unavailable-line (word)
  (declare (xargs :guard t))
  (append (fn-osch-text
           (if (equal word :read-identities-exhausted)
               "403 article temporarily unavailable; cold read identities exhausted; try after restart"
             "403 article temporarily unavailable; cold read resources unavailable; try again later"))
          '(13 10)))

(defun fn-orln-unavailable-result (oc id i end word)
  (declare (xargs :guard t))
  (fn-own-tls-make-result (nfix (- (nfix end) (nfix i)))
                         (list (fn-nntp-reply-effect (fn-orln-unavailable-line word)))
                         (fn-ocln-owner-at-line oc id) nil))

(defun fn-orln-unavailable-span (oc id i word fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))))
  (if (and (fn-orln-refusalp word) (fn-ocln-commandp oc id))
      (fn-orln-unavailable-result oc id i (fn-oct-line-end i fn-octets) word)
    nil))

(local
 (defthm fn-orln-line-end-progress
   (implies (and (natp i) (< i (fn-octets-len fn-octets)))
            (< i (fn-oct-line-end i fn-octets)))
   :hints (("Goal" :in-theory (enable fn-oct-line-end)))
   :rule-classes :linear))

(defthm fn-orln-a-refused-cold-line-is-answered-unavailable
  (implies (and (natp i) (<= i (fn-octets-len fn-octets))
                (fn-orln-refusalp word) (fn-ocln-commandp oc id))
           (let ((r (fn-orln-unavailable-span oc id i word fn-octets)))
             (and (equal (fn-own-tls-result-consumed r)
                         (- (fn-oct-line-end i fn-octets) i))
                  (implies (< i (fn-octets-len fn-octets))
                           (< 0 (fn-own-tls-result-consumed r)))
                  (equal (fn-own-tls-result-effects r)
                         (list (list :reply (fn-orln-unavailable-line word))))
                  (equal (take 3 (fn-orln-unavailable-line word)) '(52 48 51))
                  (equal (fn-own-tls-result-owner r) (fn-ocln-owner-at-line oc id)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-orln-unavailable-span
                                    fn-orln-unavailable-result fn-orln-refusalp
                                    fn-orln-unavailable-line fn-osch-text
                                    fn-own-tls-make-result fn-own-tls-result-consumed
                                    fn-own-tls-result-effects fn-own-tls-result-owner
                                    fn-nntp-reply-effect fn-oct-line-end))))

(defthm fn-orln-not-refused-or-not-command-by-definition
  (implies (or (not (fn-orln-refusalp word)) (not (fn-ocln-commandp oc id)))
           (equal (fn-orln-unavailable-span oc id i word fn-octets) nil)))

(in-theory (disable fn-orln-refusalp fn-orln-unavailable-line
                    fn-orln-unavailable-result fn-orln-unavailable-span))

; The 403 that answers a retrieval whose payload read did not come
; (books/article-stream-owner.lisp fn-asto-plan-unavailable): past its
; dependency deadline it is time-bars' line (fn-otb-unavailable-line, C3);
; refused by name before allocation it is this book's line (P12).  NIL for
; any other word: the host has no reply to give in its place.
(defun fn-orln-preflight-line (word since now limit)
  (declare (xargs :guard t))
  (cond ((equal word :unavailable) (fn-otb-unavailable-line since now limit))
        ((fn-orln-refusalp word) (fn-orln-unavailable-line word))
        (t nil)))

; KEYSTONE.  Every line it gives begins with the 403 code, and it gives one
; exactly for the deadline and the two named refusals.
(defthm fn-orln-preflight-line-is-a-403
  (let ((line (fn-orln-preflight-line word since now limit)))
    (and (iff line (or (equal word :unavailable) (fn-orln-refusalp word)))
         (implies line (equal (take 3 line) '(52 48 51)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-orln-preflight-line fn-orln-unavailable-line
                                     fn-otb-unavailable-line fn-osch-text fn-orln-refusalp))))

(in-theory (disable fn-orln-preflight-line))

; ---------------------------------------------------------------------------
; THE PUBLICATION'S OWN READS (lane pool-refusal, 2026-10-05).  A checkpoint
; publication reads the arena synchronously inside ACL2 calls (the walk,
; fn-scka-srcs-n; the arena steps, fn-scka-write-step) and, after its
; install, reads each new frame and reseats it (fn-xrt-reseat-checkpoint-
; frame, whose payload comparison reads the old extent).  A read the pool
; refuses there used to be raised inside the call, where the dispatcher
; (host/native/io.lisp fnn-call) makes every condition a fault: the owner
; stopped, exit 4 (peer catch-up native, 1000 posts: "extent read refused:
; READ-RESOURCES-UNAVAILABLE").  The host now hands the refusal's word back
; to the stage that asked (host/native/io.lisp fnn-extent-with-read-refusal)
; and this decides it:
;   * the walk or an arena step: the publication is deferred -- refused as a
;     Store write refused before publication (fnn-store-io-refusal: nothing
;     stored, the old checkpoint stays, the next decision publishes again);
;   * the release's reseat of one frame: that frame is deferred -- not
;     reseated, its old files stay retired until a later publication's frame
;     names the payloads;
;   * any other word (a malformed demand, an unknown resource state) or any
;     other stage stays a fault.
(defconst *fn-orln-read-stages* '(:checkpoint-walk :checkpoint-write :checkpoint-release))

(defun fn-orln-read-refusal-outcome (stage word)
  (declare (xargs :guard t))
  (cond ((not (fn-orln-refusalp word)) :fault)
        ((member-eq stage '(:checkpoint-walk :checkpoint-write)) :defer-publication)
        ((eq stage :checkpoint-release) :defer-frame)
        (t :fault)))

; The condition class the host raises for an outcome (NIL: none, the stage
; goes on); the failure scope's tables classify it (books/failure-scope.lisp).
(defun fn-orln-read-refusal-class (outcome)
  (declare (xargs :guard t))
  (case outcome
    (:defer-publication "fnn-store-io-refusal")
    (:defer-frame nil)
    (otherwise "fnn-store-fault")))

; KEYSTONE.  An exhausted pool (either named refusal) on a read any stage of
; the publication runs is a deferral, never a fault: the frame's is no
; condition at all, the publication's is a class the failure scope
; classifies as a refusal at every step.  Teeth (tests/acl2/
; owner-resource-line-tests.lisp): the class the dispatcher made of it
; before, fnn-store-fault, classifies as a fault; a word that is not an
; exhausted pool still faults.
(defthm fn-orln-exhausted-pool-never-faults-a-publication
  (implies (and (member-equal stage *fn-orln-read-stages*)
                (fn-orln-refusalp word))
           (let* ((outcome (fn-orln-read-refusal-outcome stage word))
                  (class (fn-orln-read-refusal-class outcome)))
             (and (member-equal outcome '(:defer-publication :defer-frame))
                  (or (and (equal outcome :defer-frame) (null class))
                      (equal (fn-fs-classify class step) :refusal)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-orln-read-refusal-outcome fn-orln-read-refusal-class
                                     fn-fs-classify))))

; KEYSTONE.  A diagnostic image with the extent cache off (limit 0) does not
; make the checkpoint walk read unfunded: the cold-read mode is the exhausted
; pool's refusal (books/page-read-executor.lisp fn-pxe-cache-mode), and the
; walk's outcome for it is the deferred publication.  With the cache on the
; mode is :ready.  A scenario that needs the checkpoint to publish therefore
; runs with the cache on (tests/test_native_owner_scheduler.py, the A6
; campaign).  Teeth (tests/acl2/owner-resource-line-tests.lisp).
(defthm fn-orln-cache-off-walk-defers-the-publication
  (and (fn-orln-refusalp (fn-pxe-cache-mode nil))
       (equal (fn-orln-read-refusal-outcome :checkpoint-walk (fn-pxe-cache-mode nil))
              :defer-publication)
       (equal (fn-pxe-cache-mode t) :ready))
  :rule-classes nil)

; And only an exhausted pool on those stages is: everything else faults.
(defthm fn-orln-read-refusal-otherwise-faults
  (implies (not (and (member-equal stage *fn-orln-read-stages*)
                     (fn-orln-refusalp word)))
           (equal (fn-orln-read-refusal-outcome stage word) :fault))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-orln-read-refusal-outcome))))
