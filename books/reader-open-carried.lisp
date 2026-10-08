;; fn: the reader's connection open with the selected archive's invariant carried.
;
; host/reader-host.lisp is the shared-lock NNTP reader (host/native/io.lisp
; `fnn-reader-prepare' selects the archive once per process, then
; `fnn-serve-client' opens every connection with `fn-reader-reset').  The
; reference open, `fn-served-open' (books/served.lisp), evaluated per
; connection, over the archive the selection had already recognised, runs
; `fn-auth-open-session' -> `fn-peer-open-session' -> `fn-nntp-open-session',
; whose `fn-nntp-projectionp' runs `fn-statep' of the whole archive
; (the article-list recognisers and the freshness scan, N each).
;
; The selected archive is immutable for the reader's life: it holds a shared
; lock and never commits (fnn-reader-prepare's docstring).  So the selection
; is where the invariant is established, once, and the open carries it:
;
; - `fn-rdc-selection' is the selection: it checks `fn-nntp-projectionp' of
;   the archive once and records the archive and its verdicts
;   (`fn-rdc-selection-establishes');
; - `fn-rdc-reset', the function the host calls per connection
;   (host/reader-host.lisp `fn-reader-reset'), opens over the recorded archive
;   and takes the projection flag from the selection instead of recomputing it
;   (the owner's `fn-ocar-auth-open-reader', books/owner-open-carried.lisp);
; - KEYSTONE `fn-rdc-reset-is-served-open': on every selection that answered
;   :ready, the connection and greeting are the reference open's, pinned with
;   the selection's verdicts.
;
; What a connection open still evaluates: the greeting's projection flag
; without its `fn-statep' and group-list conjuncts (`fn-acar-open-session':
; the next-number table; the selection's fn-nntp-projectionp carries the
; rest; PKT-190) and the connection record.

(in-package "ACL2")
(include-book "owner-open-carried")

; The recorded selection: (:ready ARCHIVE VERDICTS), or :refused.
(defun fn-rdc-selection (archive verdicts)
  (declare (xargs :guard t))
  (if (fn-nntp-projectionp archive)
      (list :ready archive verdicts)
    :refused))

(defun fn-rdc-readyp (sel)
  (declare (xargs :guard t))
  (and (true-listp sel) (equal (len sel) 3) (eq (car sel) :ready)))

(defun fn-rdc-archive (sel)
  (declare (xargs :guard t))
  (if (fn-rdc-readyp sel) (cadr sel) nil))

(defun fn-rdc-verdicts (sel)
  (declare (xargs :guard t))
  (if (fn-rdc-readyp sel) (caddr sel) nil))

; The Store selection the host makes once per process: the whole-store
; recogniser, then the archive's projection check, both once.
(defun fn-rdc-store-selection (store)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sn-statep store)
      (fn-rdc-selection (fn-node-acceptance (fn-sn-node store))
                        (fn-sn-verdicts store))
    :refused))

(verify-guards fn-rdc-store-selection)

; The projection recogniser's first conjunct is the acceptance-state one.
(defthm fn-rdc-projection-is-a-state
  (implies (fn-nntp-projectionp archive)
           (fn-statep archive))
  :hints (("Goal" :in-theory (e/d (fn-nntp-projectionp) (fn-statep)))))

; The relation the reader carries from its selection to every connection.
(defthm fn-rdc-selection-establishes
  (implies (fn-rdc-readyp (fn-rdc-selection archive verdicts))
           (and (fn-nntp-projectionp (fn-rdc-archive (fn-rdc-selection archive verdicts)))
                (fn-statep (fn-rdc-archive (fn-rdc-selection archive verdicts)))
                (equal (fn-rdc-archive (fn-rdc-selection archive verdicts)) archive)
                (equal (fn-rdc-verdicts (fn-rdc-selection archive verdicts)) verdicts)))
  :hints (("Goal" :in-theory (disable fn-statep))))

(defthm fn-rdc-selection-ready-iff-projectable
  (iff (fn-rdc-readyp (fn-rdc-selection archive verdicts))
       (fn-nntp-projectionp archive))
  :hints (("Goal" :in-theory (disable fn-nntp-projectionp))))

; The carried open: `fn-served-open-indexed' with the reader session built by
; `fn-ocar-auth-open-reader'.
(defun fn-rdc-served-open (archive line-limit body-limit config
                                   observation injection acfg)
  (declare (xargs :guard t))
  (let ((session (fn-ocar-auth-open-reader archive acfg)))
    (fn-served-make-result
     (fn-served-make-conn-indexed
      (fn-wire-initial-state line-limit body-limit)
      session archive config observation injection nil)
     (list (fn-nntp-reply-effect (fn-served-greeting config session))))))

(defthm fn-rdc-served-open-is-served-open
  (implies (and (fn-statep archive)
                (fn-nntp-safe-group-listp (fn-state-groups archive)))
           (equal (fn-rdc-served-open archive line-limit body-limit
                                      config observation injection acfg)
                  (fn-served-open archive line-limit body-limit config
                                  observation injection acfg)))
  :hints (("Goal" :use ((:instance fn-ocar-auth-open-reader-is-auth-open-session))
           :in-theory (e/d (fn-served-open fn-served-open-indexed)
                           (fn-ocar-auth-open-reader fn-auth-open-session
                            fn-ocar-auth-open-reader-is-auth-open-session
                            fn-statep fn-nntp-safe-group-listp
                            fn-served-greeting)))))

;; The subject host/reader-host.lisp `fn-reader-reset' calls, per connection.
; It has no arm for a selection that did not answer :ready: no host reaches
; one (host/native/io.lisp `fnn-reader-select' refuses the process and
; tools/run_reader.py raises before any connection is opened), so the former
; reference open over no archive is gone rather than kept as an unreachable
; arm.
(defun fn-rdc-reset (sel line-limit body-limit config observation injection
                         acfg)
  (declare (xargs :guard t))
  (fn-served-pin-verdicts
   (fn-rdc-served-open (fn-rdc-archive sel)
                       line-limit body-limit config observation injection
                       acfg)
   (fn-rdc-verdicts sel)))

; KEYSTONE.  Every connection the reader opens over a selection that answered
; :ready is the reference open of the selected archive, pinned with the
; selection's verdicts.
(defthm fn-rdc-reset-is-served-open
  (implies (fn-rdc-readyp (fn-rdc-selection archive verdicts))
           (equal (fn-rdc-reset (fn-rdc-selection archive verdicts)
                                line-limit body-limit config observation
                                injection acfg)
                  (fn-served-pin-verdicts
                   (fn-served-open archive line-limit body-limit config
                                   observation injection acfg)
                   verdicts)))
  :hints (("Goal" :use ((:instance fn-rdc-selection-establishes))
           :in-theory (e/d ()
                           (fn-rdc-selection fn-rdc-readyp fn-rdc-archive
                            fn-rdc-verdicts
                            fn-rdc-selection-establishes
                            fn-statep fn-nntp-projectionp
                            fn-served-open fn-served-pin-verdicts)))))

; The Store selection is the archive selection of the recognised store.
(defthm fn-rdc-store-selection-unfolds
  (equal (fn-rdc-store-selection store)
         (if (fn-sn-statep store)
             (fn-rdc-selection (fn-node-acceptance (fn-sn-node store))
                               (fn-sn-verdicts store))
           :refused)))
