; Witnesses and teeth for books/owner-reader-read.lisp (lane scheduler-3,
; 2026-09-27; PKT-828).
;
; The owners are owner-log-ocl-tests': *lgt-oc0* (the recovered configured
; owner, a reader open, 2 records) is the owner at the capture, and
; *lgt-finished* (the same owner after the log route committed one POST to
; fn.letters, 3 records) the working owner a reader reads during the barrier.
; The configuration witnesses are config-owner-publish-tests': *ocp-closed*
; before, *ocp-new* after a publication that created fn.live.
(in-package "ACL2")
(include-book "../../books/owner-reader-read")
(include-book "owner-log-ocl-tests")
(include-book "arena-lift")
(include-book "must-fail-checked")

(assert-event
 (equal (list (symbol-class 'fn-orr-read-span (w state))
              (symbol-class 'fn-ocs-publication-class (w state)))
        '(:common-lisp-compliant :common-lisp-compliant)))

; The catalog premise of the keystone (fn-scr-owner-catalogp, a defun-nx:
; not executable) is not built on ground values here.  Under it the host's
; call is the same composition over the carried read without the catalog
; (books/served-catalog-chain.lisp fn-scr-ocfg-read-span-is-scar-ocfg-read-
; span), so the witnesses run that twin, tied to fn-orr-read-span by the
; theorem below; the premise's removal is the must-fail further down.
(defun orrt-read-span-scar (oc views id i end fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
  (if (consp views)
      (let ((result (fn-scar-ocfg-read-span (fn-ocfg-at-reader-view oc views)
                                            id i end fn-octets fn-arena)))
        (fn-own-tls-make-result
         (fn-own-tls-result-consumed result)
         (fn-own-tls-result-effects result)
         (fn-ocfg-with-view (fn-own-tls-result-owner result)
                            (fn-own-view (fn-ocfg-owner oc)))
         (fn-own-tls-result-repinned result)))
    (fn-scar-ocfg-read-span oc id i end fn-octets fn-arena)))

(defthm orrt-the-host-read-is-the-twin-under-the-catalog
  (implies (and (fn-scr-owner-catalogp (fn-ocfg-owner (if (consp views)
                                                          (fn-ocfg-at-reader-view oc views)
                                                        oc))
                                       id fn-arena fn-cat)
                (fn-scol-okp fn-arena fn-cat))
           (equal (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)
                  (orrt-read-span-scar oc views id i end fn-octets fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-orr-read-span fn-scr-ocfg-read-span-is-scar-ocfg-read-span)
                                  (fn-scr-owner-catalogp fn-ocfg-at-reader-view)))))

; The call on ground octets: the buffer filled as fnn-octets-fill fills it,
; the whole region read (i 0, end its length), an empty sealed arena.
(defun orrt-span (oc views id octs fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let ((fn-octets (fn-octets-from-list octs fn-octets)))
    (mv (with-local-stobj fn-arena
          (mv-let (r fn-arena)
            (let ((fn-arena (fn-arn-seal-many nil fn-arena)))
              (mv (orrt-read-span-scar oc views id 0 (len octs) fn-octets fn-arena) fn-arena))
            r))
        fn-octets)))
(defun orrt (oc views id octs)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets) (orrt-span oc views id octs fn-octets) r)))
(defconst *orrt-arena* nil)
(bpr-lift fn-ocfg-read 3)

(defun orrt-records (oc) (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
(defun orrt-history (oc) (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
(defun orrt-view (oc) (fn-own-view (fn-ocfg-owner oc)))

; The keystone's hypotheses, and its conclusion, over ground values.
(defun orrt-hyps (views oc0 oc octs)
  (declare (xargs :verify-guards nil))
  (and (consp views)
       (equal (car views) (orrt-view oc0))
       (fn-ocri-relation oc0)
       (fn-ocri-relation oc)
       (equal (orrt-records oc)
              (append (orrt-records oc0)
                      (nthcdr (len (orrt-records oc0)) (orrt-records oc))))
       (equal (orrt-history oc) (orrt-history oc0))
       (equal (fn-ocfg-config oc) (fn-ocfg-config oc0))
       (true-listp octs)))

(defun orrt-concl (views oc id octs)
  (declare (xargs :verify-guards nil))
  (let* ((r (orrt oc views id octs))
         (oc2 (fn-own-tls-result-owner r))
         (o2 (fn-ocfg-owner oc2))
         (o (fn-ocfg-owner oc)))
    (and (fn-ocri-relation oc2)
         (equal (fn-own-view o2) (fn-own-view o))
         (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-next-id o2) (fn-own-next-id o))
         (equal (fn-own-max-conns o2) (fn-own-max-conns o))
         (equal (fn-own-pending o2) (fn-own-pending o))
         (equal (fn-own-ledger o2) (fn-own-ledger o))
         (equal (fn-own-clock o2) (fn-own-clock o))
         (equal (fn-own-facts o2) (fn-own-facts o))
         (equal (fn-ocfg-config oc2) (fn-ocfg-config oc))
         (equal (fn-ocfg-staged oc2) (fn-ocfg-staged oc))
         (equal (fn-own-tls-result-effects r)
                (car (in-arena-fn-ocfg-read *orrt-arena* (fn-ocfg-with-view oc (car views)) id
                                            (take (fn-own-tls-result-consumed r) octs)))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-orr-read-span-at-a-captured-view-restores-the-owner.
; Reachable positive witness: the capture before the POST's batch, the
; working owner after it; a reader on connection 0 sends GROUP fn.letters.
(defconst *orrt-group* (append (fn-nntp-string-octets "GROUP fn.letters") '(13 10)))
(defconst *orrt-views* (list (orrt-view *lgt-oc0*)))
(assert-event (orrt-hyps *orrt-views* *lgt-oc0* *lgt-finished* *orrt-group*))
; Non-degenerate: the Store grew by the POST's record, the views differ.
(assert-event (and (equal (len (orrt-records *lgt-oc0*)) 2)
                   (equal (len (orrt-records *lgt-finished*)) 3)
                   (not (equal (orrt-view *lgt-oc0*) (orrt-view *lgt-finished*)))))
(assert-event (orrt-concl *orrt-views* *lgt-finished* 0 *orrt-group*))
(defconst *orrt-r* (orrt *lgt-finished* *orrt-views* 0 *orrt-group*))
(defconst *orrt-w* (orrt *lgt-finished* nil 0 *orrt-group*))
; The reader reads the durable view: 211 0 (the POST's article is not
; counted during the barrier); with no capture held the same read answers
; 211 1 (the working view).
(assert-event (equal (fn-own-tls-result-effects *orrt-r*)
                     (list (list :reply (append (fn-nntp-string-octets "211 0 1 0 fn.letters")
                                                '(13 10))))))
(assert-event (equal (fn-own-tls-result-effects *orrt-w*)
                     (list (list :reply (append (fn-nntp-string-octets "211 1 1 1 fn.letters")
                                                '(13 10))))))
; The entry changed the reader's connection (its selection) and put the
; working view back.
(assert-event (not (equal (fn-own-conns (fn-ocfg-owner (fn-own-tls-result-owner *orrt-r*)))
                          (fn-own-conns (fn-ocfg-owner *lgt-finished*)))))

; Hypothesis removal.  Each witness checks the retained hypotheses, the
; failure of the omitted one, and the failure of the conclusion.
(defun orrt-mislabel (v version) (cons version (cdr v)))
; A view that is not the capture's: the working view relabelled with the
; capture's version (the archive of 3 records claims to be the replay of 2).
(defconst *orrt-bad-view*
  (orrt-mislabel (orrt-view *lgt-finished*) (fn-own-view-version (orrt-view *lgt-oc0*))))
(assert-event (not (equal *orrt-bad-view* (orrt-view *lgt-oc0*))))

; Without (equal (car views) (fn-own-view (fn-ocfg-owner oc0))).
(assert-event (and (fn-ocri-relation *lgt-oc0*) (fn-ocri-relation *lgt-finished*)
                   (equal (orrt-history *lgt-finished*) (orrt-history *lgt-oc0*))
                   (equal (fn-ocfg-config *lgt-finished*) (fn-ocfg-config *lgt-oc0*))
                   (not (equal (car (list *orrt-bad-view*)) (orrt-view *lgt-oc0*)))
                   (not (orrt-concl (list *orrt-bad-view*) *lgt-finished* 0 *orrt-group*))))

; Without (fn-ocri-relation oc0): the capture's owner carries the bad view.
(defconst *orrt-bad-oc0* (fn-ocfg-with-view *lgt-oc0* *orrt-bad-view*))
(assert-event (and (not (fn-ocri-relation *orrt-bad-oc0*))
                   (equal (car (list *orrt-bad-view*)) (orrt-view *orrt-bad-oc0*))
                   (fn-ocri-relation *lgt-finished*)
                   (equal (orrt-history *lgt-finished*) (orrt-history *orrt-bad-oc0*))
                   (equal (fn-ocfg-config *lgt-finished*) (fn-ocfg-config *orrt-bad-oc0*))
                   (not (orrt-concl (list *orrt-bad-view*) *lgt-finished* 0 *orrt-group*))))

; Without (fn-ocri-relation oc): the working owner carries the bad view, and
; restoring it restores the fault.
(defconst *orrt-bad-oc* (fn-ocfg-with-view *lgt-finished* *orrt-bad-view*))
(assert-event (and (not (fn-ocri-relation *orrt-bad-oc*))
                   (fn-ocri-relation *lgt-oc0*)
                   (equal (orrt-history *orrt-bad-oc*) (orrt-history *lgt-oc0*))
                   (equal (fn-ocfg-config *orrt-bad-oc*) (fn-ocfg-config *lgt-oc0*))
                   (not (orrt-concl *orrt-views* *orrt-bad-oc* 0 *orrt-group*))))

; Without the append: the roles swapped, a capture of 3 records read over a
; Store of 2.
(defconst *orrt-later-views* (list (orrt-view *lgt-finished*)))
(assert-event (and (fn-ocri-relation *lgt-finished*) (fn-ocri-relation *lgt-oc0*)
                   (not (equal (take 3 (orrt-records *lgt-oc0*)) (orrt-records *lgt-finished*)))
                   (not (equal (orrt-records *lgt-oc0*)
                               (append (orrt-records *lgt-finished*)
                                       (nthcdr 3 (orrt-records *lgt-oc0*)))))
                   (equal (orrt-history *lgt-oc0*) (orrt-history *lgt-finished*))
                   (equal (fn-ocfg-config *lgt-oc0*) (fn-ocfg-config *lgt-finished*))
                   (not (orrt-concl *orrt-later-views* *lgt-oc0* 0 *orrt-group*))))

; Without the configuration history and the configuration (the witness of
; books/owner-reader-read.lisp's second keystone): a publication between the
; capture and the read.  *ocp-closed* before it, *ocp-new* after (fn.live
; created; the same records).  A GROUP on the new connection 2 at the old
; view repins it to the new configuration with the old view's archive: the
; owner is no longer related.
(defconst *orrt-test-group* (append (fn-nntp-string-octets "GROUP fn.test") '(13 10)))
(defconst *orrt-old-views* (list (orrt-view *ocp-closed*)))
(assert-event (and (fn-ocri-relation *ocp-closed*) (fn-ocri-relation *ocp-new*)
                   (equal (orrt-records *ocp-new*) (orrt-records *ocp-closed*))
                   (not (equal (orrt-history *ocp-new*) (orrt-history *ocp-closed*)))
                   (not (equal (fn-ocfg-config *ocp-new*) (fn-ocfg-config *ocp-closed*)))
                   (fn-own-find-conn 2 (fn-own-conns (fn-ocfg-owner *ocp-new*)))
                   (not (orrt-concl *orrt-old-views* *ocp-new* 2 *orrt-test-group*))))
; The same read at the working view keeps the relation.
(assert-event (fn-ocri-relation
               (fn-own-tls-result-owner (orrt *ocp-new* nil 2 *orrt-test-group*))))

; The configuration alone (the history kept) cannot be dropped separately on
; ground owners here (a related owner's configuration is its history's
; replay); the keystone's own proof does not go through without it (failed
; proof search with the keystone's hints, not a counterexample).
(must-fail-checked
 (defthm orrt-needs-the-configuration
   (implies (and (consp views)
                 (equal (car views) (fn-own-view (fn-ocfg-owner oc0)))
                 (fn-ocri-relation oc0)
                 (fn-ocri-relation oc)
                 (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                        (append (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))
                                extra))
                 (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                        (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0))))
                 (fn-scr-owner-catalogp (fn-ocfg-owner (fn-ocfg-with-view oc (car views)))
                                        id fn-arena fn-cat)
                 (fn-scol-okp fn-arena fn-cat)
                 (natp i) (natp end))
            (fn-ocri-relation
             (fn-own-tls-result-owner (fn-orr-read-span oc views id i end fn-octets fn-arena
                                                        fn-cat))))
   :hints (("Goal" :use ((:instance fn-orr-reader-relation-at-a-captured-view)
                         (:instance fn-orr-span-read-keeps-the-reader-relation-and-the-rest
                                    (x (fn-ocfg-with-view oc (car views))))
                         (:instance fn-orr-restoring-the-working-view-keeps-the-reader-relation
                                    (x2 (fn-own-tls-result-owner
                                         (fn-scr-ocfg-read-span (fn-ocfg-with-view oc (car views))
                                                                id i end fn-octets fn-arena fn-cat)))))
            :in-theory (union-theories '(fn-orr-read-span fn-ocfg-at-reader-view fn-ocv-reader-view
                                         fn-orr-tls-result-of-make fn-orr-with-view-fields)
                                       (theory 'minimal-theory))))))

; Without the catalog premise the keystone's own proof does not go through
; (failed proof search with its hints, not a counterexample).  The
; counterexample is at the end of this book (g12b-orr-catalog-premise-fails-
; on-a-stale-catalog: a stale catalog, the host's read answering 211 1).
(must-fail-checked
 (defthm orrt-needs-the-catalog
   (implies (and (consp views)
                 (equal (car views) (fn-own-view (fn-ocfg-owner oc0)))
                 (fn-ocri-relation oc0)
                 (fn-ocri-relation oc)
                 (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                        (append (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))
                                extra))
                 (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                        (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0))))
                 (equal (fn-ocfg-config oc) (fn-ocfg-config oc0))
                 (natp i) (natp end))
            (fn-ocri-relation
             (fn-own-tls-result-owner (fn-orr-read-span oc views id i end fn-octets fn-arena
                                                        fn-cat))))
   :hints (("Goal" :use ((:instance fn-orr-reader-relation-at-a-captured-view)
                         (:instance fn-orr-span-read-keeps-the-reader-relation-and-the-rest
                                    (x (fn-ocfg-with-view oc (car views))))
                         (:instance fn-orr-restoring-the-working-view-keeps-the-reader-relation
                                    (x2 (fn-own-tls-result-owner
                                         (fn-scr-ocfg-read-span (fn-ocfg-with-view oc (car views))
                                                                id i end fn-octets fn-arena fn-cat)))))
            :in-theory (union-theories '(fn-orr-read-span fn-ocfg-at-reader-view fn-ocv-reader-view
                                         fn-orr-tls-result-of-make fn-orr-with-view-fields)
                                       (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-ocvp-reader-view-is-at-the-current-generation.
; Positive witness, a reached run: a batch and the next, both completed, a
; publication, then a batch under the new generation.
(defconst *orrt-run* '((:start 3) (:next 2) (:complete) (:complete) (:publish) (:start 1)))
(assert-event (fn-ocvp-legal-run-p (fn-ocvp-init) *orrt-run*))
(defun orrt-gen-at (n)
  (let ((p (fn-ocvp-run (fn-ocvp-init) (take n *orrt-run*))))
    (list (cdr (fn-ocv-reader-view (fn-ocvp-views p) (cons (fn-ocvp-w p) (fn-ocvp-g p))))
          (fn-ocvp-g p) (consp (fn-ocvp-views p)))))
(assert-event (equal (orrt-gen-at 1) '(0 0 t)))
(assert-event (equal (orrt-gen-at 2) '(0 0 t)))
(assert-event (equal (orrt-gen-at 4) '(0 0 nil)))
(assert-event (equal (orrt-gen-at 5) '(1 1 nil)))
; The capture after the publication is taken under generation 1, at the
; working count 5.
(assert-event (equal (orrt-gen-at 6) '(1 1 t)))
(assert-event (equal (fn-ocvp-views (fn-ocvp-run (fn-ocvp-init) *orrt-run*)) '((5 . 1))))
; Hypothesis removal: a publication while a batch is in flight is not legal,
; and along that run the conclusion fails (the capture is at generation 0,
; the configuration at 1).
(defconst *orrt-illegal* '((:start 3) (:publish)))
(assert-event (not (fn-ocvp-legal-run-p (fn-ocvp-init) *orrt-illegal*)))
(assert-event (let ((p (fn-ocvp-run (fn-ocvp-init) *orrt-illegal*)))
                (not (equal (cdr (fn-ocv-reader-view (fn-ocvp-views p)
                                                     (cons (fn-ocvp-w p) (fn-ocvp-g p))))
                            (fn-ocvp-g p)))))

; -----------------------------------------------------------------------------
; fn-ocs-a-publication-waits-for-the-complete.  In flight (:staged) with the
; control class waiting the pick is nobody, and with a reader waiting too it
; is the reader; outside a batch the same waiting control class is picked.
(defconst *orrt-staged* (fn-ocs-make (fn-ocm-init) :staged nil))
(assert-event (fn-ocs-in-flight-p (fn-ocs-phase *orrt-staged*)))
(assert-event (equal (car (mv-list 2 (fn-ocs-next *orrt-staged* '(1 0 0 0 0 0)))) nil))
(assert-event (equal (car (mv-list 2 (fn-ocs-next *orrt-staged* '(1 1 0 0 0 0)))) :reader))
; Hypothesis removal: not in flight, and the pick is the publication's class.
(assert-event (and (not (fn-ocs-in-flight-p (fn-ocs-phase (fn-ocs-init))))
                   (equal (car (mv-list 2 (fn-ocs-next (fn-ocs-init) '(1 0 0 0 0 0))))
                          (fn-ocs-publication-class))))

; -----------------------------------------------------------------------------
; The capture lemmas the keystone above composes (keystone-audit 2026-09-27):
; books/owner-reader-view.lisp fn-ocl-relation-of-a-view-captured-before-
; appends, fn-ocl-view-historyp-of-a-view-captured-before-appends and
; fn-ocl-view-configp-of-a-view-captured-before-appends, and this book's
; fn-orr-reader-relation-at-a-captured-view, each on the reached pair above:
; OC0 = *lgt-oc0* (2 records, the capture), OC = *lgt-finished* (3 records,
; the working owner), EXTRA the POST's record.
(defconst *orrt-extra* (nthcdr 2 (orrt-records *lgt-finished*)))
(defconst *orrt-at-capture* (fn-ocfg-with-view *lgt-finished* (orrt-view *lgt-oc0*)))
; Reachable positive witness: every hypothesis of the four, and every
; conclusion.  Non-degenerate: EXTRA is one record, the view is at version 2.
(assert-event
 (and (fn-ocl-relation *lgt-oc0*) (fn-ocl-relation *lgt-finished*)
      (fn-ocri-relation *lgt-oc0*) (fn-ocri-relation *lgt-finished*)
      (fn-ocl-view-historyp (fn-ocfg-owner *lgt-oc0*))
      (fn-ocl-view-configp *lgt-oc0*)
      (equal (orrt-records *lgt-finished*) (append (orrt-records *lgt-oc0*) *orrt-extra*))
      (equal (len *orrt-extra*) 1)
      (equal (orrt-history *lgt-finished*) (orrt-history *lgt-oc0*))
      (equal (fn-ocfg-config *lgt-finished*) (fn-ocfg-config *lgt-oc0*))
      (fn-ocl-relation *orrt-at-capture*)
      (fn-ocri-relation *orrt-at-capture*)
      (equal (fn-own-view-version (orrt-view *lgt-oc0*)) 2)
      (<= (fn-own-view-version (orrt-view *lgt-oc0*)) (len (orrt-records *lgt-oc0*)))
      (fn-ocl-view-historyp (fn-own-with-view (fn-ocfg-owner *lgt-finished*)
                                              (orrt-view *lgt-oc0*)))
      (fn-ocl-view-configp *orrt-at-capture*)))
; Without the relation (history) of OC0: *orrt-bad-oc0*, whose view is the
; working view relabelled (above).  The rest hold; the conclusions fail.
(assert-event
 (and (not (fn-ocl-relation *orrt-bad-oc0*))
      (not (fn-ocri-relation *orrt-bad-oc0*))
      (not (fn-ocl-view-historyp (fn-ocfg-owner *orrt-bad-oc0*)))
      (fn-ocl-relation *lgt-finished*)
      (equal (orrt-records *lgt-finished*) (append (orrt-records *orrt-bad-oc0*) *orrt-extra*))
      (equal (orrt-history *lgt-finished*) (orrt-history *orrt-bad-oc0*))
      (equal (fn-ocfg-config *lgt-finished*) (fn-ocfg-config *orrt-bad-oc0*))
      (not (fn-ocl-relation (fn-ocfg-with-view *lgt-finished* (orrt-view *orrt-bad-oc0*))))
      (not (fn-ocri-relation (fn-ocfg-with-view *lgt-finished* (orrt-view *orrt-bad-oc0*))))
      (not (fn-ocl-view-historyp (fn-own-with-view (fn-ocfg-owner *lgt-finished*)
                                                   (orrt-view *orrt-bad-oc0*))))))
; Without the append: the roles swapped (a capture of 3 records over a Store
; of 2).  Both owners are related; the conclusions fail.
(assert-event
 (and (fn-ocri-relation *lgt-finished*) (fn-ocri-relation *lgt-oc0*)
      (fn-ocl-view-historyp (fn-ocfg-owner *lgt-finished*))
      (not (equal (orrt-records *lgt-oc0*)
                  (append (orrt-records *lgt-finished*) (nthcdr 3 (orrt-records *lgt-oc0*)))))
      (equal (orrt-history *lgt-oc0*) (orrt-history *lgt-finished*))
      (not (fn-ocl-relation (fn-ocfg-with-view *lgt-oc0* (orrt-view *lgt-finished*))))
      (not (fn-ocri-relation (fn-ocfg-with-view *lgt-oc0* (orrt-view *lgt-finished*))))
      (not (fn-ocl-view-historyp (fn-own-with-view (fn-ocfg-owner *lgt-oc0*)
                                                   (orrt-view *lgt-finished*))))))
; Without the configuration history: the publication pair (*ocp-closed*,
; *ocp-new*; the same records, extra nil).  For fn-ocl-view-historyp-of-...
; this is the one hypothesis omitted; for the relation lemmas the
; configuration differs too (a related owner's configuration is its history's
; replay, so the two cannot be dropped apart on ground owners).
(assert-event
 (and (fn-ocri-relation *ocp-closed*) (fn-ocri-relation *ocp-new*)
      (fn-ocl-view-historyp (fn-ocfg-owner *ocp-closed*))
      (equal (orrt-records *ocp-new*) (append (orrt-records *ocp-closed*) nil))
      (not (equal (orrt-history *ocp-new*) (orrt-history *ocp-closed*)))
      (not (fn-ocl-relation (fn-ocfg-with-view *ocp-new* (orrt-view *ocp-closed*))))
      (not (fn-ocri-relation (fn-ocfg-with-view *ocp-new* (orrt-view *ocp-closed*))))
      (not (fn-ocl-view-historyp (fn-own-with-view (fn-ocfg-owner *ocp-new*)
                                                   (orrt-view *ocp-closed*))))))
; No tooth on these witnesses for fn-ocl-view-configp-of-a-view-captured-
; before-appends: its conclusion holds at each of the three removals above
; (the configuration read at the relabelled, swapped and pre-publication
; views is the same), recorded in planning/evidence/keystone-audit-2026-09-27.md.
(assert-event
 (and (fn-ocl-view-configp (fn-ocfg-with-view *lgt-finished* (orrt-view *orrt-bad-oc0*)))
      (fn-ocl-view-configp (fn-ocfg-with-view *lgt-oc0* (orrt-view *lgt-finished*)))
      (fn-ocl-view-configp (fn-ocfg-with-view *ocp-new* (orrt-view *ocp-closed*)))))

; -----------------------------------------------------------------------------
; Teeth for fn-ocl-view-configp-of-a-view-captured-before-appends (audit
; packet G1-5, lane audit-fixes).  Each is a CORRUPTED state: an owner whose
; configuration field is not its history's replay (no transition builds one).
; The three configuration hypotheses are separated by giving one owner a
; foreign configuration (*ocp-new*'s, which serves fn.live).
(defun orrt-with-config (oc config)
  (fn-ocfg-make (fn-ocfg-owner oc) config (fn-ocfg-pins oc) (fn-ocfg-staged oc)))
(defun orrt-configp-hyps (oc0 oc)
  (declare (xargs :verify-guards nil))
  (list (fn-ocl-view-configp oc0)
        (fn-ocl-view-historyp (fn-ocfg-owner oc0))
        (equal (orrt-records oc)
               (append (orrt-records oc0) (nthcdr (len (orrt-records oc0)) (orrt-records oc))))
        (equal (orrt-history oc) (orrt-history oc0))
        (equal (fn-ocfg-config oc) (fn-ocfg-config oc0))))
(defun orrt-configp-concl (oc0 oc)
  (declare (xargs :verify-guards nil))
  (fn-ocl-view-configp (fn-ocfg-with-view oc (orrt-view oc0))))
(defconst *orrt-foreign-config* (fn-ocfg-config *ocp-new*))
(assert-event (not (equal *orrt-foreign-config* (fn-ocfg-config *lgt-oc0*))))
; Reached pair (the positive witness above), as the list of hypotheses.
(assert-event (and (equal (orrt-configp-hyps *lgt-oc0* *lgt-finished*) '(t t t t t))
                   (orrt-configp-concl *lgt-oc0* *lgt-finished*)))
; Without (equal (fn-ocfg-config oc) (fn-ocfg-config oc0)): the working
; owner carries the foreign configuration.
(assert-event
 (and (equal (orrt-configp-hyps *lgt-oc0* (orrt-with-config *lgt-finished* *orrt-foreign-config*))
             '(t t t t nil))
      (not (orrt-configp-concl *lgt-oc0* (orrt-with-config *lgt-finished* *orrt-foreign-config*)))))
; Without (fn-ocl-view-configp oc0): both owners carry the foreign
; configuration (equal to each other, the replay of neither).
(assert-event
 (and (equal (orrt-configp-hyps (orrt-with-config *lgt-oc0* *orrt-foreign-config*)
                                (orrt-with-config *lgt-finished* *orrt-foreign-config*))
             '(nil t t t t))
      (not (orrt-configp-concl (orrt-with-config *lgt-oc0* *orrt-foreign-config*)
                               (orrt-with-config *lgt-finished* *orrt-foreign-config*)))))
; Without the equal configuration histories: the publication pair with the
; published owner's configuration field left at the pre-publication one.
(assert-event
 (and (equal (orrt-configp-hyps *ocp-closed* (orrt-with-config *ocp-new* (fn-ocfg-config *ocp-closed*)))
             '(t t t nil t))
      (not (orrt-configp-concl *ocp-closed* (orrt-with-config *ocp-new* (fn-ocfg-config *ocp-closed*))))))
; No removal witness for fn-ocl-view-historyp or the records append: on the
; reached and constructed pairs the view's prefix replays to the same
; configuration (the swapped and relabelled pairs above).

; =============================================================================
; Audit packet G1-5 (lane audit-fixes, sub-lane g12b): the keystone's catalog
; premise, evaluated.  The host's catalog is loaded as the host loads it
; (books/served-catalog-owner.lisp fn-sca-load-held-rows over the Store's
; rows), and fn-orr-read-span -- the host's own call, not the twin -- runs
; over it on live stobjs.
(include-book "../../books/served-catalog-owner")
(defun g12b-cat-rows (i n fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (if (and (natp i) (natp n) (< i n))
      (cons (fn-cat-at i fn-cat) (g12b-cat-rows (1+ i) n fn-cat))
    nil))
(defun g12b-host-read-in (oc views id octs rows payloads fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-octets (fn-octets-from-list octs fn-octets))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (fn-cat (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))
                                        fn-arena fn-cat)))
    (mv (list (fn-orr-read-span oc views id 0 (len octs) fn-octets fn-arena fn-cat)
              (fn-cat-count fn-cat)
              (g12b-cat-rows 0 (fn-cat-count fn-cat) fn-cat))
        fn-octets fn-arena fn-cat)))
(defun g12b-host-read (oc views id octs rows payloads)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (with-local-stobj fn-arena
        (mv-let (result fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (result fn-octets fn-arena fn-cat)
              (g12b-host-read-in oc views id octs rows payloads fn-octets fn-arena fn-cat)
              (mv result fn-octets fn-arena)))
          (mv result fn-octets)))
      result)))
; The arena holds the POST's bytes at the article row's handle (2), as the
; host's entry interned them; the catalog is loaded from the working Store's
; three rows (two retention events, the article: one catalog row).
(defconst *g12b-p* (fn-record-payload (own-record-wire 2 8 "<ocmt@example>")))
(defconst *g12b-payloads* (list *g12b-p* *g12b-p* *g12b-p*))
(assert-event (equal (fn-record-payload (car (last (orrt-records *lgt-finished*)))) 2))
(defconst *g12b-read*
  (g12b-host-read *lgt-finished* *orrt-views* 0 *orrt-group* (orrt-records *lgt-finished*)
                  *g12b-payloads*))

; Positive witness of fn-orr-read-span-at-a-captured-view-restores-the-owner
; with its catalog premise: the host's call over the live catalog answers
; exactly what the twin answered (so orrt-concl, asserted above for the twin,
; is the host's conclusion: the reader reads the capture, 211 0), the catalog
; holds the article, and the premise holds of the catalog's logical value
; (its rows read back through fn-cat-at) and the arena's -- decided by ACL2
; on ground terms, since fn-scr-owner-catalogp is a defun-nx.
(assert-event (and (equal (car *g12b-read*) *orrt-r*)
                   (equal (cadr *g12b-read*) 1)
                   (orrt-hyps *orrt-views* *lgt-oc0* *lgt-finished* *orrt-group*)
                   (orrt-concl *orrt-views* *lgt-finished* 0 *orrt-group*)))
(make-event
 `(defthm g12b-orr-catalog-premise-at-the-witness
    (and (fn-scr-owner-catalogp ',(fn-ocfg-owner (fn-ocfg-with-view *lgt-finished* (car *orrt-views*)))
                                0 ',*g12b-payloads* ',(caddr *g12b-read*))
         ;; the overview column's premise F, decided on the same ground state
         (fn-scol-okp ',*g12b-payloads* ',(caddr *g12b-read*)))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable fn-scr-owner-catalogp fn-scr-conn-okp fn-scr-conn-catalogp
                                       fn-scr-live-catalogp fn-scr-fields-catalogp
                                       fn-scr-catalogp fn-scol-okp fn-scol-rows-okp
                                       fn-scol-row-okp)))))

; Removal of the catalog premise (CORRUPTED catalog, not reached): the same
; owners, views and read, every other hypothesis as above; the catalog holds
; the article one cursor early (its row at sequence 0, below the capture's
; version 2), so the catalog's view at the reader's pinned version shows an
; article the captured archive does not.  The premise is false (decided by
; ACL2), and the host's read answers 211 1 where the capture answers 211 0:
; the conclusion's effects conjunct fails.
(defconst *g12b-stale-read*
  (g12b-host-read *lgt-finished* *orrt-views* 0 *orrt-group*
                  (list (own-record 0 8 "<ocmt@example>")) (list *g12b-p*)))
(make-event
 `(defthm g12b-orr-catalog-premise-fails-on-a-stale-catalog
    (not (fn-scr-owner-catalogp ',(fn-ocfg-owner (fn-ocfg-with-view *lgt-finished* (car *orrt-views*)))
                                0 ',(list *g12b-p*) ',(caddr *g12b-stale-read*)))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable fn-scr-owner-catalogp fn-scr-conn-okp fn-scr-conn-catalogp
                                       fn-scr-live-catalogp fn-scr-fields-catalogp
                                       fn-scr-catalogp)))))
(assert-event
 (let ((r (car *g12b-stale-read*)))
   (and (orrt-hyps *orrt-views* *lgt-oc0* *lgt-finished* *orrt-group*)
        (equal (fn-own-view-version (car *orrt-views*)) 2)
        (equal (fn-own-tls-result-effects r)
               (list (list :reply (append (fn-nntp-string-octets "211 1 1 1 fn.letters")
                                          '(13 10)))))
        (not (equal (fn-own-tls-result-effects r)
                    (car (in-arena-fn-ocfg-read *orrt-arena*
                                                (fn-ocfg-with-view *lgt-finished* (car *orrt-views*)) 0
                                                (take (fn-own-tls-result-consumed r) *orrt-group*))))))))
