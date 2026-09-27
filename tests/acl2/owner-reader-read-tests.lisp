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
(include-book "std/testing/must-fail" :dir :system)

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
  (implies (fn-scr-owner-catalogp (fn-ocfg-owner (if (consp views)
                                                     (fn-ocfg-at-reader-view oc views)
                                                   oc))
                                  id fn-arena fn-cat)
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
(must-fail
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
; (failed proof search with its hints, not a counterexample).
(must-fail
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
