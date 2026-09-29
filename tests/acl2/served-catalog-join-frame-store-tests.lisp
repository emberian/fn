; served-catalog-join-frame-store-tests.lisp -- teeth for books/served-
; catalog-join-frame-store.lisp (the catalog invariant across the owner steps
; that change the store but complete no article; lane sca-join-4, F-store).
;
; Two reachable owners, both through the real configured owner step
; fn-ocfg-step from an opened owner, each with the catalog the host loads
; (fn-sca-load-held-rows) from the rows the view has seen:
;
;   R: a fresh owner over groups ("fn.test"), reserved, a retention
;      undertaking prepared, and its record file, link and directory
;      observations: the store at :completing with the retention event
;      appended (no catalog row).  The catalog is empty.
;   T2: catalog-entries-tests' configured owner at :completing with an
;      ARTICLE row appended (three rows, the first two loading no row; the
;      catalog is the host's load of the first two, the rows its view has
;      seen: empty).
;
;   1. REACHABLE WITNESSES, every hypothesis and both conjuncts of the
;      conclusion evaluated (fn-scj-invp's five conjuncts each):
;      a. the store I/O keystone fn-scjs-ocfg-store-step-keeps-invp at the
;         directory's publishing observation (R before it: the history
;         grows by the candidate and enters :completing);
;      b. the prepare: the same theorem at (:store (:prepare-retention E))
;         on R's reserved owner (what fn-pout-prepare-retention installs);
;      c. the non-article completion fn-scjs-ocfg-complete-keeps-invp at R
;         (the retention event completes; the view refreshes to the
;         history's length, the catalog is untouched).
;   Each witness also evaluates fn-scjs-versionsp before and after.
;   2. HYPOTHESIS REMOVAL, JOINTLY (the two no-row hypotheses of the
;      completion are one fact in a reachable owner: the unseen history IS
;      the completing record): T2's article completion through the model's
;      fn-ocfg-complete.  Every retained hypothesis holds, both no-row
;      hypotheses fail, and the conclusion fails: the refreshed view shows
;      the article while the catalog does not (the join and the rows
;      invariant false, and the live view is no longer over the catalog).  This is why the host routes an article completion
;      through the catalog's own finish (step 2).

(in-package "ACL2")

(include-book "catalog-entries-tests")
(include-book "../../books/served-catalog-join-frame-store")

(defun scjs-rows-of (i fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (< i (fn-cat-count fn-cat))
      (cons (fn-cat-at i fn-cat) (scjs-rows-of (+ 1 i) fn-cat))
    nil))

; fn-scj-rows-invp's body.
(defun scjs-rows-invp (c events)
  (declare (xargs :mode :program))
  (equal (fn-scj-arts-map c)
         (fn-scj-arts-map (with-local-stobj fn-cat
                            (mv-let (r fn-cat)
                              (let ((fn-cat (fn-sca-load-held-rows-from events nil fn-cat)))
                                (mv (scjs-rows-of 0 fn-cat) fn-cat))
                              r)))))

; fn-scr-catalogp's body at a pin's fields (fn-scr-fields-catalogp).
(defun scjs-fields-okp (archive index buckets control version fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((c (scjs-rows-of 0 fn-cat))
         (pidx (if buckets (fn-gidx-pin-with-control index buckets control) index))
         (v (fn-scr-view-of version fn-cat)))
    (and (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
         (fn-statep archive)
         (fn-gidx-pin-correspondencep pidx archive)
         (fn-midx-correspondencep (fn-gidx-pin-trie pidx) (fn-state-articles archive))
         (fn-cnx-freshp c)
         t)))

(defun scjs-conns-okp (conns fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (consp conns)
      (and (scjs-fields-okp (fn-own-conn-archive (car conns)) (fn-own-conn-index (car conns))
                            (fn-own-conn-group-index (car conns)) (fn-own-conn-control (car conns))
                            (fn-own-conn-version (car conns)) fn-arena fn-cat)
           (scjs-conns-okp (cdr conns) fn-arena fn-cat))
    t))

; fn-scj-invp's five conjuncts over live stobjs.
(defun scjs-invp (o fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((view (fn-own-view o))
         (s (fn-own-store o))
         (c (scjs-rows-of 0 fn-cat)))
    (list (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                      (fn-state-articles (fn-own-view-archive view)))
               (fn-scj-marks-below c (fn-cat-count fn-cat))
               (fn-scj-seqs-below c (fn-own-view-version view))
               t)
          (scjs-rows-invp c (fn-own-take (fn-own-view-version view)
                                         (fn-sf-records (fn-sn-files s))))
          (and (equal (fn-own-view-raw view)
                      (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
               (equal (fn-own-view-verdicts view) (fn-sn-verdicts s)))
          (scjs-fields-okp (fn-own-view-archive view) (fn-own-view-index view)
                           (fn-own-view-group-index view) (fn-own-view-control view)
                           (fn-own-view-version view) fn-arena fn-cat)
          (scjs-conns-okp (fn-own-conns o) fn-arena fn-cat))))

; fn-scjs-seenp's and fn-scjs-historyp's bodies.
(defun scjs-seenp (o)
  (declare (xargs :mode :program))
  (let* ((files (fn-sn-files (fn-own-store o)))
         (r (if (equal (fn-sf-phase files) :completing)
                (butlast (fn-sf-records files) 1)
              (fn-sf-records files)))
         (v (fn-own-view-version (fn-own-view o))))
    (and (<= v (len r)) (fn-scj-no-rowsp (nthcdr v r)))))

; fn-scjs-versionsp's body.
(defun scjs-versionsp (o)
  (declare (xargs :mode :program))
  (fn-scj-conns-versions-atmostp (fn-own-conns o) (fn-own-view-version (fn-own-view o))))

(defun scjs-historyp (o)
  (declare (xargs :mode :program))
  (let ((v (fn-own-view-version (fn-own-view o)))
        (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
    (and (natp v) (<= v (len records)) (true-listp records))))

(defun scjs-run-events (oc events fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (consp events)
      (scjs-run-events (fn-ocfg-step oc (car events) fn-arena) (cdr events) fn-arena)
    oc))

;; ARM: (:store EV) the configured (:store EV) event; :complete the
;; configured completion fn-ocfg-complete.  NCAT: the catalog is the load of
;; the first NCAT rows.  Answers (HYPS CONCLUSION (view count before, after)
;; catalog count).
(defun scjs-run (oc payloads arm ncat fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (view (fn-own-view o))
         (records (fn-sf-records (fn-sn-files s)))
         (fn-cat (fn-sca-load-held-rows (take ncat records) (fn-own-view-index view) fn-arena fn-cat))
         (oc2 (if (equal arm :complete)
                  (fn-ocfg-complete oc)
                (fn-ocfg-step oc arm fn-arena)))
         (o2 (fn-ocfg-owner oc2))
         (inv (scjs-invp o fn-arena fn-cat))
         (common (list (equal inv '(t t t t t))
                       (if (scjs-seenp o) t nil)
                       (if (fn-scar-view-indexedp o) t nil)
                       (if (scjs-historyp o) t nil)
                       (if (fn-statep (fn-own-view-archive (fn-own-view o2))) t nil)
                       (if (scjs-versionsp o) t nil)))
         (arm-hyps (if (equal arm :complete)
                       (list (not (fn-ocfg-staged oc))
                             (not (fn-scj-load-h (fn-sn-completion-record s)))
                             (fn-scj-no-rowsp (nthcdr (fn-own-view-version view) records)))
                     (list (not (member-equal (car (cadr arm)) '(:finish :crash :recover)))))))
    (mv (list (append common arm-hyps)
              (list (scjs-invp o2 fn-arena fn-cat) (if (scjs-seenp o2) t nil)
                    (if (scjs-versionsp o2) t nil))
              (list (len (fn-state-articles (fn-own-view-archive view)))
                    (len (fn-state-articles (fn-own-view-archive (fn-own-view o2)))))
              (fn-cat-count fn-cat))
        fn-arena fn-cat)))

(defun scjs-exec (oc payloads arm ncat)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scjs-run oc payloads arm ncat fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defun scjs-events-exec (oc events)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (mv (scjs-run-events oc events fn-arena) fn-arena)
      r)))

; -----------------------------------------------------------------------------
; R: a fresh configured owner (owner-retention-preparation-tests' setup).

(defconst *scjs-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))
(defconst *scjs-post-config*
  (fn-inj-make-config
   t '(102 110 46 111 112 114 46 105 110 118 97 108 105 100)
   (list '(102 110 46 116 101 115 116)) 32768))
(defconst *scjs-r0*
  (fn-ocfg-make (fn-own-configure (fn-own-start (fn-sn-initial '("fn.test") 10) 2)
                                  *scjs-post-config*)
                *scjs-config* nil nil))
(defconst *scjs-r-reserved*
  (scjs-events-exec *scjs-r0* '((:store (:io :start-frontier nil))
                                (:store (:io :frontier-file :ok))
                                (:store (:io :frontier-replace :ok))
                                (:store (:io :frontier-directory :ok)))))
(defconst *scjs-r-event*
  (let* ((s (fn-own-store (fn-ocfg-owner *scjs-r-reserved*)))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (fn-store-retention-event-make
     :undertake (fn-sn-identity-next s) txid txid
     (fn-record-octets-string '(111 98 108))
     (fn-record-octets-string '(115 117 98))
     (fn-record-octets-string '(101 118 105)) 1)))
(defconst *scjs-r-prepare* (list :store (list :prepare-retention *scjs-r-event*)))
(defconst *scjs-r-attempted*
  (scjs-events-exec *scjs-r-reserved* (list *scjs-r-prepare*
                                            '(:store (:io :record-file :ok))
                                            '(:store (:io :record-link :ok)))))
(defconst *scjs-r-dir* '(:store (:io :record-directory :ok)))
(defconst *scjs-r-completing* (scjs-events-exec *scjs-r-attempted* (list *scjs-r-dir*)))

(defun scjs-phase (oc)
  (declare (xargs :mode :program))
  (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
(defun scjs-nrecords (oc)
  (declare (xargs :mode :program))
  (len (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))

(assert-event (equal (scjs-phase *scjs-r-reserved*) :reserved))
(assert-event (equal (scjs-phase *scjs-r-attempted*) :record-attempted))
(assert-event (equal (scjs-phase *scjs-r-completing*) :completing))
(assert-event (equal (list (scjs-nrecords *scjs-r-attempted*) (scjs-nrecords *scjs-r-completing*))
                     '(0 1)))

(defconst *scjs-store-all* (make-list 7 :initial-element t))
(defconst *scjs-complete-all* (make-list 9 :initial-element t))
(defconst *scjs-concl* '((t t t t t) t t))

; 1a. The store I/O keystone at the directory's publishing observation: every
; hypothesis, both conjuncts; the history grows by the candidate (0 to 1),
; the store enters :completing, the view and the empty catalog stay.
(assert-event (equal (scjs-exec *scjs-r-attempted* nil *scjs-r-dir* 0)
                     (list *scjs-store-all* *scjs-concl* '(0 0) 0)))

; 1b. The prepare at the reservation (fn-pout-prepare-retention's owner).
(assert-event (equal (scjs-exec *scjs-r-reserved* nil *scjs-r-prepare* 0)
                     (list *scjs-store-all* *scjs-concl* '(0 0) 0)))
(assert-event (equal (scjs-phase (scjs-events-exec *scjs-r-reserved* (list *scjs-r-prepare*)))
                     :record-staged))

; 1c. The non-article completion: the retention event completes, the store
; returns to :ready, the view refreshes (its version becomes the history's
; length, 1) and the empty catalog is untouched.
(assert-event (equal (scjs-exec *scjs-r-completing* nil :complete 0)
                     (list *scjs-complete-all* *scjs-concl* '(0 0) 0)))
(assert-event (let ((o2 (fn-ocfg-owner (fn-ocfg-complete *scjs-r-completing*))))
                (and (equal (fn-sf-phase (fn-sn-files (fn-own-store o2))) :ready)
                     (equal (fn-own-view-version (fn-own-view o2)) 1)
                     (fn-store-retention-event-p
                      (car (fn-sf-records (fn-sn-files (fn-own-store o2))))))))

; 2. Hypothesis removal, JOINTLY (the completing record loads a row, and so
; the unseen history does): T2's article completion.  Every retained
; hypothesis holds (the first six); both no-row hypotheses fail; the
; conclusion fails in the join, the rows invariant and the live view (VV
; and the pinned connections still hold): the view goes from no article to
; one, the catalog stays empty.
(assert-event (equal (scjs-exec *cet-t2-oc* *cet-t2-payloads* :complete 2)
                     (list (list t t t t t t t nil nil)
                           '((nil nil t nil t) t t) '(0 1) 0)))

; -----------------------------------------------------------------------------
; 3. REACHABLE WITNESS of fn-scjs-rows-invp-before-in-flight at both
; :completing owners: the antecedent (invariant, seen fact, history facts,
; :completing) and the conclusion (the version within the history less the
; in-flight record; the rows invariant over it), with that history's length
; and the version.

(defun scjs-inflight-run (oc payloads ncat fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (view (fn-own-view o))
         (records (fn-sf-records (fn-sn-files s)))
         (b (butlast records 1))
         (v (fn-own-view-version view))
         (fn-cat (fn-sca-load-held-rows (take ncat records) (fn-own-view-index view) fn-arena fn-cat)))
    (mv (list (list (equal (scjs-invp o fn-arena fn-cat) '(t t t t t))
                    (if (scjs-seenp o) t nil)
                    (if (scjs-historyp o) t nil)
                    (equal (fn-sf-phase (fn-sn-files s)) :completing))
              (list (<= v (len b)) (scjs-rows-invp (scjs-rows-of 0 fn-cat) b))
              (len b) v)
        fn-arena fn-cat)))

(defun scjs-inflight-exec (oc payloads ncat)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scjs-inflight-run oc payloads ncat fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event (equal (scjs-inflight-exec *scjs-r-completing* nil 0)
                     '((t t t t) (t t) 0 0)))
(assert-event (equal (scjs-inflight-exec *cet-t2-oc* *cet-t2-payloads* 2)
                     '((t t t t) (t t) 2 2)))
