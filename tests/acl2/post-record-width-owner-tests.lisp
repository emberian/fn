; Teeth for books/post-record-width-owner.lisp (PKT-250): the keystone
; fn-prwo-owner-post-record-is-within-r over the owner's two host calls.
(in-package "ACL2")
(include-book "post-prepare-catalog-tests")
(include-book "../../books/post-record-width-owner")
(include-book "must-fail-checked")

; The owner is post-prepare-catalog-tests' *pit-oc* (two articles, the Store
; :reserved); the record is the one host/owner-host.lisp
; `fn-owner-prepare-buffer' builds for a fresh Message-ID over that Store
; (`fn-sn-article-record' at the owner's clock), interned at the arena's next
; handle 2 by `fn-apc-intern-row-at' under the empty parse carry; the
; catalog is recovery's load of the Store's history (ppct-run's), the budget
; and retain carry ppct-run's.  The boundary is asked of a scale profile, its
; carried verdict and the paged table's key (post-admission-keyed-tests').

(defconst *prwot-profile* (fn-bs-config-for-profile :scale))
(defconst *prwot-key*
  (fn-mpxt-key-of-entry (fn-ns-create-entry '(112 97 107) (make-list 32 :initial-element 9))))
(defconst *prwot-s* (fn-own-store (fn-ocfg-owner *pit-oc*)))
(defconst *prwot-obs* (fn-clock-observation 1 841000000000 0 t))
(defconst *prwot-payload* (fn-own-sub-octets *osi-sub*))
(defconst *prwot-groups* '("fn.letters"))
(defconst *prwot-msgid-octets* (fn-record-string-octets *pit-fresh*))

(defun prwot-record (s obs payload charge)
  (fn-sn-article-record s obs *pit-fresh* payload *prwot-groups*
                        "own-pin:pit" "own-content:pit" "own-release:pit" charge))

; The host interns over the prepare's own Store (*prwot-s*).
(defun prwot-row (s obs payload charge)
  (fn-apc-intern-row-at (prwot-record s obs payload charge)
                        (fn-sn-keyring *prwot-s*) (fn-sn-keyring-generation *prwot-s*)
                        2 nil))

;; The boundary's verdict and the prepare's word over the loaded catalog
;; (ppct-run's load), each asked as the host asks it.
(defun prwot-host-in (pcarry profile payload-length charge row fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((o (fn-ocfg-owner *pit-oc*))
         (fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                        (fn-own-view-index *pit-view*) fn-arena fn-cat))
         (verdict (fn-pak-post-admission pcarry profile *prwot-msgid-octets*
                                         payload-length (len *prwot-groups*) charge
                                         *prwot-key* fn-cat)))
    (mv-let (word next)
      (fn-ppc-pout-prepare-article-cat *pit-oc* row 100 (ppct-carry *pit-oc*)
                                       fn-arena fn-cat)
      (declare (ignore next))
      (mv (list verdict word) fn-arena fn-cat))))

(defun prwot-host (pcarry profile payload-length charge row)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (with-local-stobj fn-cat
        (mv-let (answer fn-arena fn-cat)
          (prwot-host-in pcarry profile payload-length charge row fn-arena fn-cat)
          (mv answer fn-arena)))
      answer)))

;; The keystone's three hypotheses and its four conclusions, each evaluated
;; (fn-prwo-owner-post-record-is-narrow-within-the-profile).
(defun prwot-literals (pcarry profile payload charge s obs)
  (declare (xargs :mode :program))
  (let ((record (prwot-record s obs payload charge)))
    (cons (fn-pvc-carryp pcarry)
          (append (prwot-host pcarry profile (len payload) charge
                              (prwot-row s obs payload charge))
                  (list (list (fn-bs-profile-admittedp profile)
                              (not (fn-record-widep record))
                              (<= (len payload)
                                  (fn-bs-profile-max-article-octets profile))
                              (<= (len *prwot-groups*)
                                  (fn-bs-profile-max-groups-per-article profile))))))))

;; 1. REACHABLE POSITIVE WITNESS: the carry is the profile's own, the
;; boundary admits the article, the host's prepare stages the record's row,
;; and every conclusion holds; so does the R corollary
;; (fn-prwo-owner-post-record-is-within-r).
(assert-event
 (equal (prwot-literals (fn-pvc-make *prwot-profile*) *prwot-profile*
                        *prwot-payload* 2 *prwot-s* *prwot-obs*)
        '(t :ok :prepared (t t t t))))
(assert-event
 (<= (len (fn-record-encode (prwot-record *prwot-s* *prwot-obs* *prwot-payload* 2)))
     (fn-bs-profile-max-record-octets *prwot-profile*)))

;; 2. HYPOTHESIS REMOVAL (fn-pvc-carryp), CORRUPTED STATE: a carry that
;; claims admission for a profile that is not admitted (its R is 1 octet).
;; The boundary reads A and G from it and admits, the prepare stages, and the
;; profile-is-admitted conclusion fails.
(defconst *prwot-unadmitted*
  (update-nth *fn-bs-pf-max-record-octets* 1 *prwot-profile*))
(assert-event
 (equal (prwot-literals (cons *prwot-unadmitted* t) *prwot-unadmitted*
                        *prwot-payload* 2 *prwot-s* *prwot-obs*)
        '(nil :ok :prepared (nil t nil nil))))

;; 3. HYPOTHESIS REMOVAL (the boundary's :ok), REACHABLE: an article one
;; octet past the profile's A.  The carry is the profile's own and the
;; prepare stages its row (it does not read the profile's A); the boundary
;; answers :payload-bound and the payload conclusion fails.
(defconst *prwot-long-payload*
  (make-list (1+ (fn-bs-profile-max-article-octets *prwot-profile*))
             :initial-element 65))
(assert-event
 (equal (prwot-literals (fn-pvc-make *prwot-profile*) *prwot-profile*
                        *prwot-long-payload* 2 *prwot-s* *prwot-obs*)
        '(t :payload-bound :prepared (t t nil t))))

;; 4. HYPOTHESIS REMOVAL (the prepare's :prepared), CORRUPTED STATE: the
;; record is built over a value that is not a Store (nil: no txid, no
;; identity sequence), so its coordinates are not u32; the prepare refuses
;; its row and the narrowness conclusion fails.  Over the owner's own Store
;; the record is narrow whatever the prepare answers (witness 1's record).
(assert-event
 (equal (prwot-literals (fn-pvc-make *prwot-profile*) *prwot-profile*
                        *prwot-payload* 2 nil *prwot-obs*)
        '(t :ok :refused (t nil t t))))
