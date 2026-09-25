;; fn: the submission's intent identity computed once, at take, and carried.
;
; fn-own-feed-intent-id (books/owner-feed.lisp) is SHA-256 of the payload
; octets, then SHA-256 of the obligation preimage: a function of the
; submission's Message-ID and octets, both fixed when fn-own-take-submission
; moves the submission into the durable path.  The reference readers in
; books/owner.lisp compute it again at each use: fn-own-submission-intent-result
; once, fn-own-submission-intent-records twice (once itself and once through
; the result), fn-own-submission-resolution-records once.  The host called the
; first two at the intent and the third at the resolution: four digests of the
; payload per POST, 17 percent of POST CPU at N = 120
; (planning/evidence/representation-2026-09-25.md).
;
; The carry is (SUB ID . PATH): the submission, its identity and its Path
; (fn-own-feed-path-of, the parse of the article the feed targets filter by;
; carried since lane carry-kind, PKT-113).  fn-icar-carry-of builds it from the
; submission fn-owner-take (host/owner-host.lisp) just took, and that is the
; host's only writer of the global that holds it.  fn-icar-carryp says the
; carry's ID is fn-own-feed-intent-id of its own submission and its PATH that
; submission's parsed Path; it does
; not mention the owner, so no owner step can falsify it, and
; fn-icar-carryp-of-carry-of discharges it for every value the writer
; produces (nil, the global's value before the first take, satisfies it too).
; A reader uses the carried ID when the carried submission is the one in
; flight (EQUAL, which is EQ on the object the take left in the owner) and
; computes the reference otherwise, so a stale carry costs a digest and
; never a wrong identity.
;
; Every reader below is its reference with the identity replaced by
; fn-icar-intent-id and is proved equal to it under fn-icar-carryp.  The host
; calls fn-icar-submission-intent (fn-owner-submission-intent, which also
; takes the result and the records in one call instead of two) and
; fn-icar-submission-resolution-records (fn-owner-submission-resolution).

(in-package "ACL2")
(include-book "owner")

; -----------------------------------------------------------------------------
; The carry.

(defun fn-icar-carry-of (sub)
  (declare (xargs :guard t))
  (list* sub
         (fn-own-feed-intent-id (fn-own-sub-msgid sub) (fn-own-sub-octets sub))
         (fn-own-feed-path-of (fn-own-sub-octets sub))))

(defun fn-icar-carryp (carry)
  (declare (xargs :guard t))
  (or (atom carry)
      (and (consp (cdr carry))
           (equal (cadr carry)
                  (fn-own-feed-intent-id (fn-own-sub-msgid (car carry))
                                         (fn-own-sub-octets (car carry))))
           (equal (cddr carry)
                  (fn-own-feed-path-of (fn-own-sub-octets (car carry)))))))

(defthm fn-icar-carryp-of-carry-of
  (fn-icar-carryp (fn-icar-carry-of sub)))

(defthm fn-icar-carryp-when-atom
  (implies (atom carry) (fn-icar-carryp carry)))

; The carry's parts are read only for the submission it was built from.
(defun fn-icar-carries-p (sub carry)
  (declare (xargs :guard t))
  (and (consp carry) (consp (cdr carry)) (equal (car carry) sub)))

(defun fn-icar-intent-id (sub carry)
  (declare (xargs :guard t))
  (if (fn-icar-carries-p sub carry)
      (cadr carry)
    (fn-own-feed-intent-id (fn-own-sub-msgid sub) (fn-own-sub-octets sub))))

; The keystone: at every use, the carried identity is the digest of the
; submission it is used for.
(defthm fn-icar-intent-id-is-intent-id
  (implies (fn-icar-carryp carry)
           (equal (fn-icar-intent-id sub carry)
                  (fn-own-feed-intent-id (fn-own-sub-msgid sub)
                                         (fn-own-sub-octets sub)))))

; The submission's Path (fn-own-feed-path-of parses the article), carried the
; same way (PKT-113, lane carry-kind): parsed once at take, where the
; reference parsed it at the intent and again at the resolution.
(defun fn-icar-path (sub carry)
  (declare (xargs :guard t))
  (if (fn-icar-carries-p sub carry)
      (cddr carry)
    (fn-own-feed-path-of (fn-own-sub-octets sub))))

; KEYSTONE: at every use, the carried Path is the parse of the submission it
; is used for.
(defthm fn-icar-path-is-path-of
  (implies (fn-icar-carryp carry)
           (equal (fn-icar-path sub carry)
                  (fn-own-feed-path-of (fn-own-sub-octets sub)))))

; fn-own-submission-targets (books/owner.lisp) with the carried Path.
(defun fn-icar-submission-targets (o carry)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (if (null sub)
        nil
      (let* ((tbl (fn-own-feeds o))
             (msgid (fn-own-sub-msgid sub))
             (targets (fn-own-feed-targets
                       tbl (fn-own-sub-origin sub)
                       (fn-own-sub-feed-groups sub)
                       (fn-icar-path sub carry))))
        (fn-own-feed-new-targets targets tbl msgid)))))

(defthm fn-icar-submission-targets-is-submission-targets
  (implies (fn-icar-carryp carry)
           (equal (fn-icar-submission-targets o carry)
                  (fn-own-submission-targets o)))
  :hints (("Goal" :in-theory (e/d (fn-own-submission-targets)
                                  (fn-icar-path fn-icar-carryp
                                   fn-own-feed-targets
                                   fn-own-feed-new-targets
                                   fn-own-feed-path-of)))))

(in-theory (disable fn-icar-carry-of fn-icar-carryp fn-icar-carries-p fn-icar-intent-id
                    fn-icar-path fn-icar-submission-targets))

; -----------------------------------------------------------------------------
; The readers.

; The intent: the result and its records in one call, one identity and one
; target computation between them.  The reference computes the result twice
; (fn-own-submission-intent-records calls it) and the identity three times.
(defun fn-icar-submission-intent (o carry evidence generation txid)
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (identity (and sub (fn-icar-intent-id sub carry)))
         (targets (fn-icar-submission-targets o carry))
         (result
          (cond ((null sub) :absent)
                ((or (not (fn-feed-namep identity))
                     (not (fn-feed-namep evidence))
                     (not (natp generation)) (not (natp txid)))
                 :refused)
                ((not (fn-own-feed-target-capacityp
                       targets (fn-own-feeds o) (fn-own-sub-msgid sub)))
                 :capacity)
                (t :ready))))
    (cons result
          (if (equal result :ready)
              (fn-own-feed-intent-records
               targets (fn-own-sub-msgid sub) identity
               evidence generation txid (fn-own-feed-stamp o))
            nil))))

(defthm fn-icar-submission-intent-is-reference
  (implies (fn-icar-carryp carry)
           (equal (fn-icar-submission-intent o carry evidence generation txid)
                  (cons (fn-own-submission-intent-result o evidence generation txid)
                        (fn-own-submission-intent-records o evidence generation txid))))
  :hints (("Goal" :in-theory (e/d (fn-own-submission-intent-result
                                   fn-own-submission-intent-records)
                                  (fn-own-submission-targets
                                   fn-own-feed-target-capacityp
                                   fn-own-feed-intent-records
                                   fn-feed-namep fn-own-feed-intent-id)))))

(defun fn-icar-submission-resolution-records (o carry word evidence generation txid)
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (completion (fn-own-outcome-completion o word))
         (kind (cond ((equal completion :durable) :feed-commit)
                     ((member-equal completion '(:refused :clock-unusable))
                      :feed-abort)
                     (t nil))))
    (if (or (null sub) (null kind))
        nil
      (fn-own-feed-resolution-records
       kind (fn-icar-submission-targets o carry) (fn-own-sub-msgid sub)
       (fn-icar-intent-id sub carry)
       evidence generation txid (fn-own-feed-stamp o)))))

(defthm fn-icar-submission-resolution-records-is-reference
  (implies (fn-icar-carryp carry)
           (equal (fn-icar-submission-resolution-records
                   o carry word evidence generation txid)
                  (fn-own-submission-resolution-records
                   o word evidence generation txid)))
  :hints (("Goal" :in-theory (e/d (fn-own-submission-resolution-records)
                                  (fn-own-submission-targets
                                      fn-own-outcome-completion
                                      fn-own-feed-resolution-records
                                      fn-own-feed-intent-id)))))

; The composition with the host's writer: every carry fn-owner-take
; installs, whichever submission it was built from, gives the reference.
(defthm fn-icar-submission-intent-of-take-carry
  (equal (fn-icar-submission-intent o (fn-icar-carry-of sub)
                                    evidence generation txid)
         (cons (fn-own-submission-intent-result o evidence generation txid)
               (fn-own-submission-intent-records o evidence generation txid))))

(defthm fn-icar-submission-resolution-records-of-take-carry
  (equal (fn-icar-submission-resolution-records
          o (fn-icar-carry-of sub) word evidence generation txid)
         (fn-own-submission-resolution-records o word evidence generation txid)))
