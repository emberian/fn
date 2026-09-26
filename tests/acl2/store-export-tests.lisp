; Teeth for books/store-export (PRF-205): the import of an export replays
; the same history, and each refusal of the import's plan by name.
(in-package "ACL2")
(include-book "../../books/store-export")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; A ground history of five committed records of four kinds (an article, an
; undertake, a release, two consumer events), each its sealed store frame
; as the open reads it, at sequences 0 1 2 4 5 (3 a burned reservation).
; Codec attachments are not evaluated in a defconst body, so the octets are
; computed by make-event.
(defconst *sxpt-events*
  (list (fn-record-make 0 0 0 "<sxpt-0@example.invalid>" '(65)
                        '("fn.letters") "archive" "subject" "evidence" 1 :legacy)
        (fn-store-retention-event-make :undertake 1 1 1
                                       "obligation-1" "article-0" "local" 1)
        (fn-store-retention-event-make :release 2 2 1
                                       "obligation-1" "article-0" "local" 0)
        (fn-cpe-make 4 3 1 '(:bootstrap (1) (2)))
        (fn-cpe-make 5 4 1 '(:register (3) (4) (5) 1 2 3))))

(defun sxpt-frames (events)
  (if (consp events)
      (cons (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                           *fn-frame-store-kind*
                           (fn-store-event-encode (car events)))
            (sxpt-frames (cdr events)))
    nil))

(make-event
 `(defconst *sxpt-records*
    ',(pairlis$ '(0 1 2 4 5) (sxpt-frames *sxpt-events*))))
(make-event
 `(defconst *sxpt-profile* ',(fn-bs-config-encode *fn-bs-profile-development*)))
(make-event `(defconst *sxpt-frontier* ',(fn-bs-frontier-encode-impl 6)))
(defconst *sxpt-configs* '(("groups" 1 2 3) ("peers" 4 5)))
(make-event
 `(defconst *sxpt-manifest*
    ',(fn-sxp-manifest (fn-sxp-entries *sxpt-profile* *sxpt-frontier*
                                       *sxpt-configs* *sxpt-records*))))

; Every record encodes, and the kinds are four.
(assert-event (not (member-equal nil (strip-cdrs *sxpt-records*))))
(assert-event (equal (strip-cars *sxpt-records*) '(0 1 2 4 5)))

; The archive's entry names, in order.
(assert-event
 (equal (strip-cars (fn-sxp-entries *sxpt-profile* *sxpt-frontier*
                                    *sxpt-configs* *sxpt-records*))
        (list (fn-sxp-text-octets "profile") (fn-sxp-text-octets "frontier")
              (fn-sxp-text-octets "config/groups") (fn-sxp-text-octets "config/peers")
              (fn-sxp-text-octets "records/00000000000000000000.txn")
              (fn-sxp-text-octets "records/00000000000000000001.txn")
              (fn-sxp-text-octets "records/00000000000000000002.txn")
              (fn-sxp-text-octets "records/00000000000000000004.txn")
              (fn-sxp-text-octets "records/00000000000000000005.txn"))))

; Reachable positive witness of the keystone: the complete antecedent, then
; the conclusion, at this history.
(assert-event (fn-bs-profile-validp *fn-bs-profile-development*))
(assert-event (fn-sxp-increasingp *sxpt-records*))
(assert-event (fn-sxp-config-names-increasingp *sxpt-configs* nil))
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest* *sxpt-profile* *sxpt-frontier*
                            *sxpt-configs* *sxpt-records* '(:current nil))
        (list :import *fn-bs-profile-development* *sxpt-frontier*
              *sxpt-configs* *sxpt-records*)))

; Hypothesis-removal witnesses: the retained hypotheses hold, the omitted
; one fails, and so does the conclusion; the weakened theorem is not
; proved (with the keystone's hint, under a step limit and without
; induction: the ground rows above are the counterexamples).
(defun sxpt-plan (values frontier configs records)
  (fn-sxp-import-plan
   (fn-sxp-manifest (fn-sxp-entries (fn-bs-config-encode values) frontier
                                    configs records))
   (fn-bs-config-encode values) frontier configs records '(:current nil)))

; validp: values '(1 2 3).
(assert-event (not (fn-bs-profile-validp '(1 2 3))))
(assert-event (and (fn-sxp-increasingp *sxpt-records*)
                   (fn-sxp-config-names-increasingp *sxpt-configs* nil)))
(assert-event (equal (sxpt-plan '(1 2 3) *sxpt-frontier* *sxpt-configs* *sxpt-records*)
                     '(:refused :profile :store-format)))
(must-fail
 (with-prover-step-limit
  20000
  (defthm sxpt-without-validp
   (implies (and (fn-sxp-increasingp records)
                 (fn-sxp-config-names-increasingp configs nil))
            (equal (sxpt-plan values frontier configs records)
                   (list :import values frontier configs records)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-sxp-increasingp)
                                   (fn-sxp-manifest fn-sxp-entries
                                    fn-bs-config-encode fn-bs-config-decode
                                    fn-bs-profile-validp)))))))

; increasing: records at sequences (3 2).
(defconst *sxpt-backwards*
  (list (cons 3 (cdr (nth 1 *sxpt-records*)))
        (cons 2 (cdr (nth 2 *sxpt-records*)))))
(assert-event (not (fn-sxp-increasingp *sxpt-backwards*)))
(assert-event (fn-sxp-config-names-increasingp *sxpt-configs* nil))
(assert-event (equal (sxpt-plan *fn-bs-profile-development* *sxpt-frontier*
                                *sxpt-configs* *sxpt-backwards*)
                     '(:refused :record-out-of-sequence 2)))
(must-fail
 (with-prover-step-limit
  20000
  (defthm sxpt-without-increasing
   (implies (and (fn-bs-profile-validp values)
                 (fn-sxp-config-names-increasingp configs nil))
            (equal (sxpt-plan values frontier configs records)
                   (list :import values frontier configs records)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-sxp-increasingp)
                                   (fn-sxp-manifest fn-sxp-entries
                                    fn-bs-config-encode fn-bs-config-decode
                                    fn-bs-profile-validp)))))))

; configuration order: names ("b" "a").
(defconst *sxpt-configs-backwards* '(("b" 1) ("a" 2)))
(assert-event (not (fn-sxp-config-names-increasingp *sxpt-configs-backwards* nil)))
(assert-event (fn-sxp-increasingp *sxpt-records*))
(assert-event (equal (sxpt-plan *fn-bs-profile-development* *sxpt-frontier*
                                *sxpt-configs-backwards* *sxpt-records*)
                     '(:refused :config-out-of-sequence)))
(must-fail
 (with-prover-step-limit
  20000
  (defthm sxpt-without-config-order
   (implies (and (fn-bs-profile-validp values)
                 (fn-sxp-increasingp records))
            (equal (sxpt-plan values frontier configs records)
                   (list :import values frontier configs records)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-sxp-increasingp)
                                   (fn-sxp-manifest fn-sxp-entries
                                    fn-bs-config-encode fn-bs-config-decode
                                    fn-bs-profile-validp)))))))

; -----------------------------------------------------------------------------
; Refusals by name

; A record whose octets changed after the export: the MANIFEST names it.
(defun sxpt-flip-last (octets)
  (if (consp octets)
      (if (consp (cdr octets))
          (cons (car octets) (sxpt-flip-last (cdr octets)))
        (list (logxor 1 (nfix (car octets)))))
    nil))
(defconst *sxpt-tampered*
  (update-nth 2 (cons 2 (sxpt-flip-last (cdr (nth 2 *sxpt-records*))))
              *sxpt-records*))
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest* *sxpt-profile* *sxpt-frontier*
                            *sxpt-configs* *sxpt-tampered* '(:current nil))
        (list :refused :manifest-mismatch
              (fn-sxp-text-octets "records/00000000000000000002.txn"))))

; A MANIFEST with one octet changed (the profile line's first hex digit).
(defconst *sxpt-manifest-flipped*
  (cons (if (equal (car *sxpt-manifest*) 48) 49 48) (cdr *sxpt-manifest*)))
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest-flipped* *sxpt-profile* *sxpt-frontier*
                            *sxpt-configs* *sxpt-records* '(:current nil))
        (list :refused :manifest-mismatch (fn-sxp-text-octets "profile"))))

; A MANIFEST carrying a line more than the archive: it names itself.
(assert-event
 (equal (fn-sxp-import-plan (append *sxpt-manifest* '(10)) *sxpt-profile*
                            *sxpt-frontier* *sxpt-configs* *sxpt-records*
                            '(:current nil))
        (list :refused :manifest-mismatch (fn-sxp-text-octets "MANIFEST"))))

; Records out of sequence, with a MANIFEST rendered for them.
(assert-event
 (equal (sxpt-plan *fn-bs-profile-development* *sxpt-frontier*
                   *sxpt-configs* (list (nth 0 *sxpt-records*) (nth 2 *sxpt-records*)
                                        (nth 1 *sxpt-records*)))
        '(:refused :record-out-of-sequence 1)))

; A profile frame that is not a profile (a record's frame in its place).
(defconst *sxpt-not-a-profile* (cdr (nth 1 *sxpt-records*)))
(make-event
 `(defconst *sxpt-not-a-profile-manifest*
    ',(fn-sxp-manifest (fn-sxp-entries *sxpt-not-a-profile* *sxpt-frontier*
                                       *sxpt-configs* *sxpt-records*))))
(assert-event
 (equal (fn-sxp-import-plan *sxpt-not-a-profile-manifest* *sxpt-not-a-profile*
                            *sxpt-frontier* *sxpt-configs* *sxpt-records*
                            '(:current nil))
        '(:refused :profile :store-format)))

; An override that breaks a relation: H 1000 below R.
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest* *sxpt-profile* *sxpt-frontier*
                            *sxpt-configs* *sxpt-records* '(:current ((3 . 1000))))
        '(:refused :profile :max-history-octets-below-max-record-octets)))

; A request that is not a profile request.
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest* *sxpt-profile* *sxpt-frontier*
                            *sxpt-configs* *sxpt-records* '(:bogus nil))
        '(:refused :profile :request)))

; A raised field: T to 1000, every other field kept, the same history.
(defconst *sxpt-raised*
  (fn-bs-profile-set-fields *fn-bs-profile-development* '((2 . 1000))))
(assert-event (fn-bs-profile-validp *sxpt-raised*))
(assert-event (not (equal *sxpt-raised* *fn-bs-profile-development*)))
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest* *sxpt-profile* *sxpt-frontier*
                            *sxpt-configs* *sxpt-records* '(:current ((2 . 1000))))
        (list :import *sxpt-raised* *sxpt-frontier* *sxpt-configs* *sxpt-records*)))
