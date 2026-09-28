; Teeth for books/store-export (PRF-205): the import of an export replays
; the same history, and each refusal of the import's plan by name.
(in-package "ACL2")
(include-book "../../books/store-export")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

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
(assert-event (fn-bs-profile-logp *fn-bs-profile-development*))
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
;; validp is not a hypothesis: fn-bs-profile-logp reads the profile only
;; when it is valid (fn-bs-profile-of), so the retained logp implies it; the
;; weakened theorem was proved (the keystone as stated) before validp was
;; removed.  '(1 2 3) is refused by name above.

;; logp: the development preset's fields under the previous format's word
;; (fn-store-9).  In order, not a log profile (not a format-10 profile at
;; all): the plan does not import it under VALUES.
(defconst *sxpt-word-9* (cons *fn-bs-meta-format-9* (cdr *fn-bs-profile-development*)))
(assert-event (not (fn-bs-profile-validp *sxpt-word-9*)))
(assert-event (and (fn-sxp-increasingp *sxpt-records*)
                   (fn-sxp-config-names-increasingp *sxpt-configs* nil)))
(assert-event (not (fn-bs-profile-logp *sxpt-word-9*)))
(assert-event (not (equal (sxpt-plan *sxpt-word-9* *sxpt-frontier* *sxpt-configs*
                                     *sxpt-records*)
                          (list :import *sxpt-word-9* *sxpt-frontier*
                                *sxpt-configs* *sxpt-records*))))
(must-fail-checked
 (with-prover-step-limit
  20000
  (defthm sxpt-without-logp
   (implies (and (fn-sxp-increasingp records)
                 (fn-sxp-config-names-increasingp configs nil))
            (equal (sxpt-plan values frontier configs records)
                   (list :import values frontier configs records)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-sxp-increasingp)
                                   (fn-sxp-manifest fn-sxp-entries
                                    fn-bs-config-encode fn-bs-config-decode
                                    fn-bs-profile-validp)))))))

;; -----------------------------------------------------------------------------
;; The migration reads records as the export writes them: each record's
;; codec octets (host/native/io.lisp fnn-command-store-export: the log's
;; records as the open reads them), not frames.
(defun sxpt-encodings (events)
  (if (consp events)
      (cons (fn-store-event-encode (car events)) (sxpt-encodings (cdr events)))
    nil))
(make-event
 `(defconst *sxpt-raw-records*
    ',(pairlis$ '(0 1 2 4 5) (sxpt-encodings *sxpt-events*))))

;; The migration from format 9 (fn-sxp-import-of-a-format-9-export): the
;; archive the previous release exported -- the development preset's fields
;; in format 9's layout (the word, the frontier word, sixteen naturals with
;; the committed-history marker 0 at field 14), its config.json sealed under
;; SHA-256, and a MANIFEST of SHA-256 lines -- imports as the development
;; preset itself, format 10.
(defconst *sxpt-v9*
  (list* *fn-bs-meta-format-9* *fn-f9-frontier-word*
         (append (take 12 (cdr *fn-bs-profile-development*))
                 (list 0)
                 (nthcdr 12 (cdr *fn-bs-profile-development*)))))
(assert-event (equal (len *sxpt-v9*) 18))
(make-event `(defconst *sxpt-profile-9* ',(fn-f9-config-frame *sxpt-v9*)))
(make-event
 `(defconst *sxpt-manifest-9*
    ',(fn-sxp-manifest-under t (fn-sxp-entries *sxpt-profile-9* *sxpt-frontier*
                                               *sxpt-configs* *sxpt-raw-records*))))
;; The records translated (books/store-format-9-records.lisp): the article's
;; two identities re-derived under this format's digest, every other field and
;; every other event kept.
(make-event `(defconst *sxpt-records-10* ',(fn-f9r-records *sxpt-raw-records*)))
(assert-event (equal (strip-cars *sxpt-records-10*) (strip-cars *sxpt-raw-records*)))
(assert-event (equal (cdr *sxpt-records-10*) (cdr *sxpt-raw-records*)))
(assert-event (not (equal (car *sxpt-records-10*) (car *sxpt-raw-records*))))
(make-event
 `(defconst *sxpt-article-10*
    ',(cadr (fn-store-event-decode-exact (cdar *sxpt-records-10*)))))
(assert-event (equal (fn-record-msgid *sxpt-article-10*) "<sxpt-0@example.invalid>"))
(assert-event (equal (fn-record-payload *sxpt-article-10*) '(65)))
(assert-event (equal (fn-record-release-evidence *sxpt-article-10*) "evidence"))
(make-event
 `(defconst *sxpt-subject-10*
    ',(fn-record-octets-string (fn-id-text (fn-id-subject-of-payload '(65))))))
(assert-event (equal (fn-record-content-subject *sxpt-article-10*) *sxpt-subject-10*))
;; Reachable positive witness: the complete antecedent, then the conclusion.
(assert-event (null (fn-f9-profile-refusal *sxpt-v9*)))
(assert-event (not (equal (car *sxpt-records-10*) :refused)))
(assert-event (fn-sxp-increasingp *sxpt-records-10*))
(assert-event (equal (fn-f9-profile-of *sxpt-v9*) *fn-bs-profile-development*))
(assert-event (fn-sxp-archive-format-9p *sxpt-profile-9*))
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest-9* *sxpt-profile-9* *sxpt-frontier*
                            *sxpt-configs* *sxpt-raw-records* '(:current nil))
        (list :import *fn-bs-profile-development* *sxpt-frontier*
              *sxpt-configs* *sxpt-records-10*)))
;; A retention event naming a format-9 identity no article defined is refused
;; by name (the translation never guesses).
(make-event
 `(defconst *sxpt-v1-obligation*
    ',(fn-record-octets-string
       (fn-id-hex-octets (append *fn-id-obligation-label* (list 0 1 1)
                                 (make-list 32 :initial-element 5))))))
(assert-event (fn-f9r-v1-identity-textp *sxpt-v1-obligation*))
(defconst *sxpt-orphan*
  (list (cons 7 (fn-store-event-encode
                 (fn-store-retention-event-make :undertake 7 8 1 *sxpt-v1-obligation*
                                                "article-9" "local" 1)))))
(assert-event (equal (fn-f9r-records *sxpt-orphan*) '(:refused :unknown-identity 7)))
;; Hypothesis removed (no refusal): the marker `required' (1).  The retained
;; hypotheses hold; the translation is refused by name, so the plan is.
(defconst *sxpt-v9-marked* (update-nth *fn-f9-history-marker* 1 *sxpt-v9*))
(assert-event (equal (fn-f9-profile-refusal *sxpt-v9-marked*) :history-marker-required))
(make-event `(defconst *sxpt-profile-9m* ',(fn-f9-config-frame *sxpt-v9-marked*)))
(assert-event
 (equal (fn-sxp-import-plan
         (fn-sxp-manifest-under t (fn-sxp-entries *sxpt-profile-9m* *sxpt-frontier*
                                                  *sxpt-configs* *sxpt-raw-records*))
         *sxpt-profile-9m* *sxpt-frontier* *sxpt-configs* *sxpt-raw-records* '(:current nil))
        '(:refused :profile :history-marker-required)))
;; And a field the translation cannot hold (R below H is kept in order: H
;; below R) is refused by the relation's own name.
(defconst *sxpt-v9-short* (update-nth 3 196607 *sxpt-v9*))
(assert-event (equal (fn-f9-profile-refusal *sxpt-v9-short*)
                     :max-history-octets-below-max-record-octets))
(must-fail-checked
 (with-prover-step-limit
  20000
  (defthm sxpt-format-9-without-no-refusal
   (implies (and (not (equal (car (fn-f9r-records records)) :refused))
                 (fn-sxp-increasingp (fn-f9r-records records))
                 (fn-sxp-config-names-increasingp configs nil))
            (equal (fn-sxp-import-plan
                    (fn-sxp-manifest-under
                     t (fn-sxp-entries (fn-f9-config-frame values9) frontier
                                       configs records))
                    (fn-f9-config-frame values9) frontier configs records
                    '(:current nil))
                   (list :import (fn-f9-profile-of values9) frontier configs
                         (fn-f9r-records records))))
   :hints (("Goal" :do-not-induct t)))))

;; The written word (fn-sxp-log-profile-is-a-valid-log-profile).
(assert-event (let ((v (fn-sxp-log-profile *fn-bs-profile-development*)))
                (and (fn-bs-profile-validp v) (fn-bs-profile-logp v)
                     (equal (cdr v) (cdr *fn-bs-profile-development*)))))
;; Without validp: '(1 2 3) takes the word and stays invalid.
(assert-event (not (fn-bs-profile-validp '(1 2 3))))
(assert-event (not (fn-bs-profile-validp (fn-sxp-log-profile '(1 2 3)))))
(must-fail-checked
 (with-prover-step-limit
  20000
  (defthm sxpt-log-profile-without-validp
   (fn-bs-profile-validp (fn-sxp-log-profile values)))))

; increasing: records at sequences (3 2).
(defconst *sxpt-backwards*
  (list (cons 3 (cdr (nth 1 *sxpt-records*)))
        (cons 2 (cdr (nth 2 *sxpt-records*)))))
(assert-event (not (fn-sxp-increasingp *sxpt-backwards*)))
(assert-event (fn-sxp-config-names-increasingp *sxpt-configs* nil))
(assert-event (equal (sxpt-plan *fn-bs-profile-development* *sxpt-frontier*
                                *sxpt-configs* *sxpt-backwards*)
                     '(:refused :record-out-of-sequence 2)))
(must-fail-checked
 (with-prover-step-limit
  20000
  (defthm sxpt-without-increasing
   (implies (and (fn-bs-profile-logp values)
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
(must-fail-checked
 (with-prover-step-limit
  20000
  (defthm sxpt-without-config-order
   (implies (and (fn-bs-profile-logp values)
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
                            *sxpt-configs* *sxpt-records* '(:current ((2 . 1000))))
        '(:refused :profile :max-history-octets-below-max-record-octets)))

; A request that is not a profile request.
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest* *sxpt-profile* *sxpt-frontier*
                            *sxpt-configs* *sxpt-records* '(:bogus nil))
        '(:refused :profile :request)))

; A raised field: T to 1000, every other field kept, the same history.
(defconst *sxpt-raised*
  (fn-bs-profile-set-fields *fn-bs-profile-development* '((1 . 1000))))
(assert-event (fn-bs-profile-validp *sxpt-raised*))
(assert-event (not (equal *sxpt-raised* *fn-bs-profile-development*)))
(assert-event
 (equal (fn-sxp-import-plan *sxpt-manifest* *sxpt-profile* *sxpt-frontier*
                            *sxpt-configs* *sxpt-records* '(:current ((1 . 1000))))
        (list :import *sxpt-raised* *sxpt-frontier* *sxpt-configs* *sxpt-records*)))


; -----------------------------------------------------------------------------
; The archive's profile (fn-sxp-config-decode-archive).  A store's config.json
; from before batch AS (thirteen u64 fields, format 8), octet for octet as
; tests/acl2/store-profile-open-tests.lisp pins it: format 10 reads the
; previous release's export only (format 9), so this archive is refused by
; name, :store-format (batch AY retired the proposed D38 reader of this
; layout with format 10; a format-8 archive imports through a format-9
; release first).
(defconst *sxpt-pre-as-octets*
  '(70 78 83 77 1 1 0 0 0 148 0 10 102 110 45 115
    116 111 114 101 45 56 0 30 102 110 45 115 116 111 114 101
    45 97 108 108 111 99 97 116 105 111 110 45 102 114 111 110
    116 105 101 114 45 50 0 0 0 0 255 255 255 255 0 0
    1 0 0 0 0 0 0 0 0 0 4 0 0 0 0 0
    0 0 1 0 0 0 0 0 0 0 0 0 16 0 0 0
    0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 16 0 0 0 0
    0 0 0 16 0 0 0 0 0 0 0 0 0 0 70 112
    111 138 38 173 76 99 249 65 234 23 184 118 203 76 223 145
    252 221 169 197 118 171 16 149 10 151 172 203 171 232))

(assert-event (equal (len *sxpt-pre-as-octets*) 190))
(assert-event (null (fn-bs-config-decode *sxpt-pre-as-octets*)))
(assert-event (null (fn-sxp-config-decode-archive *sxpt-pre-as-octets*)))
(assert-event (equal (fn-sxp-profile-refusal *sxpt-pre-as-octets*) :store-format))
; The current layout reads as the open's decoder reads it.
(assert-event (equal (fn-sxp-config-decode-archive (fn-bs-config-encode *fn-bs-profile-scale*))
                     *fn-bs-profile-scale*))
; Anything else is nothing.
(assert-event (null (fn-sxp-config-decode-archive '(1 2 3))))
