; Witnesses and teeth for books/filed-history: the reclaim-aware history
; invariant FN-O1-FILES-INVP carried by every Store transition (KR1-KR7), and
; the reclaim rewrite of a record (K0).
;
; A concrete store (store-node-tests' reserved store, groups fn.letters and
; fn.test) stages and then publishes a record: the held row is interned at
; handle 0 of an arena holding the payload, so the staged row meets
; FN-O1-PREPARE-KEEPS-THE-HISTORY's hypothesis (KR5), and the record-directory
; :ok that appends it (the one step that changes the records, KR1) leaves the
; files invariant, with the row among the records and no candidate left.  The
; finish (KR2), a crash that keeps the record (KR3, the :present choice) and,
; after the crash, the recovery (KR4) are evaluated on the same store, and a
; seal of one more payload (KR7) keeps the invariant.  Two records run through
; it: a FILED one (*otf-good*, groups fn.letters, the payload names fn.test and
; fn.letters) and its RECLAIMED form *otf-z* (FN-RCLP-TOMBSTONED of it: the
; groups kept, the payload a reclaim tombstone), for which the old all-filed
; predicate FN-O1-RECORDS-FILEDP is NIL and the invariant holds throughout;
; the checked mutation drops the tombstone disjunct from the invariant and is
; then false of the satisfiable reclaimed instance.
; Removal teeth: an UNFILED non-tombstone record (*otf-bad*, groups fn.test,
; payload naming fn.letters only); a row whose handle lies outside the arena;
; a composite row whose held article is not its composite's article.
(in-package "ACL2")
(include-book "store-node-tests")
(include-book "held-rows-tests")
(include-book "key-statements-tests")   ; *kst-event*: a composite for the forged-row tooth
(include-book "store-identity-traces-tests")   ; a Store that stages a composite (kind-4) row
(include-book "owner-prepare-deferred-carried-tests") ; consumer and retention events a Store stages
(include-book "../../books/topic-history-local-proposals") ; the topic install a Store stages
(include-book "../../books/crypto-attach")
(include-book "../../books/codec-attach")

(defconst *otf-crlf* (coerce '(#\Return #\Newline) 'string))
(defun otf-src (newsgroups)
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" *otf-crlf*
                "Newsgroups: " newsgroups *otf-crlf*
                "Subject: s" *otf-crlf*
                "Message-ID: <w1@b.example>" *otf-crlf*
                *otf-crlf* "body" *otf-crlf*)))
(defun otf-wire (payload groups)
  (fn-record-make 0 0 0 "<w1@b.example>" payload groups
                  "otf-pin" "otf-content" "otf-release" 2 841000000))
; filed: groups fn.letters, the payload names fn.test and fn.letters
(defconst *otf-good* (otf-wire (otf-src "fn.test,fn.letters") '("fn.letters")))
; unfiled: groups fn.test, the payload names fn.letters only
(defconst *otf-bad* (otf-wire (otf-src "fn.letters") '("fn.test")))

; the reclaimed form of the filed record: the groups kept, the payload a tombstone
(defconst *otf-z* (fn-rclp-tombstoned *otf-good*))

; ---------------------------------------------------------------------------
; KR5 for the identity prepare, on the composite (kind-4) row of a signed
; article: the Store of store-identity-traces-tests after the keyring
; enrollment stages the composite row whose article is filed (*otf-sig-good*),
; or reclaimed (*otf-sig-z*, its tombstone); the unfiled one (*otf-sig-bad*:
; groups example, payload naming other) is the removal tooth of the row
; hypothesis (the start is invariant, the row is not, the files after are not).
(defun otf-sig-id (n) (concatenate 'string "<sig" (coerce (list (code-char (+ 48 n))) 'string) "@example.invalid>"))
(defun otf-sig-src (n newsgroups)
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" *otf-crlf* "Newsgroups: " newsgroups *otf-crlf*
                "Subject: s" *otf-crlf* "Message-ID: " (otf-sig-id n) *otf-crlf*
                *otf-crlf* "body" *otf-crlf*)))
(defun otf-sig-record (n payload)
  (fn-record-make n n n (otf-sig-id n) payload *sit-groups*
                  (concatenate 'string "signed-obligation" (coerce (list (code-char (+ 48 n))) 'string))
                  "signed-subject" "signed-release" 3 841000000))
(defun otf-sig-wire (rec)
  (fn-hsig-authorized-article-event
   (fn-record-sequence rec) (fn-record-txid rec) (fn-record-generation rec) 1 *sit-snapshot*
   (fn-record-msgid rec) (fn-record-string-octets "signed-subject")
   (fn-record-encode-impl rec) *sit-principal* *sit-keys* (fn-record-payload rec)
   *sit-signatures* *sit-ml-key* :verified :verified))
(defconst *otf-sig-good* (otf-sig-record 1 (otf-sig-src 1 "example,other")))
(defconst *otf-sig-z* (fn-rclp-tombstoned *otf-sig-good*))
(defconst *otf-sig-bad* (otf-sig-record 1 (otf-sig-src 1 "other")))

; ---------------------------------------------------------------------------
; D2's conjuncts, each removed alone (the rows of a prepare cannot reach all
; three: the identity gate refuses a composite whose held article is not its
; composite's, so a forged one stays unstaged).  The rows: an unfiled record
; (records conjunct), a composite row whose held article is another record
; (composites conjunct), a held row whose handle lies outside the arena with
; no groups (handles conjunct).
(defconst *otf-nog* (otf-wire (otf-src "fn.letters") nil))

