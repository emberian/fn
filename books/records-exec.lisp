; fn: the record decoder's executable twins (G9, the definition/implementation
; split; planning/evidence/book-split-2026-09-28.md).
;
; `books/records.lisp' defines the decoder's record level in :logic terms
; only.  This book defines, for each of its three functions, a twin whose
; :logic is that function and whose :exec is the one-payload-check body of
; PRF-333: the payload is an item read from the checked input, so its check
; is its length bound, and the final record check runs over the record with
; the empty payload in its place.  Guard verification of each twin is the
; proof that the :exec body computes the :logic value under the guard; the
; two equations it runs on are below.
;
; WHO INCLUDES IT: books/records-attach-concrete.lisp (the images'
; attachment of `fn-record-decode-exact') and the test books that exercise
; the twins.  No proof book includes it, so an edit to an :exec body here
; recertifies this book and the attachment's includers, and nothing that
; reasons about the record codec.  A proof about the decoder names the
; records.lisp functions; a twin never appears in a theorem above the seam.
;
; Host subject: fn-record-decode-exact, attached to
; `fn-record-decode-exact-exec' by books/records-attach-concrete.lisp
; (host/native/io.lisp's recovery decode: fnn-recover-log-stream-flush ->
; fn-lgb-decode-next -> fn-srs-decode -> fn-store-event-decode-exact ->
; fn-record-decode-exact).

(in-package "ACL2")
(include-book "records")

(local (in-theory (enable fn-cbor-codec-vocabulary
                          fn-record-guard-vocabulary)))
(local (in-theory (enable fn-record-shape-vocabulary
                          fn-record-cbor-octet-list-true-listp
                          fn-record-cbor-octet-listp-of-nthcdr
                          fn-record-cbor-octet-listp-of-take
                          fn-record-len-of-take-within-list)))

;; PRF-333: the decode checks each payload ONCE.  An item the decoder read
;; from the checked input is already an octet list: its payload check is the
;; length bound.
(defthm fn-record-payloadp-of-octets-by-definition
  (implies (fn-cbor-octet-listp payload)
           (equal (fn-record-payloadp payload)
                  (<= (len payload) *fn-record-max-payload*))))

;; The record check of a made record whose payload is valid is the check of
;; the same record with the empty payload: fn-record-p's other conjuncts do
;; not read the payload.  (syntaxp: the right side is an instance of the left.)
(defthm fn-record-p-of-make-is-without-payload
  (implies (and (syntaxp (not (equal payload ''nil)))
                (fn-record-payloadp payload))
           (equal (fn-record-p (fn-record-make sequence txid generation msgid payload groups
                                               obligation-id content-subject
                                               release-evidence charge stamp binding))
                  (fn-record-p (fn-record-make sequence txid generation msgid nil groups
                                               obligation-id content-subject
                                               release-evidence charge stamp binding))))
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-internals))))

(defun fn-record-decode-tail-exec (sequence txid generation msgid payload octets)
  (declare (xargs :guard (and (fn-record-uint64p sequence)
                              (fn-record-uint64p txid)
                              (fn-record-uint64p generation)
                              (fn-record-msgidp msgid)
                              (fn-record-payloadp payload)
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (mbe
   :logic (fn-record-decode-tail sequence txid generation msgid payload octets)
   :exec
   (let ((count-result (fn-record-read-uint octets)))
     (if (not (fn-record-parse-okp count-result))
         (fn-record-parse-error :group-count)
       (let ((count (fn-record-parse-value count-result)))
         (if (< *fn-record-max-groups* count)
             (fn-record-parse-error :groups-limit)
           (let ((groups-result
                  (fn-record-parse-groups count
                                          (fn-record-parse-rest count-result))))
             (if (not (fn-record-parse-okp groups-result))
                 groups-result
               (let ((id-result
                      (fn-record-read-bytes (fn-record-parse-rest groups-result))))
                 (if (not (fn-record-parse-okp id-result))
                     id-result
                   (let ((subject-result
                          (fn-record-read-bytes (fn-record-parse-rest id-result))))
                     (if (not (fn-record-parse-okp subject-result))
                         subject-result
                       (let ((evidence-result
                              (fn-record-read-bytes
                               (fn-record-parse-rest subject-result))))
                         (if (not (fn-record-parse-okp evidence-result))
                             evidence-result
                           (let ((charge-result
                                  (fn-record-read-uint
                                   (fn-record-parse-rest evidence-result))))
                             (if (not (fn-record-parse-okp charge-result))
                                 charge-result
                               (let* ((stamp-result
                                       (fn-record-read-uint
                                        (fn-record-parse-rest charge-result)))
                                      (binding-result
                                       (if (fn-record-parse-okp stamp-result)
                                           (fn-record-read-bytes
                                            (fn-record-parse-rest stamp-result))
                                         (fn-record-parse-error :invalid-binding)))
                                     (binding-decoded
                                      (fn-ab-decode (fn-record-parse-value binding-result)))
                                     (binding (cadr binding-decoded))
                                     (id (fn-record-octets-string
                                           (fn-record-parse-value id-result)))
                                      (subject (fn-record-octets-string
                                                (fn-record-parse-value subject-result)))
                                      (evidence (fn-record-octets-string
                                                 (fn-record-parse-value evidence-result)))
                                      (record
                                       (fn-record-make
                                        sequence txid generation msgid payload
                                        (fn-record-parse-value groups-result)
                                        id subject evidence
                                        (fn-record-parse-value charge-result)
                                        (fn-record-parse-value stamp-result) binding)))
                                 (if (not (fn-record-parse-okp stamp-result))
                                     stamp-result
                                   (if (or (not (fn-record-parse-okp binding-result))
                                          (not (equal (car binding-decoded) :ok)))
                                      (fn-record-parse-error :invalid-binding)
                                    (if (not (null (fn-record-parse-rest binding-result)))
                                       (fn-record-parse-error :trailing)
                                     ;; The payload position was checked by the caller and
                                     ;; is in the guard: the record is checked with the
                                     ;; empty payload in its place
                                     ;; (fn-record-p-of-make-is-without-payload).
                                     (if (fn-record-p
                                          (fn-record-make
                                           sequence txid generation msgid nil
                                           (fn-record-parse-value groups-result)
                                           id subject evidence
                                           (fn-record-parse-value charge-result)
                                           (fn-record-parse-value stamp-result) binding))
                                         (fn-record-parse-ok record nil)
                                       (fn-record-parse-error :invalid))))))))))))))))))))))


(defun fn-record-decode-after-header-exec (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)
                  :verify-guards nil))
  (mbe
   :logic (fn-record-decode-after-header octets)
   :exec
   (let ((sequence-result (fn-record-read-uint octets)))
     (if (not (fn-record-parse-okp sequence-result))
         sequence-result
       (let ((txid-result
              (fn-record-read-uint (fn-record-parse-rest sequence-result))))
         (if (not (fn-record-parse-okp txid-result))
             txid-result
           (let ((generation-result
                  (fn-record-read-uint (fn-record-parse-rest txid-result))))
             (if (not (fn-record-parse-okp generation-result))
                 generation-result
               (let ((msgid-result
                      (fn-record-read-bytes
                       (fn-record-parse-rest generation-result))))
                 (if (not (fn-record-parse-okp msgid-result))
                     msgid-result
                   (let ((msgid (fn-record-octets-string
                                 (fn-record-parse-value msgid-result))))
                     (if (not (fn-record-msgidp msgid))
                         (fn-record-parse-error :msgid)
                       (let ((payload-result
                              (fn-record-read-bytes
                               (fn-record-parse-rest msgid-result))))
                         (if (not (fn-record-parse-okp payload-result))
                             payload-result
                           (let ((payload (fn-record-parse-value payload-result)))
                             ;; The item's octets are already an octet list (the whole
                             ;; input's one check, fn-record-read-bytes-success-domain):
                             ;; only the length bound is left to test
                             ;; (fn-record-payloadp-of-octets-by-definition).
                             (if (not (<= (len payload) *fn-record-max-payload*))
                                 (fn-record-parse-error :payload)
                               (fn-record-decode-tail-exec
                                (fn-record-parse-value sequence-result)
                                (fn-record-parse-value txid-result)
                                (fn-record-parse-value generation-result)
                                msgid payload
                                (fn-record-parse-rest payload-result))))))))))))))))))

(defun fn-record-decode-exact-exec (octets)
  (declare (xargs :guard t :verify-guards nil))
  (mbe
   :logic (fn-record-decode-exact-impl octets)
   :exec
   (if (not (fn-cbor-at-mostp octets *fn-record-max-octets*))
       (fn-record-parse-error :limit)
     (if (not (fn-cbor-octet-listp octets))
         (fn-record-parse-error :malformed)
       (let ((magic-result (fn-record-read-bytes octets)))
         (if (not (fn-record-parse-okp magic-result))
             magic-result
           (if (not (equal (fn-record-parse-value magic-result)
                           *fn-record-magic*))
               (fn-record-parse-error :magic)
             (let ((version-result
                    (fn-record-read-uint (fn-record-parse-rest magic-result))))
               (if (not (fn-record-parse-okp version-result))
                   version-result
                 (if (not (member-equal (fn-record-parse-value version-result)
                                        '(3 4)))
                     (fn-record-parse-error :unknown-version)
                   (let ((parsed
                          (fn-record-decode-after-header-exec
                           (fn-record-parse-rest version-result))))
                     (if (fn-record-parse-okp parsed)
                         (if (equal (fn-record-schema-octet
                                     (fn-record-parse-value parsed))
                                    (fn-record-parse-value version-result))
                             (fn-record-result-ok (fn-record-parse-value parsed))
                           (fn-record-parse-error :schema))
                       parsed))))))))))))

(verify-guards fn-record-decode-tail-exec
  :hints (("Goal"
           :in-theory (e/d (fn-record-decode-tail)
                           (fn-record-read-uint fn-record-read-bytes
                               fn-record-parse-groups
                               fn-record-octets-string
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-record-parse-rest
                               fn-record-uint64p
                               fn-record-msgidp
                               fn-record-payloadp
                               fn-cbor-octet-listp
                               true-listp)))))
(verify-guards fn-record-decode-after-header-exec
  :hints (("Goal"
           :in-theory (e/d (fn-record-decode-after-header fn-record-decode-tail-exec)
                           (fn-record-read-uint fn-record-read-bytes
                               fn-record-decode-tail
                               fn-record-octets-string
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-record-parse-rest
                               fn-record-uint64p
                               fn-record-msgidp
                               fn-record-payloadp
                               fn-cbor-octet-listp
                               true-listp)))))
(verify-guards fn-record-decode-exact-exec
  :hints (("Goal"
           :in-theory (e/d (fn-record-decode-exact-impl fn-record-decode-after-header-exec)
                           (fn-record-read-uint fn-record-read-bytes
                               fn-record-decode-after-header
                               fn-record-parse-okp
                               fn-record-parse-value
                               fn-record-parse-rest
                               fn-cbor-octet-listp
                               true-listp)))))

;; The attachment's rewrite: the twin is the records.lisp decoder on every
;; input, with no hypothesis, by its :logic (guard verification above is what
;; makes the :exec compute it).
(defthm fn-record-decode-exact-exec-is-impl-by-definition
  (equal (fn-record-decode-exact-exec octets)
         (fn-record-decode-exact-impl octets)))

;; The two PRF-333 equations serve the guard proofs above, and the
;; attachment names the -by-definition equation in its hint; all are withdrawn
;; on export (enabled, the payload equation stalled a
;; store-checkpoint-arena-writer proof, persvati run-20260927T223317Z-f677).
(in-theory (disable fn-record-payloadp-of-octets-by-definition
                    fn-record-p-of-make-is-without-payload
                    fn-record-decode-exact-exec-is-impl-by-definition
                    fn-record-decode-tail-exec
                    fn-record-decode-after-header-exec
                    fn-record-decode-exact-exec))
