; fn: the carry control journal's frame, FNCC (lane operations, PKT-869).
;
; The operator's carry controls (books/bp-carry-control.lisp) are durable
; records of their own application journal (books/app-journal.lisp domain
; :carry, JOURNAL/carry beside the FNWF workflow journal), not FNWF kinds:
; books/frame-journal.lisp, where the FNWF kinds live, has some 1,100
; dependents, and each FNWF kind doubled books/frame's
; fn-frame-workflow-protected guard proof (476k to 874k prover steps for
; one).  This book is the frame over the generic codec of
; books/frame-fields.lisp: its magic, its three kinds and their fields, the
; encoder and the decoder, and their round trip.
(in-package "ACL2")
(include-book "frame-journal")
(include-book "frame-invariants")

(defconst *fn-bpcc-frame-magic* '(70 78 67 67))   ; FNCC
(defconst *fn-bpcc-frame-kinds* '(:config :carry :waive))
; :config (JOURNAL-NAME), the journal's first record; :carry (VERB WORK
; REASON), books/bp-carry-control.lisp's control record; :waive (WORK
; PRINCIPAL REASON), its operator waiver (`carry drop WORK --abandon',
; lane carry-abandon, PRF-950).
(defconst *fn-bpcc-frame-specs*
  (list (cons :config '(:text))
        (cons :carry '(:text :text :text))
        (cons :waive '(:text :text :text))))
(defconst *fn-bpcc-frame-max-payload*
  (fn-frame-table-width *fn-bpcc-frame-specs*))

(defthm fn-bpcc-frame-spec-for-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-bpcc-frame-specs*) :none))
           (fn-frame-spec-listp (fn-frame-spec-for kind *fn-bpcc-frame-specs*)))
  :hints (("Goal" :in-theory (enable fn-frame-spec-for))))

(defun fn-bpcc-frame-record-okp (kind values)
  (declare (xargs :guard t))
  (let ((spec (fn-frame-spec-for kind *fn-bpcc-frame-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values))))

(defun fn-bpcc-frame-code (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :config) 1) ((equal kind :carry) 2) ((equal kind :waive) 3)
        (t 0)))

(defun fn-bpcc-frame-protected (kind values)
  (declare (xargs :guard t))
  (if (not (fn-bpcc-frame-record-okp kind values))
      :bad
    (let ((payload (fn-frame-fields-octets
                    (fn-frame-spec-for kind *fn-bpcc-frame-specs*) values)))
      (if (or (equal (fn-bpcc-frame-code kind) 0)
              (not (fn-cbor-octet-listp payload))
              (< *fn-bpcc-frame-max-payload* (len payload)))
          :bad
        (fn-frame-protected *fn-bpcc-frame-magic* *fn-frame-version*
                            (fn-bpcc-frame-code kind) payload)))))

(defun fn-bpcc-frame-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-bpcc-frame-max-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-bpcc-frame-magic*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)))
          (fn-frame-error :magic)
        (let* ((code (fn-frame-result-kind frame))
               (kind (cond ((equal code 1) :config) ((equal code 2) :carry)
                           ((equal code 3) :waive) (t nil))))
          (if (not kind)
              (fn-frame-error :kind)
            (let ((parsed (fn-frame-fields-parse
                           (fn-frame-spec-for kind *fn-bpcc-frame-specs*)
                           (fn-frame-result-payload frame))))
              (if (not (fn-frame-parse-okp parsed))
                  (fn-frame-error (fn-frame-parse-value parsed))
                (if (not (fn-bpcc-frame-record-okp kind (fn-frame-parse-value parsed)))
                    (fn-frame-error :fields)
                  (fn-frame-ok *fn-bpcc-frame-magic* *fn-frame-version*
                               kind (fn-frame-parse-value parsed)))))))))))
(defthm fn-bpcc-frame-max-payload-within-frame
  (<= *fn-bpcc-frame-max-payload* *fn-frame-max-payload*)
  :rule-classes nil)

; KEYSTONE (the carry journal's representation boundary): what the host
; seals (the protected prefix and the digest it computes over it,
; host/native/workflow.lisp fnn-app-frame) is what it reads back
; (fnn-app-unframe through host/workflow-host.lisp fn-workflow-carry-frame-decode).
(defthm fn-bpcc-frame-decode-of-sealed
  (implies (and (not (equal (fn-bpcc-frame-protected kind values) :bad))
                (fn-frame-digestp digest))
           (equal (fn-bpcc-frame-decode
                   (append (fn-bpcc-frame-protected kind values) digest) digest)
                  (fn-frame-ok *fn-bpcc-frame-magic* *fn-frame-version* kind values)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-encode
                            (magic *fn-bpcc-frame-magic*) (version *fn-frame-version*)
                            (kind (fn-bpcc-frame-code kind))
                            (payload (fn-frame-fields-octets
                                      (fn-frame-spec-for kind *fn-bpcc-frame-specs*) values))
                            (max-payload *fn-bpcc-frame-max-payload*))
                 (:instance fn-frame-fields-parse-of-octets
                            (specs (fn-frame-spec-for kind *fn-bpcc-frame-specs*))
                            (values values))
                 (:instance fn-bpcc-frame-max-payload-within-frame))
           :in-theory (e/d (fn-bpcc-frame-decode fn-bpcc-frame-protected
                            fn-bpcc-frame-code fn-frame-encode fn-frame-inputp
                            fn-frame-magicp)
                           (fn-frame-decode-of-encode fn-frame-fields-parse-of-octets
                            fn-frame-decode fn-frame-protected
                            fn-frame-fields-parse fn-frame-fields-octets
                            fn-frame-spec-for fn-frame-values-okp)))))
