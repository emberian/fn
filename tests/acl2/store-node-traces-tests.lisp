; Mixed actual-wrapper traces, including allocator gaps and lost publication.
(in-package "ACL2")
(include-book "../../books/store-node-traces")
(include-book "../../books/codec-attach")

(defconst *snt-groups* '("fn.letters" "fn.test"))
(defconst *snt-first*
  (fn-record-make 0 1 1 "<trace-one@example>" '(65) *snt-groups*
                  "trace-pin-one" "trace-content-one" "trace-release-one" 2))
(defconst *snt-second*
  (fn-record-make 1 2 2 "<trace-two@example>" '(66) '("fn.test")
                  "trace-pin-two" "trace-content-two" "trace-release-two" 1))
(defconst *snt-barriers*
  '((:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
    (:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
    (:io :recovery-barrier :ok)))
(defconst *snt-reserve*
  '((:io :start-frontier nil) (:io :frontier-file :ok)
    (:io :frontier-replace :ok) (:io :frontier-directory :ok)))

; The uncertain initial frontier replacement survives, burning txid zero.
(defconst *snt-unused-reservation*
  (append '((:io :start-frontier nil) (:io :frontier-file :ok)
            (:io :frontier-replace :error) (:finish)
            (:crash :new :absent) (:recover)) *snt-barriers*))
(defconst *snt-first-events*
  (append *snt-unused-reservation* *snt-reserve*
          (list (list :prepare *snt-first*))
          '((:finish) (:io :core-completion :matching)
            (:io :record-file :ok) (:io :record-link :ok)
            (:io :record-directory :ok) (:finish) (:finish)
            (:crash :old :absent) (:recover)) *snt-barriers*))
(defconst *snt-first-state*
  (fn-snt-run (fn-sn-initial *snt-groups* 10) *snt-first-events*))
(assert-event (fn-snt-relation *snt-first-state*))
(assert-event (equal (fn-sf-phase (fn-sn-files *snt-first-state*)) :ready))
(assert-event (equal (fn-sf-successes (fn-sn-files *snt-first-state*)) '((0 . 1))))
(assert-event (fn-sn-committed-recordp (fn-sn-node *snt-first-state*) *snt-first*))
(assert-event (equal (fn-sn-node *snt-first-state*)
                     (fn-sf-replay-node *snt-groups* 10 (list *snt-first*) 2)))

; The second publication survives a failed link observation.  It becomes
; visible through actual replay without inventing a second acknowledgement.
(defconst *snt-second-events*
  (append *snt-reserve* (list (list :prepare *snt-second*))
          '((:io :record-file :ok) (:io :record-link :error)
            (:finish) (:unrecognized) (:crash :old :present) (:recover))
          *snt-barriers*))

; The same publication, dying in :record-data-durable with the link issued
; but unobserved (final-link cut), reaches the identical recovered node.
(defconst *snt-second-unobserved-link*
  (append *snt-reserve* (list (list :prepare *snt-second*))
          '((:io :record-file :ok) (:crash :old :present) (:recover))
          *snt-barriers*))
(assert-event (equal (fn-sn-node (fn-snt-run *snt-first-state* *snt-second-unobserved-link*))
                     (fn-sn-node (fn-snt-run *snt-first-state* *snt-second-events*))))
(assert-event (fn-snt-relation (fn-snt-run *snt-first-state* *snt-second-unobserved-link*)))
(defconst *snt-final* (fn-snt-run *snt-first-state* *snt-second-events*))
(assert-event (fn-snt-relation *snt-final*))
(assert-event (equal (fn-sf-successes (fn-sn-files *snt-final*)) '((0 . 1))))
(assert-event (fn-sn-committed-recordp (fn-sn-node *snt-final*) *snt-first*))
(assert-event (fn-sn-committed-recordp (fn-sn-node *snt-final*) *snt-second*))
(assert-event (equal (fn-sn-node *snt-final*)
                     (fn-sf-replay-node *snt-groups* 10
                                        (list *snt-first* *snt-second*) 3)))
