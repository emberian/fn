; Teeth for the native shared-owner prepare correspondence.

(in-package "ACL2")
(include-book "../../books/owner-prepare-correspondence")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *opc-groups* '("fn.letters" "fn.test"))
(defconst *opc-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record*)))
(defconst *opc-post-config*
  (fn-inj-make-config
   t '(102 110 46 111 112 99 46 105 110 118 97 108 105 100)
   (list (fn-nntp-string-octets "fn.letters")
         (fn-nntp-string-octets "fn.test"))
   32768))

(defconst *opc-first*
  (fn-record-make 0 0 0 "<opc-first@example.invalid>" '(65 66)
                  *opc-groups* "opc-pin-1" "opc-subject-1"
                  "opc-release-1" 2 841000000))
(defconst *opc-second*
  (fn-record-make 1 1 1 "<opc-second@example.invalid>" '(67 68)
                  '("fn.test") "opc-pin-2" "opc-subject-2"
                  "opc-release-2" 1 841000000))

(defun opc-run (oc events)
  (declare (xargs :guard (fn-sn-statep
                          (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (if (consp events)
      (opc-run (fn-ocfg-step oc (car events)) (cdr events))
    oc))

(defconst *opc-reserve-events*
  '((:store (:io :start-frontier nil))
    (:store (:io :frontier-file :ok))
    (:store (:io :frontier-replace :ok))
    (:store (:io :frontier-directory :ok))))

; Reach a second reservation through the same configured-owner events used by
; the host, with one nonempty durable record already committed.
(defconst *opc-0*
  (fn-ocfg-make
   (fn-own-configure
    (fn-own-start (fn-sn-initial *opc-groups* 10) 3)
    *opc-post-config*)
   *opc-config* nil nil))
(defconst *opc-first-reserved* (opc-run *opc-0* *opc-reserve-events*))
(defconst *opc-first-staged* (fn-opc-prepare *opc-first-reserved* *opc-first*))
(defconst *opc-first-completing*
  (opc-run *opc-first-staged*
           '((:store (:io :record-file :ok))
             (:store (:io :record-link :ok))
             (:store (:io :record-directory :ok)))))
(defconst *opc-ready-one*
  (fn-ocfg-step *opc-first-completing* '(:complete)))
(defconst *opc-second-reserved*
  (opc-run *opc-ready-one* *opc-reserve-events*))
(defconst *opc-second-fast*
  (fn-opc-prepare *opc-second-reserved* *opc-second*))
(defconst *opc-second-spec*
  (fn-ocfg-step *opc-second-reserved*
                (list :store (list :prepare *opc-second*))))

(assert-event (fn-own-relation (fn-ocfg-owner *opc-second-reserved*)))
(assert-event
 (equal (len (fn-sf-records
              (fn-sn-files
               (fn-own-store (fn-ocfg-owner *opc-second-reserved*)))))
        1))
(assert-event (equal *opc-second-fast* *opc-second-spec*))
(assert-event
 (equal (fn-sf-phase
         (fn-sn-files (fn-own-store (fn-ocfg-owner *opc-second-fast*))))
        :record-staged))
(assert-event
 (equal (fn-opc-pending-octets *opc-second-fast*)
        (fn-record-encode *opc-second*)))

; Owner/configuration effects are exact.  In particular, this is one live
; owner: prepare cannot reset its allocation counter, pin table, staged
; configuration record, pending owner, or feed state.
(assert-event
 (equal (fn-own-next-id (fn-ocfg-owner *opc-second-fast*))
        (fn-own-next-id (fn-ocfg-owner *opc-second-reserved*))))
(assert-event
 (equal (fn-own-pending (fn-ocfg-owner *opc-second-fast*))
        (fn-own-pending (fn-ocfg-owner *opc-second-reserved*))))
(assert-event
 (equal (fn-own-inflight (fn-ocfg-owner *opc-second-fast*))
        (fn-own-inflight (fn-ocfg-owner *opc-second-reserved*))))
(assert-event
 (equal (fn-own-feeds (fn-ocfg-owner *opc-second-fast*))
        (fn-own-feeds (fn-ocfg-owner *opc-second-reserved*))))
(assert-event
 (equal (fn-own-config (fn-ocfg-owner *opc-second-fast*))
        *opc-post-config*))
(assert-event (equal (fn-ocfg-config *opc-second-fast*)
                     (fn-ocfg-config *opc-second-reserved*)))
(assert-event (equal (fn-ocfg-pins *opc-second-fast*)
                     (fn-ocfg-pins *opc-second-reserved*)))
(assert-event (equal (fn-ocfg-staged *opc-second-fast*)
                     (fn-ocfg-staged *opc-second-reserved*)))

; A malformed next sequence is refused before either implementation can
; expose pending record bytes.
(defconst *opc-wrong-sequence*
  (fn-record-make 9 1 1 "<opc-second@example.invalid>" '(67 68)
                  '("fn.test") "opc-pin-2" "opc-subject-2"
                  "opc-release-2" 1 841000000))
(assert-event
 (equal (fn-opc-prepare *opc-second-reserved* *opc-wrong-sequence*)
        *opc-second-reserved*))
(assert-event
 (equal (fn-ocfg-step *opc-second-reserved*
                      (list :store (list :prepare *opc-wrong-sequence*)))
        *opc-second-reserved*))

; This candidate has correct counters but conflicts with the durable first
; article's Message-ID.  Binding rejects it, and both owner transitions are
; exact no-ops with no candidate bytes.
(defconst *opc-conflict*
  (fn-record-make 1 1 1 "<opc-first@example.invalid>" '(67 68)
                  '("fn.test") "opc-pin-2" "opc-subject-2"
                  "opc-release-2" 1 841000000))
(assert-event
 (fn-sf-candidatep
  *opc-conflict*
  (fn-sf-records
   (fn-sn-files (fn-own-store (fn-ocfg-owner *opc-second-reserved*))))
  (fn-sf-frontier
   (fn-sn-files (fn-own-store (fn-ocfg-owner *opc-second-reserved*))))))
(assert-event
 (equal (fn-opc-prepare *opc-second-reserved* *opc-conflict*)
        *opc-second-reserved*))
(assert-event
 (equal (fn-ocfg-step *opc-second-reserved*
                      (list :store (list :prepare *opc-conflict*)))
        *opc-second-reserved*))

; Sole equality-premise tooth.  Keep the real nonempty files and all outer
; configured-owner fields, but replace the live node with a stale empty node.
; This is a well-shaped composed value, not a malformed outer list.  The fast
; node accepts the conflicting Message-ID while replay of the durable history
; rejects it, so the actual old and new owner call subjects differ.
(defconst *opc-related-owner* (fn-ocfg-owner *opc-second-reserved*))
(defconst *opc-stale-store*
  (fn-sn-make
   *opc-groups* 10
   (fn-sn-files (fn-own-store *opc-related-owner*))
   (fn-node-initial-state *opc-groups* 10)
   nil (fn-stx-index-empty)))
(defconst *opc-stale-owner*
  (fn-own-make
   *opc-stale-store* (fn-own-view *opc-related-owner*)
   (fn-own-conns *opc-related-owner*)
   (fn-own-next-id *opc-related-owner*)
   (fn-own-max-conns *opc-related-owner*)
   (fn-own-pending *opc-related-owner*)
   (fn-own-ledger *opc-related-owner*)
   (fn-own-clock *opc-related-owner*)
   (fn-own-facts *opc-related-owner*)
   (fn-own-config *opc-related-owner*)
   (fn-own-queue *opc-related-owner*)
   (fn-own-inflight *opc-related-owner*)
   (fn-own-feeds *opc-related-owner*)))
(defconst *opc-stale*
  (fn-ocfg-make *opc-stale-owner*
                (fn-ocfg-config *opc-second-reserved*)
                (fn-ocfg-pins *opc-second-reserved*)
                (fn-ocfg-staged *opc-second-reserved*)))
(assert-event (fn-sn-statep *opc-stale-store*))
(assert-event (fn-own-shapep *opc-stale-owner*))
(assert-event (fn-ocfg-shapep *opc-stale*))
(assert-event (not (fn-own-relation *opc-stale-owner*)))
(assert-event
 (equal (fn-sf-phase
         (fn-sn-files
          (fn-own-store
           (fn-ocfg-owner
            (fn-opc-prepare *opc-stale* *opc-conflict*)))))
        :record-staged))
(assert-event
 (equal (fn-ocfg-step *opc-stale*
                      (list :store (list :prepare *opc-conflict*)))
        *opc-stale*))
(must-fail
 (assert-event
  (equal (fn-opc-prepare *opc-stale* *opc-conflict*)
         (fn-ocfg-step *opc-stale*
                       (list :store (list :prepare *opc-conflict*))))))

; Actual recovery root: observed replay, owner start and post-recovery
; configuration establish the premise consumed by fn-opc-prepare.
(defconst *opc-opened*
  (fn-sn-open-observed *opc-groups* 10 1 (list *opc-first*)))
(defconst *opc-recovered*
  (fn-ocfg-make
   (fn-own-configure
    (fn-own-start (fn-sn-open-state *opc-opened*) 3)
    *opc-post-config*)
   *opc-config* nil nil))
(assert-event (fn-sn-open-okp *opc-opened*))
(assert-event (fn-own-relation (fn-ocfg-owner *opc-recovered*)))
