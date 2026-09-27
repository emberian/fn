; fn: what the store node's two composite steps on the record log do to the
; file kernel's phase (lane commit-onto-log, 2026-09-27).
;
; host/native/io.lisp checks the phase ACL2 answers after each composite:
; fnn-log-reserve expects :reserved, fnn-log-publish :completing.  These are
; the theorems behind those checks, over the store node the developer bridge
; calls (fn-olr-sn-reserve / fn-olr-sn-order, books/store-log-route.lisp;
; the owner's are the same steps inside fn-rcon-ocfg-io):
;
;   RESERVE from :ready below the u32 frontier ceiling reaches :reserved with
;   the frontier advanced by one: the txid reserved is the old frontier.
;   ORDER from :record-staged reaches :completing with the staged record
;   appended to the records: the record's place in the log's order is the
;   next position of the history, and its completion is enabled.
(in-package "ACL2")
(include-book "store-log-route")
(include-book "store-node-invariants-base")
(include-book "store-files-invariants")

(local (in-theory (disable fn-sn-statep)))

; The store node's files after one observation are the file kernel's step.
(defthm fn-olr-files-of-sn-io
  (implies (fn-sn-statep s)
           (equal (fn-sn-files (fn-sn-io s operation result))
                  (fn-sn-file-step (fn-sn-files s) operation result)))
  :hints (("Goal" :in-theory (enable fn-sn-io))))

(defthm fn-olr-sf-statep-of-sn-statep
  (implies (fn-sn-statep s) (fn-sf-statep (fn-sn-files s)))
  :hints (("Goal" :in-theory (enable fn-sn-statep))))

; Each file-kernel step's phase and fields, one lemma a step.
(defmacro fn-olr-step-facts (name fn phase-in args phase-out &rest more)
  `(defthm ,name
     (implies (and (fn-sf-statep f) (equal (fn-sf-phase f) ,phase-in))
              (and (equal (fn-sf-phase (,fn f ,@args)) ,phase-out) ,@more))
     :hints (("Goal" :in-theory (enable ,fn)))))

(fn-olr-step-facts fn-olr-frontier-file-ok fn-sf-frontier-file-result :frontier-staged (:ok)
  :frontier-data-durable
  (equal (fn-sf-frontier-candidate (fn-sf-frontier-file-result f :ok)) (fn-sf-frontier-candidate f))
  (equal (fn-sf-records (fn-sf-frontier-file-result f :ok)) (fn-sf-records f)))
(fn-olr-step-facts fn-olr-frontier-replace-ok fn-sf-frontier-replace-result :frontier-data-durable (:ok)
  :frontier-attempted
  (equal (fn-sf-frontier-candidate (fn-sf-frontier-replace-result f :ok)) (fn-sf-frontier-candidate f))
  (equal (fn-sf-records (fn-sf-frontier-replace-result f :ok)) (fn-sf-records f)))
(fn-olr-step-facts fn-olr-frontier-dir-ok fn-sf-frontier-dir-result :frontier-attempted (:ok)
  :reserved
  (equal (fn-sf-frontier (fn-sf-frontier-dir-result f :ok)) (fn-sf-frontier-candidate f))
  (equal (fn-sf-records (fn-sf-frontier-dir-result f :ok)) (fn-sf-records f)))
(fn-olr-step-facts fn-olr-record-file-ok fn-sf-record-file-result :record-staged (:ok)
  :record-data-durable
  (equal (fn-sf-record-candidate (fn-sf-record-file-result f :ok)) (fn-sf-record-candidate f))
  (equal (fn-sf-records (fn-sf-record-file-result f :ok)) (fn-sf-records f)))
(fn-olr-step-facts fn-olr-record-link-ok fn-sf-record-link-result :record-data-durable (:ok)
  :record-attempted
  (equal (fn-sf-record-candidate (fn-sf-record-link-result f :ok)) (fn-sf-record-candidate f))
  (equal (fn-sf-records (fn-sf-record-link-result f :ok)) (fn-sf-records f)))
(fn-olr-step-facts fn-olr-record-dir-ok fn-sf-record-dir-result :record-attempted (:ok)
  :completing
  (equal (fn-sf-records (fn-sf-record-dir-result f :ok))
         (append (fn-sf-records f) (list (fn-sf-record-candidate f)))))

(defthm fn-olr-start-frontier-facts
  (implies (and (fn-sf-statep f) (equal (fn-sf-phase f) :ready)
                (< (fn-sf-frontier f) *fn-sf-max-uint*))
           (and (equal (fn-sf-phase (fn-sf-start-frontier f)) :frontier-staged)
                (equal (fn-sf-frontier-candidate (fn-sf-start-frontier f))
                       (+ 1 (fn-sf-frontier f)))
                (equal (fn-sf-records (fn-sf-start-frontier f)) (fn-sf-records f))))
  :hints (("Goal" :in-theory (enable fn-sf-start-frontier))))

(local (in-theory (disable fn-sn-io fn-sf-statep
                           fn-sf-start-frontier fn-sf-frontier-file-result
                           fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                           fn-sf-record-file-result fn-sf-record-link-result
                           fn-sf-record-dir-result)))

(defthm fn-olr-sn-reserve-reaches-reserved
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           (and (equal (fn-sf-phase (fn-sn-files (fn-olr-sn-reserve s))) :reserved)
                (equal (fn-sf-frontier (fn-sn-files (fn-olr-sn-reserve s)))
                       (+ 1 (fn-sf-frontier (fn-sn-files s))))
                (equal (fn-sf-records (fn-sn-files (fn-olr-sn-reserve s)))
                       (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (enable fn-olr-sn-reserve fn-sn-file-step))))

(defthm fn-olr-sn-order-reaches-completing
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-staged))
           (and (equal (fn-sf-phase (fn-sn-files (fn-olr-sn-order s))) :completing)
                (equal (fn-sf-records (fn-sn-files (fn-olr-sn-order s)))
                       (append (fn-sf-records (fn-sn-files s))
                               (list (fn-sf-record-candidate (fn-sn-files s)))))))
  :hints (("Goal" :in-theory (enable fn-olr-sn-order fn-sn-file-step))))
