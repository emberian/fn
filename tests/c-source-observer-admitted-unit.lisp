; Prepared actual admission -> typed observer controls. The request frame and
; principal fields are unused synthetic environment inputs. Actual actor take,
; generation checks, writer session and observer transitions are real. This
; does not claim source-byte materialization or live adoption completion.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-e-auth")
(defconst *fn2-cso-admitted-profile*
 (put-assoc-equal :authority 2
  (put-assoc-equal :t 8
   (put-assoc-equal :pool-classes '((24 . 4096) (8 . 65536)) *fn2-profile-tiny*))))
(defun fn2-cso-admitted-body (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-cso-admitted-profile* fn2-core))
      ((mv born0 id0 gen0 fn2-core)
       (fn2-machine-take-fn2-auth *fn2-none* *fn2-none* 0 7 0 0 *fn2-none* 0 1 0 1 fn2-core))
      ((mv born1 id1 gen1 fn2-core)
       (fn2-machine-take-fn2-auth *fn2-none* *fn2-none* 0 7 0 0 *fn2-none* 0 1 0 1 fn2-core))
      ((unless (and (eq born0 :ok) (eq born1 :ok) (not (equal id0 id1)))) (mv nil fn2-core))
      ((mv a fn2-core) (fn2-c-source-read-acquire id0 gen0 fn2-core))
      ((mv b fn2-core) (fn2-c-source-read-acquire id1 gen1 fn2-core))
      (writer (fn2-machine-kind-base *fn2-checkpoint-master-kind* fn2-core))
      ((unless (fn2-machine-idp writer fn2-core)) (mv nil fn2-core))
      (wgen (fn2-machine-generation writer fn2-core))
      ((mv begin token fn2-core) (fn2-c-source-writer-begin writer wgen fn2-core))
      ((mv stale st stgen fn2-core) (fn2-c-source-read-release id0 (+ gen0 1) fn2-core))
      ((mv ra ta tagen fn2-core) (fn2-c-source-read-release id0 gen0 fn2-core))
      ((mv blocked fn2-core) (fn2-c-source-read-acquire id0 gen0 fn2-core))
      ((mv rb tb tbgen fn2-core) (fn2-c-source-read-release id1 gen1 fn2-core))
      ((mv poll fn2-core) (fn2-c-source-writer-poll token writer wgen fn2-core)))
  (mv (and (eq a :ok) (eq b :ok) (eq begin :waiting) (posp token)
           (eq stale :stale) (equal st *fn2-none*) (equal stgen 0)
           (eq ra :ok) (equal ta *fn2-none*) (equal tagen 0) (eq blocked :busy)
           (eq rb :ok) (equal tb writer) (equal tbgen wgen)
           (eq poll :exclusive) (fn2-c-source-writer-exclusive token writer wgen fn2-core))
      fn2-core)))
(assert-event
 (with-local-stobj fn2-core
  (mv-let (ok fn2-core) (fn2-cso-admitted-body fn2-core) ok)))
