; The raw commitment vector, not physical extent size, chooses representation.
; Actual raw-unit hash and article constructor controls; no input-feed or
; complete 32-KiB APPEND progress is claimed by these prepared assertions.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "upload-location-hashes-unit")
(include-book "txn-upload-physical-location-unit")
(assert-event (equal *fn2-upload-raw-bytes* 12288))
(assert-event (not (fn2-am-manifestp 12288)))
(assert-event (and (fn2-am-manifestp 12289) (fn2-am-fits 12289)))
(assert-event (and (fn2-am-manifestp 32768) (fn2-am-fits 32768)))
(assert-event (and (= *fn2-article-location-hashes-max* 96)
                   (= *fn2-commit-write-resources* 3)
                   (= *fn2-storage-extent-units* 16)))
; Exercise all three actual raw hash writes at the boundary, with the
; existing independent digest oracle over each complete unit.
(assert-event
 (with-local-stobj fn2-core
  (mv-let (ok fn2-core)
   (fn2-ulh-fixture nil (make-list 12288 :initial-element 65) fn2-core) ok)))
(defun fn2-urt-constructor (total fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-txn-posting-profile* fn2-core))
      ((mv reserve ls lg fn2-core) (fn2-core-reserve 2 *fn2-upload-kind* 0 1 fn2-core))
      (manifest (fn2-am-manifestp total))
      (n (* 32 (if manifest (fn2-am-units total) (ceiling total *fn2-commit-unit-bytes*))))
      ((mv write fn2-core) (fn2-uss-write (make-list (+ 64 n) :initial-element 7) ls lg 0 fn2-core))
      ((mv put fn2-core)
       (fn2-txn-put-article 0 ls lg 0 1 ls lg 0 ls lg 32 64 n total 0 *fn2-storage-extent-units* 1 1 1 0
                            *fn2-upload-kind* 0 1 fn2-core))
      ((mv kind-code kind & & & &) (fn2-tupl-arg *fn2-article-entry-field-location-kind* fn2-core))
      ((mv hash-code & slot gen off len) (fn2-tupl-arg *fn2-article-entry-field-location-hashes* fn2-core)))
  (mv (and (eq reserve :ok) (eq write :ok) (eq put :ok) (eq kind-code :ok) (eq hash-code :ok)
           (= kind (if manifest *fn2-txn-location-source-manifest* *fn2-txn-location-raw-source*))
           (= slot ls) (= gen lg) (= off 64) (= len n) (<= n *fn2-article-location-hashes-max*)
           (if manifest (> (fn2-upload-page-bytes total) *fn2-upload-page-manifest*)
             (= (fn2-upload-page-bytes total) *fn2-upload-page-manifest*))
           (fn2-core-wfp fn2-core) (not (fn2-core-stopped-p fn2-core))) fn2-core)))
(assert-event (with-local-stobj fn2-core (mv-let (ok fn2-core) (fn2-urt-constructor 12288 fn2-core) ok)))
(assert-event (with-local-stobj fn2-core (mv-let (ok fn2-core) (fn2-urt-constructor 12289 fn2-core) ok)))
(assert-event (with-local-stobj fn2-core (mv-let (ok fn2-core) (fn2-urt-constructor 32768 fn2-core) ok)))
