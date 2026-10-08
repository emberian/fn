; Critical reclaim loader evidence. Host fn-owner-orcp-load-catalog-chunk /
; fnn-owner-reclaim-pass, exercised by tests/test_native_reclaim_walk.py::
; test_a_pass_longer_than_two_chunks_installs_and_counts_the_available.
(in-package "ACL2")
(include-book "../../books/reclaim-chunked-seal")
(include-book "catalog-availability-owner-load-tests")

(defconst *rclt-chunks* (list (list (cav-row 0 t)) nil (list (cav-row 1 nil))))
(defconst *rclt-payloads* (list (cav-bytes 0 t) (cav-bytes 1 nil)))
(defconst *rclt-old-row* (cav-row 2 nil))

; Execute both complete loads, snapshotting their logical rows via the
; catalog's scalar exports. Each loader starts by clearing the same catalog.
(defun rclt-compare (chunks view-index key keyed fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-cat (if keyed (fn-cat-clear-keyed key fn-cat) (fn-cat-clear fn-cat)))
         (fn-cat (fn-rcw-load-chunks chunks view-index fn-arena fn-cat))
         (a (p7-cat-rows 0 fn-cat))
         (fn-cat (if keyed
                     (fn-sca-load-held-rows-keyed key (fn-rcw-concat chunks) view-index fn-arena fn-cat)
                   (fn-sca-load-held-rows (fn-rcw-concat chunks) view-index fn-arena fn-cat))))
    (mv (equal a (p7-cat-rows 0 fn-cat)) fn-arena fn-cat)))
; IMPLEMENTATION MUTATION: the host forgets to clear the fresh catalog.
; Compare its row count with the full open's, on a previously populated cat.
(defun rclt-no-clear (chunks view-index key keyed fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-cat (fn-rcw-load-chunks chunks view-index fn-arena fn-cat))
         (a (fn-cat-count fn-cat))
         (fn-cat (if keyed
                     (fn-sca-load-held-rows-keyed key (fn-rcw-concat chunks) view-index fn-arena fn-cat)
                   (fn-sca-load-held-rows (fn-rcw-concat chunks) view-index fn-arena fn-cat))))
    (mv (equal a (fn-cat-count fn-cat)) fn-arena fn-cat)))

(defteeth fn-rcw-load-chunks-is-load
  :claim (()
          (equal (fn-rcw-load-chunks chunks view-index fn-arena (fn-cat-clear fn-cat))
                 (fn-sca-load-held-rows (fn-rcw-concat chunks) view-index fn-arena fn-cat)))
  :subject fn-rcw-load-chunks
  :witness ((chunks *rclt-chunks*)
            (view-index nil))
  :stobjs ((fn-arena (fn-arn-seal-many *rclt-payloads* fn-arena))
           (fn-cat (fn-cat-commit *rclt-old-row* fn-cat)))
  :stobj-checks
  (((equal (fn-rcw-load-chunks chunks view-index fn-arena (fn-cat-clear fn-cat))
           (fn-sca-load-held-rows (fn-rcw-concat chunks) view-index fn-arena fn-cat))
    (rclt-compare chunks view-index nil nil fn-arena fn-cat)
    :hints (("Goal" :in-theory (e/d (rclt-compare fn-sca-load-held-rows)
                                    (fn-rcw-load-chunks fn-sca-load-held-available-from)))))
   ((equal (fn-cat-count (fn-rcw-load-chunks chunks view-index fn-arena fn-cat))
           (fn-cat-count (fn-sca-load-held-rows (fn-rcw-concat chunks) view-index fn-arena fn-cat)))
    (rclt-no-clear chunks view-index nil nil fn-arena fn-cat)
    :hints (("Goal" :in-theory (e/d (rclt-no-clear fn-sca-load-held-rows)
                                    (fn-rcw-load-chunks fn-sca-load-held-available-from))))))
  :mutations ((missing-clear
               (:conclusion
                (equal (fn-cat-count (fn-rcw-load-chunks chunks view-index fn-arena fn-cat))
                       (fn-cat-count (fn-sca-load-held-rows (fn-rcw-concat chunks) view-index fn-arena fn-cat))))
               ((chunks *rclt-chunks*) (view-index nil))
               :fault "reclaim loads into the previous catalog without clearing it")))

(defteeth fn-rcw-load-chunks-keyed-is-keyed-load
  :claim (()
          (equal (fn-rcw-load-chunks chunks view-index fn-arena (fn-cat-clear-keyed key fn-cat))
                 (fn-sca-load-held-rows-keyed key (fn-rcw-concat chunks) view-index fn-arena fn-cat)))
  :subject fn-rcw-load-chunks
  :witness ((chunks *rclt-chunks*)
            (view-index nil) (key (make-list *fn-mpxt-key-octets* :initial-element 7)))
  :stobjs ((fn-arena (fn-arn-seal-many *rclt-payloads* fn-arena))
           (fn-cat (fn-cat-commit *rclt-old-row* fn-cat)))
  :stobj-checks
  (((equal (fn-rcw-load-chunks chunks view-index fn-arena (fn-cat-clear-keyed key fn-cat))
           (fn-sca-load-held-rows-keyed key (fn-rcw-concat chunks) view-index fn-arena fn-cat))
    (rclt-compare chunks view-index key t fn-arena fn-cat)
    :hints (("Goal" :in-theory (e/d (rclt-compare fn-sca-load-held-rows-keyed fn-sca-load-held-rows)
                                    (fn-rcw-load-chunks fn-sca-load-held-available-from)))))
   ((equal (fn-cat-count (fn-rcw-load-chunks chunks view-index fn-arena fn-cat))
           (fn-cat-count (fn-sca-load-held-rows-keyed key (fn-rcw-concat chunks) view-index fn-arena fn-cat)))
    (rclt-no-clear chunks view-index key t fn-arena fn-cat)
    :hints (("Goal" :in-theory (e/d (rclt-no-clear fn-sca-load-held-rows-keyed fn-sca-load-held-rows)
                                    (fn-rcw-load-chunks fn-sca-load-held-available-from))))))
  :mutations ((missing-keyed-clear
               (:conclusion
                (equal (fn-cat-count (fn-rcw-load-chunks chunks view-index fn-arena fn-cat))
                       (fn-cat-count (fn-sca-load-held-rows-keyed key (fn-rcw-concat chunks) view-index fn-arena fn-cat))))
               ((chunks *rclt-chunks*)
                (view-index nil) (key (make-list *fn-mpxt-key-octets* :initial-element 7)))
               :fault "reclaim skips the keyed clear and publishes old rows twice")))
