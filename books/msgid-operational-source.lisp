; The operational source includes actual layout/key/frontiers. Its logical
; rows are the catalog projection, while ROOTS name its retained backing.
(in-package "ACL2")
(include-book "msgid-probe-layout")
(include-book "msgid-query-state")

(fn-defrecord fn-mio
  :tag :fn-mio
  :constructor (fn-mio-make generation table-root row-root key pages count
                            frontier words rows)
  :fields ((fn-mio-generation t) (fn-mio-table-root t) (fn-mio-row-root t)
           (fn-mio-key t) (fn-mio-pages t) (fn-mio-count t)
           (fn-mio-frontier t) (fn-mio-words t) (fn-mio-rows t))
  :recognizer nil)

; Every committed catalog ordinal is reachable before the first empty slot
; in its actual operational key's circular probe. This is stronger than
; merely finding the tag somewhere in the table.
(defun fn-mio-covered-from (i count frontier key pages words rows)
  (declare (xargs :measure (nfix (- (nfix count) (nfix i)))
                  :guard t :verify-guards nil))
  (if (or (not (true-listp rows)) (not (natp i)) (not (natp count)) (>= i count))
      t
    (let* ((row (nth i rows))
           (tag (fn-mpxt-tag (fn-record-msgid row) key)))
      (and (posp pages) (true-listp words)
           (fn-held-p row)
           (natp frontier) (natp (fn-record-sequence row))
           (< (fn-record-sequence row) frontier)
           (fn-mpl-reachable tag i (list (fn-mpx-home tag pages) pages 0)
                             pages words)
           (fn-mio-covered-from (+ 1 i) count frontier key pages words rows)))))

(defun fn-mio-chronologicalp (rows)
  (declare (xargs :guard t :verify-guards nil))
  (or (atom rows)
      (and (fn-held-p (car rows))
           (or (atom (cdr rows))
               (and (fn-held-p (cadr rows))
                    (< (nfix (fn-record-sequence (car rows)))
                       (nfix (fn-record-sequence (cadr rows))))))
           (fn-mio-chronologicalp (cdr rows)))))

(defun fn-mio-readyp (source)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-mio-shapep source)
       (posp (fn-mio-generation source))
       (posp (fn-mio-pages source))
       (natp (fn-mio-count source)) (natp (fn-mio-frontier source))
       (true-listp (fn-mio-rows source))
       (equal (len (fn-mio-rows source)) (fn-mio-count source))
       (fn-mio-chronologicalp (fn-mio-rows source))
       (fn-mpxt-wp (fn-mio-words source))
       (equal (len (fn-mio-words source))
              (* *fn-mpxt-page-words* (fn-mio-pages source)))
       (fn-mio-covered-from 0 (fn-mio-count source) (fn-mio-frontier source)
                            (fn-mio-key source) (fn-mio-pages source)
                            (fn-mio-words source) (fn-mio-rows source))))

; Logical capture after provider admission. The native/core capture also
; checks ticket association to BOTH registered roots; the ticket alone is
; not an immutable backing proof. No layout or row reconstruction occurs.
(defun fn-mio-query-capture (source ticket msgid)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn-mpxt-tag msgid (fn-mio-key source))))
    (fn-miq-make ticket (fn-mio-generation source) (fn-mio-key source)
                 (fn-mio-count source) (fn-mio-frontier source)
                 (fn-mio-pages source) msgid tag
                 (list (fn-mpx-home tag (nfix (fn-mio-pages source)))
                       (fn-mio-pages source) 0)
                 nil nil :probing)))

(verify-guards fn-mio-covered-from
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))
(verify-guards fn-mio-chronologicalp)
(verify-guards fn-mio-readyp)
(verify-guards fn-mio-query-capture)

(defthm fn-mio-covered-from-candidate
  (implies (and (natp i) (natp ordinal) (natp count)
                (<= i ordinal) (< ordinal count) (true-listp rows)
                (fn-mio-covered-from i count frontier key pages words rows))
           (let ((tag (fn-mpxt-tag (fn-record-msgid (nth ordinal rows)) key)))
             (and (fn-held-p (nth ordinal rows))
                  (< (fn-record-sequence (nth ordinal rows)) frontier)
                  (fn-mpl-reachable tag ordinal
                    (list (fn-mpx-home tag pages) pages 0) pages words))))
  :hints (("Goal" :induct (fn-mio-covered-from i count frontier key pages words rows)
           :in-theory (enable fn-mio-covered-from))))

(in-theory (disable fn-mio-covered-from fn-mio-chronologicalp fn-mio-readyp
                    fn-mio-query-capture))
