; Canonical header on a peer history READ and the receive credit for its K28 envelope.
(in-package "ACL2")
(include-book "fncu-pool")
(fn2-book-layer :e)
(local (in-theory (disable fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-fields-value
                           fn2-fields-ref-off fn2-fields-ref-len fn2-fields-ref-slot fn2-fields-ref-gen
                           fn2-poolp fn2-pool-wfp fn2-pool-rows)))

(defconst *fn2-xfnc-batch-version* 1)
(defconst *fn2-xfnc-batch-interpretation* 1)
(deflayout fn2-xfnc-batch-header
 '((version :u8) (history-domain :u64be) (incarnation :u64be)
   (revision :u64be) (chain :digest) (view :u64be) (view-version :u64be)
   (interpretation :u16be) (next :u64be) (end :u64be)
   (stop (:enum fn2-xfnc-stop (:end :items :octets :work)))
   (count :u32be) (cursor (:octets16 366))))
(defun fn2-xfnc-batch-frontier-p (revision view view-version next end stop count)
  (declare (xargs :guard t))
  (and (posp revision) (unsigned-byte-p 60 revision)
       (posp view) (unsigned-byte-p 60 view)
       (posp view-version) (unsigned-byte-p 60 view-version)
       (unsigned-byte-p 60 next) (unsigned-byte-p 60 end)
       (unsigned-byte-p 32 count)
       (case stop (0 (equal next end)) ((1 2 3) (< next end)) (otherwise nil))))

(fn2-fnct-def-result fn2-xfnc-put-batch-header-fields fn2-xfnc-batch-header
 (history incarnation revision chain-off view view-version next end stop count cursor-off cursor-len)
 ((version *fn2-xfnc-batch-version*) (history-domain history) (incarnation incarnation)
  (revision revision) (chain :ref chain-off 32) (view view) (view-version view-version)
  (interpretation *fn2-xfnc-batch-interpretation*) (next next) (end end)
  (stop stop) (count count) (cursor :ref cursor-off cursor-len)))

; The producer supplies its checked view frontier plus a cursor minted from
; the same registration. CHAIN-OFF and CURSOR-OFF name owned scratch spans.
(defun fn2-xfnc-put-batch-header (base history incarnation revision chain-off view view-version
                                  next end stop count cursor-off cursor-len slot gen okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (if (and (fn2-origin-physicalp history incarnation)
           (fn2-xfnc-batch-frontier-p revision view view-version next end stop count)
           (posp cursor-len) (<= cursor-len 366))
      (fn2-xfnc-put-batch-header-fields base history incarnation revision chain-off view view-version
                                       next end stop count cursor-off cursor-len slot gen okind oslot ogen fn2-fields fn2-pool)
    (mv :bounds 0 0 fn2-fields fn2-pool)))
(fn2-pool-block-shape fn2-xfnc-put-batch-header-shape
 (fn2-xfnc-put-batch-header base history incarnation revision chain-off view view-version next end stop count
                            cursor-off cursor-len slot gen okind oslot ogen fn2-fields fn2-pool)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-fields 3) (fn2-pool 4))
 (("Goal" :in-theory (enable fn2-xfnc-put-batch-header))))
(in-theory (disable fn2-xfnc-put-batch-header))

; Both fncu versions encode the same five variable-width scope identifiers.
; NEXT can cross 2^32 even on a single-item READ. V2 adds its domain and
; widens four counters, so its extent grows by the fixed layout difference.
(defun fn2-xfnc-next-cursor-bound (wire-version cursor-size)
  (declare (xargs :guard t))
  (cond ((and (equal wire-version 1) (posp cursor-size) (<= cursor-size *fn2-fncu-v1-max-size*))
         (+ cursor-size (- *fn2-fncu-v2-max-size* *fn2-fncu-v1-max-size*)))
        ((and (equal wire-version 2) (posp cursor-size) (<= cursor-size *fn2-fncu-v2-max-size*)) cursor-size)
        (t 0)))

(local
 (defun fn2-xfnc-scope-sizers (name layout)
   (declare (xargs :verify-guards nil))
   (if (atom layout) nil
     (cons (fn2-codec-sizer-name name (caar layout))
           (fn2-xfnc-scope-sizers name (cdr layout))))))
(local
 (deftheory fn2-xfnc-cursor-sizers
   (append '(fn2-fncu-v1-size fn2-fncu-v2-size)
           (fn2-xfnc-scope-sizers 'fn2-fncu-v1 *fn2-fncu-v1-layout*)
           (fn2-xfnc-scope-sizers 'fn2-fncu-v2 *fn2-fncu-v2-layout*))))

; On the same five scope fields, the bound equals the generated V2 encoder's
; size for every admissible V1 extent. The counters' values do not affect
; either sizer in a fixed layout.
(defthm fn2-xfnc-next-cursor-bound-is-v2-size
  (let ((v1-size (fn2-fncu-v1-size base fn2-fields)))
    (implies (and (posp v1-size) (<= v1-size *fn2-fncu-v1-max-size*))
             (equal (fn2-xfnc-next-cursor-bound 1 v1-size)
                    (fn2-fncu-v2-size base fn2-fields))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-xfnc-cursor-sizers)
                                             (disable fn2-fields-ref-len fn2-layout-varsize)))))

; The accepted kind 28 prefix contains the class, empty reason and result length.
(defun fn2-xfnc-batch-read-budget (wire-version cursor-size capacity)
  (declare (xargs :guard t))
  (let ((next-size (fn2-xfnc-next-cursor-bound wire-version cursor-size)))
    (if (and (posp next-size) (natp capacity))
        (let ((header (+ (- *fn2-xfnc-batch-header-max-size* *fn2-fncu-v2-max-size*) next-size))
              (frame (min capacity (+ *fn2-pool-block-bytes* *fn2-fnct-trailer-octets*))))
          (nfix (- frame (+ *fn2-fnct-overhead* 7 header))))
      0)))

(defthm fn2-xfnc-batch-read-budget-fits
  (let ((amount (fn2-xfnc-batch-read-budget wire-version cursor-size capacity)))
    (implies (and (posp amount) (natp reply-cursor-size)
                  (<= reply-cursor-size (fn2-xfnc-next-cursor-bound wire-version cursor-size)))
             (let ((header (+ (- *fn2-xfnc-batch-header-max-size* *fn2-fncu-v2-max-size*) reply-cursor-size)))
               (and (<= (+ amount *fn2-fnct-overhead* 7 header) capacity)
                    (<= (+ amount *fn2-fnct-header-octets* 7 header) *fn2-pool-block-bytes*)))))
  :rule-classes nil)
(in-theory (disable fn2-xfnc-batch-read-budget))
