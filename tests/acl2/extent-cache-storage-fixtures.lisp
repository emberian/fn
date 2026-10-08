; Round-5 witnesses derive their table/backing snapshots by init and install.
(in-package "ACL2")
(include-book "../../books/extent-cache-storage-complete")
(include-book "../../books/extent-cache-memory-install")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *xcs5-et* '(7 9 11 100 3 77))
(defconst *xcs5-et2* '(8 9 12 100 3 77))
(defconst *xcs5-bytes* (append '(1 2 3) (make-list 32 :initial-element 0)))
(defconst *xcs5-entry-ledger*
  (list nil nil nil (list (cons *xcs5-et* '((35 0 0 0 0) :cached nil))
                          (cons *xcs5-et2* '((35 0 0 0 0) :cached nil))) nil))
(defconst *xcs5-zt* '(:decoded-window 7 11 100 3 100 3 0 77 3 0))
(defconst *xcs5-z* (list :decoded (list :verified 11 100 3 3 0 77 3 7 47 *xcs5-zt* 100 3 3) 3 0 3 0 3 3 :decoded))
(defconst *xcs5-z-ledger* (list nil nil nil (list (cons *xcs5-zt* '((35 0 0 0 0) :cached nil))) nil))
(defconst *xcs5-z-returned* (list nil nil nil (list (cons *xcs5-zt* '((35 0 0 0 0) :window :returned 0))) nil))
(defconst *xcs5-z-worker* (list 0 7 :returned *xcs5-zt*))
; Short logical arrays keep the ground proof compact. The live trace uses
; the actual creators, profile-sized windows, and guard-checked installers.
(defconst *xcs5-empty-entries* (list (make-list 8 :initial-element nil) (make-list 8 :initial-element nil)))
(defconst *xcs5-empty-wins* (list (make-list 8 :initial-element nil) (make-list 8 :initial-element '((0 0 0)))))
(defconst *xcs5-buf* '((1 2 3)))
(defconst *xcs5-dst* '((0 0 0 0)))
(defun-nx xcs5-entry-build ()
  (let ((init (fn-xc-init-all 1 0 nil nil)))
    (fn-xc-install-entry-funded *xcs5-entry-ledger* 11 100 3 77 *xcs5-et*
      (mv-nth 1 init) (mv-nth 2 init) *xcs5-empty-entries* *xcs5-bytes*)))
(defun-nx xcs5-decoded-build ()
  (let ((init (fn-xc-init-all 0 1 nil nil)))
    (fn-xc-install-decoded-bytes *xcs5-zt* *xcs5-z*
      (mv-nth 1 init) (mv-nth 2 init) *xcs5-empty-wins* *xcs5-buf*)))

(defthm xcs5-plan-is-published
  (fn-xc-decoded-planp *xcs5-z* *xcs5-zt*)
  :rule-classes nil
  :hints (("Goal" :in-theory (executable-counterpart-theory :here))))

(defthm xcs5-entry-build-ran-init-and-install
  (equal (xcs5-entry-build)
    (list :installed 0 nil '((1 t 7 9 11 100 3 0 0 0 0 0 77 0)) '(1 1 0)
      (list (cons (fn-xc-entry-key 11 100 3 77 *xcs5-et*) (make-list 7 :initial-element nil))
            (cons *xcs5-bytes* (make-list 7 :initial-element nil))) nil))
  :hints (("Goal" :in-theory (enable xcs5-entry-build fn-xc-install-entry-funded fn-xc-install-entry-bytes fn-xc-install-entry fn-xc-install fn-xc-init-all fn-xc-init fn-xc-append-free fn-xc-touch fn-xc-next-stamp fn-xc-write fn-xce-adopt fn-xc-token fn-xc-slot-token fn-xc-find fn-xc-find-free fn-xc-lru))))

(defthm xcs5-decoded-build-ran-init-and-install
  (equal (xcs5-decoded-build)
    (list :installed 0 nil '((3 t 7 0 11 100 3 100 3 3 0 0 77 0)) '(1 0 1)
      (list (cons *xcs5-z* (make-list 7 :initial-element nil))
            (cons *xcs5-buf* (make-list 7 :initial-element '((0 0 0)))))))
  :hints (("Goal" :expand ((:free (src count dst buf win) (fn-xcw-copy src count dst buf win))) :in-theory (enable xcs5-decoded-build fn-xc-install-decoded-bytes fn-xc-install-window fn-xc-install fn-xc-init-all fn-xc-init fn-xc-append-free fn-xc-touch fn-xc-next-stamp fn-xc-write fn-xcw-store-counted fn-xcw-copy fn-xc-token fn-xc-slot-token fn-xc-find fn-xc-find-free fn-xc-lru))))


(defconst *xcs5-zt1* '(:decoded-window 8 11 100 3 100 3 1 77 3 0))
(defconst *xcs5-z1* (list :decoded (list :verified 11 100 3 3 0 77 3 8 47 *xcs5-zt1* 100 3 3) 3 1 2 0 3 3 :decoded))
(defun-nx xcs5-entry-two-build ()
  (let* ((init (fn-xc-init-all 2 0 nil nil))
         (first (fn-xc-install-entry-funded *xcs5-entry-ledger* 12 100 3 77 *xcs5-et2*
                   (mv-nth 1 init) (mv-nth 2 init) *xcs5-empty-entries* *xcs5-bytes*)))
    (fn-xc-install-entry-funded *xcs5-entry-ledger* 11 100 3 77 *xcs5-et*
      (mv-nth 3 first) (mv-nth 4 first) (mv-nth 5 first) *xcs5-bytes*)))
(defun-nx xcs5-decoded-two-build ()
  (let* ((init (fn-xc-init-all 0 2 nil nil))
         (first (fn-xc-install-decoded-bytes *xcs5-zt1* *xcs5-z1*
                   (mv-nth 1 init) (mv-nth 2 init) *xcs5-empty-wins* *xcs5-buf*)))
    (fn-xc-install-decoded-bytes *xcs5-zt* *xcs5-z*
      (mv-nth 3 first) (mv-nth 4 first) (mv-nth 5 first) *xcs5-buf*)))
(defthm xcs5-entry-two-build-ran-init-and-install
  (equal (xcs5-entry-two-build)
    (list :installed 1 nil '((1 t 8 9 12 100 3 0 0 0 0 0 77 0) (1 t 7 9 11 100 3 0 0 0 0 0 77 1)) '(2 2 0)
      (list (list* (fn-xc-entry-key 12 100 3 77 *xcs5-et2*) (fn-xc-entry-key 11 100 3 77 *xcs5-et*) (make-list 6 :initial-element nil))
            (list* *xcs5-bytes* *xcs5-bytes* (make-list 6 :initial-element nil))) nil))
  :hints (("Goal" :in-theory (enable xcs5-entry-two-build fn-xc-install-entry-funded fn-xc-install-entry-bytes fn-xc-install-entry fn-xc-install fn-xc-init-all fn-xc-init fn-xc-append-free fn-xc-touch fn-xc-next-stamp fn-xc-write fn-xce-adopt fn-xc-token fn-xc-slot-token fn-xc-find fn-xc-find-free fn-xc-lru))))
(defthm xcs5-decoded-two-build-ran-init-and-install
  (equal (xcs5-decoded-two-build)
    (list :installed 1 nil '((3 t 8 0 11 100 3 100 3 3 0 1 77 0) (3 t 7 0 11 100 3 100 3 3 0 0 77 1)) '(2 0 2)
      (list (list* *xcs5-z1* *xcs5-z* (make-list 6 :initial-element nil))
            (list* '((1 2 0)) *xcs5-buf* (make-list 6 :initial-element '((0 0 0)))))))
  :hints (("Goal" :expand ((:free (src count dst buf win) (fn-xcw-copy src count dst buf win)))
           :in-theory (enable xcs5-decoded-two-build fn-xc-install-decoded-bytes fn-xc-install-window fn-xc-install fn-xc-init-all fn-xc-init fn-xc-append-free fn-xc-touch fn-xc-next-stamp fn-xc-write fn-xcw-store-counted fn-xcw-copy fn-xc-token fn-xc-slot-token fn-xc-find fn-xc-find-free fn-xc-lru))))

; Faulty implementations exist only in the teeth book.
(set-ignore-ok t)
(set-irrelevant-formals-ok t)
(defun xcs5-entry-stale-row (slot file eoff elen poff plen trailer p end fn-xcs fn-xce fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xce fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (natp slot) (< slot (fn-xcs-count fn-xcs))
                              (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end))
                  :verify-guards nil))
  (if (and (< slot (fn-xce-keys-length fn-xce)) (<= eoff poff) (<= (+ poff plen) (+ eoff elen))
           t)
      (let ((j (min (min end plen) (+ p *fn-ew-span-capacity*))))
        (if (< p j)
            (stobj-let ((fn-xce-entry (fn-xce-entriesi slot fn-xce))) (word fn-ew-span)
              (if (equal (fn-xce-entry-len fn-xce-entry) (+ elen *fn-frame-trailer-octets*))
                  (let ((fn-ew-span (fn-xce-copy (+ (- poff eoff) p) (- j p) 0 fn-xce-entry fn-ew-span)))
                    (mv :span fn-ew-span))
                (mv :miss fn-ew-span))
              (mv word j fn-ew-span))
          (mv :miss 0 fn-ew-span)))
    (mv :miss 0 fn-ew-span)))

(defun xcs5-entry-stale-row-mutant (from file eoff elen poff plen trailer p end fn-xcs fn-xcc fn-xce fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xce fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (natp from)
                              (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end))
                  :measure (nfix (- (fn-xcs-count fn-xcs) (nfix from))) :verify-guards nil))
  (if (and (fn-xc-readyp fn-xcs fn-xcc) (natp from) (< from (fn-xcs-count fn-xcs)))
      (mv-let (word j fn-ew-span)
        (if (and (< from (fn-xc-ne fn-xcc))
                 (fn-xc-slot-matchp from nil 1 file eoff elen 0 0 0 0 trailer 0 fn-xcs)
                 (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end))
            (xcs5-entry-stale-row from file eoff elen poff plen trailer p end fn-xcs fn-xce fn-ew-span)
          (mv :miss 0 fn-ew-span))
        (if (equal word :span)
            (mv-let (touch fn-xcs fn-xcc) (fn-xc-touch from fn-xcs fn-xcc)
              (declare (ignore touch))
              (mv :span (- j p) from fn-ew-span fn-xcs fn-xcc))
          (xcs5-entry-stale-row-mutant (1+ from) file eoff elen poff plen trailer p end fn-xcs fn-xcc fn-xce fn-ew-span)))
    (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc)))

(defun xcs5-entry-first-candidate-mutant (from file eoff elen poff plen trailer p end fn-xcs fn-xcc fn-xce fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xce fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (natp from)
                              (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end))
                   :verify-guards nil))
  (if (and (fn-xc-readyp fn-xcs fn-xcc) (natp from) (< from (fn-xcs-count fn-xcs)))
      (mv-let (word j fn-ew-span)
        (if (and (< from (fn-xc-ne fn-xcc))
                 (fn-xc-slot-matchp from nil 1 file eoff elen 0 0 0 0 trailer 0 fn-xcs)
                 (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end))
            (fn-xc-entry-span-row from file eoff elen poff plen trailer p end fn-xcs fn-xce fn-ew-span)
          (mv :miss 0 fn-ew-span))
        (if (equal word :span)
            (mv-let (touch fn-xcs fn-xcc) (fn-xc-touch from fn-xcs fn-xcc)
              (declare (ignore touch))
              (mv :span (- j p) from fn-ew-span fn-xcs fn-xcc))
          (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc)))
    (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc)))

(defun xcs5-decoded-stale-row (slot ledger file eoff elen poff compressed trailer decoded dict-id p end
                                  fn-xcs fn-xcc fn-xcw fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)
                              (natp slot) (< slot (fn-xcs-count fn-xcs))
                              (natp p) (natp end) (natp decoded))
                  :verify-guards nil))
  (let ((row (fn-xc-row slot fn-xcc)) (token (fn-xc-slot-token slot fn-xcs)))
    (if (and (<= (fn-xc-ne fn-xcc) slot) (< row (fn-xcw-plans-length fn-xcw)))
        (let ((z (fn-xcw-plansi row fn-xcw)))
          (if t
              (let ((j (fn-xc-span-end p end decoded (fn-pwz-nth 7 token)
                                     (fn-pwz-token-window-length token))))
                (if (< p j)
                    (stobj-let ((fn-xcw-win (fn-xcw-winsi row fn-xcw))) (word fn-ew-span)
                      (fn-pwz-cache-span-at ledger token file eoff elen poff compressed trailer
                                           decoded dict-id p j fn-xcw-win fn-ew-span)
                      (mv word j fn-ew-span))
                  (mv :miss 0 fn-ew-span)))
            (mv :miss 0 fn-ew-span)))
      (mv :miss 0 fn-ew-span))))

(defun xcs5-decoded-stale-row-mutant (from ledger file eoff elen poff compressed trailer decoded dict-id p end
                                 fn-xcs fn-xcc fn-xcw fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                              (natp from) (natp p) (natp end) (natp decoded))
                  :measure (nfix (- (fn-xcs-count fn-xcs) (nfix from)))
                  :verify-guards nil))
  (if (and (fn-xc-readyp fn-xcs fn-xcc) (natp from) (< from (fn-xcs-count fn-xcs)))
      (mv-let (word j fn-ew-span)
        (if (and (fn-xc-slot-matchp from nil 3 file eoff elen poff compressed decoded dict-id trailer p fn-xcs)
                 (natp p) (natp end) (natp decoded))
            (xcs5-decoded-stale-row from ledger file eoff elen poff compressed trailer decoded dict-id p end
                                    fn-xcs fn-xcc fn-xcw fn-ew-span)
          (mv :miss 0 fn-ew-span))
        (if (equal word :span)
            (mv-let (touch fn-xcs fn-xcc) (fn-xc-touch from fn-xcs fn-xcc)
              (declare (ignore touch))
              (mv :span (- j p) from fn-ew-span fn-xcs fn-xcc))
          (xcs5-decoded-stale-row-mutant (1+ from) ledger file eoff elen poff compressed trailer decoded dict-id p end
                                fn-xcs fn-xcc fn-xcw fn-ew-span)))
    (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc)))

(defun xcs5-decoded-first-candidate-mutant (from ledger file eoff elen poff compressed trailer decoded dict-id p end
                                 fn-xcs fn-xcc fn-xcw fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                              (natp from) (natp p) (natp end) (natp decoded))
                  
                  :verify-guards nil))
  (if (and (fn-xc-readyp fn-xcs fn-xcc) (natp from) (< from (fn-xcs-count fn-xcs)))
      (mv-let (word j fn-ew-span)
        (if (and (fn-xc-slot-matchp from nil 3 file eoff elen poff compressed decoded dict-id trailer p fn-xcs)
                 (natp p) (natp end) (natp decoded))
            (fn-xc-decoded-span-row from ledger file eoff elen poff compressed trailer decoded dict-id p end
                                    fn-xcs fn-xcc fn-xcw fn-ew-span)
          (mv :miss 0 fn-ew-span))
        (if (equal word :span)
            (mv-let (touch fn-xcs fn-xcc) (fn-xc-touch from fn-xcs fn-xcc)
              (declare (ignore touch))
              (mv :span (- j p) from fn-ew-span fn-xcs fn-xcc))
          (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc)))
    (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc)))


(set-ignore-ok t)
(defmacro xcs5-ground (name bindings claim)
  `(make-event
    (mv-let (bad term) (fn-dt-translate ',claim (w state))
      (mv-let (badb alist) (fn-dt-bindings-alist ',bindings (w state))
        (if (or bad badb) (er soft 'xcs5-ground "Witness translation failed")
          (value (list 'defthm ',name (fn-dt-subst term alist) :rule-classes nil
            :hints '(("Goal" :expand ((:free (n ledger slots entries) (fn-xce-funded-through n ledger slots entries)) (:free (i ledger slots entries) (fn-xce-row-fundedp i ledger slots entries)) (:free (ledger worker token z i fn-ew-buffer) (fn-pwz-byte ledger worker token z i fn-ew-buffer)) (:free (ledger worker token z file eoff elen poff compressed trailer decoded dict-id i fn-ew-buffer) (fn-pwz-byte-at ledger worker token z file eoff elen poff compressed trailer decoded dict-id i fn-ew-buffer)) (:free (ledger token file eoff elen poff compressed trailer decoded dict-id i
                                    fn-ew-buffer) (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed trailer decoded dict-id i
                                    fn-ew-buffer)) (:free (slot ledger file eoff elen poff compressed trailer decoded dict-id p end
                                  fn-xcs fn-xcc fn-xcw fn-ew-span) (fn-xc-decoded-span-row slot ledger file eoff elen poff compressed trailer decoded dict-id p end
                                  fn-xcs fn-xcc fn-xcw fn-ew-span)) (:free (from ledger file eoff elen poff compressed trailer decoded dict-id p end
                                 fn-xcs fn-xcc fn-xcw fn-ew-span) (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end
                                 fn-xcs fn-xcc fn-xcw fn-ew-span)) (:free (src count dst fn-xce-entry fn-ew-span) (fn-xce-copy src count dst fn-xce-entry fn-ew-span)) (:free (slot file eoff elen poff plen trailer p end fn-xcs fn-xce fn-ew-span) (fn-xc-entry-span-row slot file eoff elen poff plen trailer p end fn-xcs fn-xce fn-ew-span)) (:free (from file eoff elen poff plen trailer p end fn-xcs fn-xcc fn-xce fn-ew-span) (fn-xc-entry-span-at from file eoff elen poff plen trailer p end fn-xcs fn-xcc fn-xce fn-ew-span)) (:free (p end plen start count) (fn-xc-span-end p end plen start count)) (:free (slot ledger file eoff elen poff plen trailer p end
                            fn-xcs fn-xcc fn-xcw fn-ew-span) (fn-xc-span-row slot ledger file eoff elen poff plen trailer p end
                            fn-xcs fn-xcc fn-xcw fn-ew-span)) (:free (from ledger file eoff elen poff plen trailer p end
                         fn-xcs fn-xcc fn-xcw fn-ew-span) (fn-xc-span-at from ledger file eoff elen poff plen trailer p end
                         fn-xcs fn-xcc fn-xcw fn-ew-span)) (:free (src count dst fn-ew-buffer fn-xcw-win) (fn-xcw-copy src count dst fn-ew-buffer fn-xcw-win)) (:free (ledger worker token z i j fn-ew-buffer fn-ew-span) (fn-pwz-span ledger worker token z i j fn-ew-buffer fn-ew-span)) (:free (ledger worker token z file eoff elen poff compressed trailer decoded
                              dict-id i j fn-ew-buffer fn-ew-span) (fn-pwz-span-at ledger worker token z file eoff elen poff compressed trailer decoded
                              dict-id i j fn-ew-buffer fn-ew-span)) (:free (ledger worker token file eoff elen poff compressed trailer decoded dict-id
                              i j fn-decoded-job fn-ew-span) (fn-dwj-span-at ledger worker token file eoff elen poff compressed trailer decoded dict-id
                              i j fn-decoded-job fn-ew-span)) (:free (ledger token file eoff elen poff compressed trailer decoded dict-id
                                    i j fn-ew-buffer fn-ew-span) (fn-pwz-cache-span-at ledger token file eoff elen poff compressed trailer decoded dict-id
                                    i j fn-ew-buffer fn-ew-span)) (:free (src count dst fn-ew-buffer fn-ew-span) (fn-pwr-span-copy src count dst fn-ew-buffer fn-ew-span)) (:free (ledger worker token s i j fn-ew-buffer fn-ew-span) (fn-pwr-span ledger worker token s i j fn-ew-buffer fn-ew-span)) (:free (ledger worker token s file eoff elen poff plen trailer i j
                              fn-ew-buffer fn-ew-span) (fn-pwr-span-at ledger worker token s file eoff elen poff plen trailer i j
                              fn-ew-buffer fn-ew-span)) (:free (ledger token s file eoff elen poff plen trailer i j
                              fn-ew-buffer fn-ew-span) (fn-pwc-span-at ledger token s file eoff elen poff plen trailer i j
                              fn-ew-buffer fn-ew-span))) :in-theory
              (union-theories (enable fn-xc-slot-token fn-xc-token fn-xc-touch fn-xc-next-stamp
                fn-xcs-get-kind-is-nth fn-xcs-get-tokp-is-nth fn-xcs-get-tid-is-nth fn-xcs-get-tcid-is-nth
                fn-xcs-get-file-is-nth fn-xcs-get-eoff-is-nth fn-xcs-get-elen-is-nth fn-xcs-get-a-is-nth
                fn-xcs-get-b-is-nth fn-xcs-get-c-is-nth fn-xcs-get-d-is-nth fn-xcs-get-start-is-nth
                fn-xcs-get-trailer-is-nth fn-xcs-count-is-len fn-xcs-get-stamp-is-nth nth)
                (executable-counterpart-theory :here)))))))))))

(defun-nx xcs5-entry-keep-victim-mutant (ledger file eoff elen trailer token slots cells entries stage)
  (if (not (and token (posp (len stage)) (<= (len stage) (fn-xce-cached-charge ledger token))))
      (list :refused-entry-charge nil nil slots cells entries stage)
    (fn-xc-install-entry-bytes file eoff elen trailer token slots cells entries stage)))
