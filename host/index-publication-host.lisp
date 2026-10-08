(in-package "ACL2")
(logic)
(include-book "../books/owner-report-owner-accessors")
(include-book "../books/owner-node-secret-accessor")
(include-book "../books/msgid-pages-exec")
(include-book "../books/index-backing-writer")
(include-book "query-publication-arena-host")

; Reads the actual owner transition outputs and PreparedCommit, never a host
; supplied frontier/version/pending tuple. The decision index is distinct
; from its scalar visibility version and from the article-only catalog count.
(defun fn-owner-index-source (state)
 (declare (xargs :stobjs state :guard t))
 (if (and (f-boundp-global 'fn-owner state)
          (f-boundp-global 'fn-owner-cat-pending state))
     (let* ((owner (fn-ocfg-owner (f-get-global 'fn-owner state)))
            (view (fn-own-view owner)))
       (mv :current (f-get-global 'fn-owner-cat-pending state)
           (fn-sf-frontier (fn-sn-files (fn-own-store owner)))
           (fn-own-view-version view) view))
   (mv :unavailable nil nil nil nil)))

; The actual generation key originates in the maintained owner's current
; node-secret entry. It is never a native key-generation setter. Purpose KDF
; execution belongs in the funded writer quantum, not a query's hot capture.
(defun fn-owner-index-key (state)
 (declare (xargs :stobjs state :guard t))
 (if (not (f-boundp-global 'fn-owner state))
     (mv :unavailable nil)
   (let* ((owner (fn-ocfg-owner (f-get-global 'fn-owner state)))
          (entry (fn-ns-current (fn-own-node-secret owner))))
    (if (not (fn-ns-entryp entry))
        (mv :recovery-required nil)
      (mv :key (fn-mpxt-key-of-entry entry))))))

; Private durable-finish join. The native completion caller must call this
; only after its actual owner replacement, before clearing PreparedCommit.
; No native caller can supply a publication, root, frontier or visibility.
(defun fn-owner-index-publication-complete (fuel fn-mio$c state)
 (declare (xargs :stobjs (fn-mio$c state) :guard (natp fuel)))
 (mv-let (source pc frontier version visibility) (fn-owner-index-source state)
  (if (not (eq source :current))
      (mv :unavailable fuel fn-mio$c)
    (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
     (status remaining fn-index-backing)
     (fn-ibp-writer-complete pc frontier version visibility fuel fn-index-backing)
     (mv status remaining fn-mio$c)))))

; The writer token originates in the current registered builder, never in a
; native argument. The actual arena adapter obtains incarnation/prefix from
; STATE and arena, and increments the maintained publication hold exactly
; once. An escaped child transition without its builder marker is fenced.
(defun fn-owner-index-writer-arena-capture (fuel fn-mio$c fn-arena state)
 (declare (xargs :stobjs (fn-mio$c fn-arena state) :guard (natp fuel)
                 :verify-guards nil))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (phase token)
  (let ((builder (fn-ibp-builder fn-index-backing)))
   (mv (fn-omk-at 1 builder) (fn-omk-at 2 builder)))
  (cond
   ((not (fn-ibp-generation-tokenp token)) (mv :stale fuel fn-mio$c))
   ((eq phase :arena-held) (mv :arena-held fuel fn-mio$c))
   ((not (eq phase :registered)) (mv :recovery-required fuel fn-mio$c))
   (t
    (mv-let (word remaining fn-mio$c)
     (fn-owner-index-publication-arena-capture token fuel fn-mio$c fn-arena state)
     (if (not (eq word :captured))
         (mv (if (eq word :stale) :recovery-required word) remaining fn-mio$c)
       (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
        (status fn-index-backing)
        (let ((builder (fn-ibp-builder fn-index-backing)))
         (if (not (and (fn-omk-widthp builder 20) (true-listp builder)
                       (eq (fn-omk-at 1 builder) :registered)
                       (equal (fn-omk-at 2 builder) token)))
             (mv :recovery-required fn-index-backing)
           (let ((fn-index-backing
                   (update-fn-ibp-builder (update-nth 1 :arena-held builder) fn-index-backing)))
            (mv :arena-held fn-index-backing))))
        (mv status remaining fn-mio$c))))))))

(verify-guards fn-owner-index-writer-arena-capture
 :hints (("Goal" :in-theory (disable fn-owner-index-publication-arena-capture fn-mio$cp
                                    fn-index-backingp fn-ibp-nodep))))
