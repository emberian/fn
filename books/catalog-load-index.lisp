; fn: the catalog loaded from the checkpoint's P extents (lane open-by-index,
; 2026-09-26; the consolidation design 2.1 "the reader loads P into the
; arena ... E into the catalog"; PRF-240's second part; entry E3 of R,
; books/catalog-entries.lisp).
;
; THE INTERFACE records-freeze attaches its arena behind (the coordinator's
; direction, 2026-09-27): `fn-obi-seal-range' seals the octet buffer's cells
; [A, B) as ONE payload.  Today it is the thin wrapper over the arena's list
; seal of the slice (`fn-obi-seal-range-is-seal-of-slice'); an implementation
; that copies the cells without a list keeps that theorem and nothing else
; here changes.
;
; THE LOAD `fn-obi-load': each E row in order; an article row is interned
; with its payload SEALED FROM ITS P EXTENT in the buffer (never from the
; row's own payload list) and committed; every other kind skipped, as
; `fn-cat-load' does.  KEYSTONE `fn-obi-load-is-cat-load': when every
; article row's payload is the buffer's slice at its extent
; (`fn-obi-extents-agreep': what the schema-3 reader's ref op restores, P[s]
; at the row's payload leaf), the load by extents IS `fn-cat-load' over the
; rows, from any state, under any keyring and generation; so with
; `fn-sca-ocl-relation-at-recover' (books/served-catalog-owner.lisp) the catalog
; the E3 entry installs by extents is in R.  OPEN (PKT-680): discharging the
; agreement from the reader (the P run's extents by index against
; `fn-sct-load's rows) and the host call (no served arm reads the catalog
; yet: catalog-slice-5 step 7b/8).

(in-package "ACL2")
(include-book "catalog-relation")
(include-book "octets-stobj")

; -----------------------------------------------------------------------------
; The interface: seal the buffer's cells [A, B) as one payload.

(defun fn-obi-seal-range (a b fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
  (fn-arena-seal-list (fn-oct-slice-list a b fn-octets) fn-arena))

(defthm fn-obi-seal-range-is-seal-of-slice
  (equal (fn-obi-seal-range a b fn-octets fn-arena)
         (fn-arena-seal-list (fn-oct-slice-list a b fn-octets) fn-arena)))

(in-theory (disable fn-obi-seal-range))

; -----------------------------------------------------------------------------
; Intern from an extent: the row's metadata, the extent's bytes.

(defun fn-obi-intern-range (w a b fn-octets keyring generation fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
  (let* ((bytes (fn-oct-slice-list a b fn-octets))
         (h (fn-arena-count fn-arena))
         (fn-arena (fn-obi-seal-range a b fn-octets fn-arena)))
    (mv (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                      (fn-record-generation w) (fn-record-msgid w) h
                      (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
                      (fn-held-facts-of bytes)
                      (fn-held-context-of bytes keyring generation)
                      nil nil (fn-record-binding w))
        fn-arena)))

(defthm fn-obi-intern-range-is-intern-list
  (implies (equal (fn-record-payload w) (fn-oct-slice-list a b fn-octets))
           (equal (fn-obi-intern-range w a b fn-octets keyring generation fn-arena)
                  (fn-cat-intern-list w keyring generation fn-arena)))
  :hints (("Goal" :in-theory (enable fn-cat-intern-list))))

(in-theory (disable fn-obi-intern-range))

; -----------------------------------------------------------------------------
; The load by extents.  EXTENTS has one (A . B) per row, in row order.

(defun fn-obi-load (rows extents fn-octets keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil))
  (if (consp rows)
      (if (fn-record-p (car rows))
          (mv-let (held fn-arena)
            (fn-obi-intern-range (car rows) (nfix (car (car extents)))
                                 (nfix (cdr (car extents))) fn-octets keyring
                                 generation fn-arena)
            (let ((fn-cat (fn-cat-commit held fn-cat)))
              (fn-obi-load (cdr rows) (cdr extents) fn-octets keyring generation
                           fn-arena fn-cat)))
        (fn-obi-load (cdr rows) (cdr extents) fn-octets keyring generation
                     fn-arena fn-cat))
    (mv fn-arena fn-cat)))

(defun fn-obi-extents-agreep (rows extents fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (if (consp rows)
      (and (or (not (fn-record-p (car rows)))
               (equal (fn-record-payload (car rows))
                      (fn-oct-slice-list (nfix (car (car extents)))
                                         (nfix (cdr (car extents))) fn-octets)))
           (fn-obi-extents-agreep (cdr rows) (cdr extents) fn-octets))
    t))

(defthm fn-obi-load-is-cat-load
  (implies (fn-obi-extents-agreep rows extents fn-octets)
           (equal (fn-obi-load rows extents fn-octets keyring generation fn-arena fn-cat)
                  (fn-cat-load rows keyring generation fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-obi-load rows extents fn-octets keyring generation fn-arena fn-cat)
           :in-theory (enable fn-cat-load fn-cat-load-row))))

; With books/catalog-relation's fold keystone: the load by extents from the
; creators establishes R over the rows.
(defthm fn-obi-load-from-empty-establishes-relation
  (implies (and (fn-obi-extents-agreep rows extents fn-octets)
                (natp generation))
           (mv-let (fn-arena2 fn-cat2)
             (fn-obi-load rows extents fn-octets keyring generation
                          (create-fn-arena) (create-fn-cat))
             (fn-cat-history-relation rows fn-arena2 fn-cat2)))
  :hints (("Goal" :use ((:instance fn-cat-load-from-empty (records rows)))
           :in-theory (disable fn-cat-load fn-obi-load fn-cat-history-relation))))
