; fn: the exec open of the paged checkpoint (lane s-pck-host, 2026-10-07;
; STORAGE-PROGRAM-20261006.md section 3.3, phase 2c-1).  STATEMENT FIRST: the
; refinement below is the contract; the proof follows in this file.
;
; The model.  `fn-pck-capture-of-pages' (paged-checkpoint.lisp) decodes a page
; list into a capture C: the records (wire trees) from the events tape, the
; four fold roots (cpr, identity, consumer, topic) from the root region, the
; event index rebuilt from the records.  The host does not hold trees: it
; holds ROWS interned in the payload arena (books/store-intern.lisp,
; `fn-row-wire-of' reads a row's wire back) and the four roots.
;
; The exec.  `fn-pck-x-open' reads the image in `pgs-mem' (pages already
; filled and verified, flags 2) word by word at tape positions, one record at
; a time: the tag word 1, the octet count, the packed octets into the
; `fn-octets' buffer (no page list, no whole-tape word list; a record that
; crosses a page boundary is read through the contiguous word array), decodes
; the record's tree from the buffer, and interns it with `fn-ssr-intern-step'
; (:resident mode) into `fn-arena', until a word that is not the tag.  The root
; region is read the same way from words 0 .. 8*2048.  Answer:
; (mv VERDICT ROWS ROOTS INDEX fn-octets fn-arena), VERDICT :ok or a refusal
; by name (:root, :record, :intern).
;
; THE STATEMENT (to be proved as `fn-pck-x-open-is-the-capture-of-pages'):
;
;   (let* ((pages (fn-pck-pages configs recs))
;          (c (fn-pck-capture-of-pages pages))
;          (r (fn-pck-x-open pgs-mem fn-arena fn-octets)))
;     (implies
;       (and (fn-pck-recordsp configs recs)            ; encodable trees, as the writer needs
;            (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows recs))
;            (fn-pck-root-fitsp configs recs)
;            ;; the image holds exactly those pages, filled and verified
;            (equal (pgs-x-words 0 0 (* 2048 (len pages)) pgs-mem) (adt-tp-flat pages))
;            (pcki-resident 0 (len pages) pgs-mem)
;            (<= (len pages) (pgs-v-length pgs-mem))
;            ;; the arena is fresh, and the records intern from the seed
;            (equal (fn-arena-count fn-arena) 0)
;            (not (eq (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed (nth 1 (fn-pck-root-tree configs recs)))
;                                                   recs nil nil :resident nil fn-arena))
;                     :bad)))
;       (and (equal (nth 0 r) :ok)
;            ;; the arena records ARE the capture's records
;            (equal (fn-rows-wire-of (nth 1 r) (nth 5 r)) (fn-sco-records c))
;            ;; the four tables
;            (equal (nth 2 r) (list (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c) (fn-sco-topic c)))
;            ;; the event index
;            (equal (nth 3 r) (fn-sco-event-index c)))))
;
; and the exec reads each tape word once, in order: the pages touched are the
; tape's pages and the root's, no more (`fn-pck-x-open-reads', a bound on the
; words read: 8*2048 + the tape's word count + 2).
;
; Premise inhabitation: tests/acl2/paged-checkpoint-open-tests.lisp builds the
; image of a ground (configs, recs) with the step-1 staging and runs the open on
; it (:ok, rows read back equal to recs, roots equal).
; Tooth (must-fail): the same statement without `fn-pck-recordsp' (a record
; the codec cannot encode decodes to NIL in the model, the exec refuses it).
