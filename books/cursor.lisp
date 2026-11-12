; The query cursor machine fn2-cursor (layer D, quest D6; docs/d-machines-
; nntp.md section 15), the first kind written in the machine form's child form
; (MACHINE-FORM 6.10): its arms are generated and proved here over its table,
; the five arm children and the children of the operations it calls (C-S4's
; reads, the pool); their core faces are made in its callbacks section
; (assembly-callbacks-d-cursor.lisp).
;
; A connection that frames a reader command (GROUP, LISTGROUP, NEXT, LAST,
; STAT, OVER, XOVER) moves to :query and takes a cursor row, copying the
; line's place in RX, its TX range, its selection (group, current article,
; view) and its own owner triple. The cursor reads the line, reads the store
; through read row X = its own slot (C-S4), and renders the reply into the
; connection's TX under the connection's owner (the connection does not
; touch TX or RX while it is in :query), one page at a time. TURN says whose
; move it is: the cursor clears it and wakes the connection when a page is
; ready (ROFF: where the page starts); the connection sends the page and sets
; it again, waking the cursor, which renders the next page or, once DONE,
; finishes. The selection the reply moves to (UPDATE, SEL, NCURRENT, SVIEW)
; is copied back by the connection after the last page. CANCEL is the
; connection's: set when it drains with a cursor waiting.
(in-package "ACL2")
(include-book "cursor-kind")
(include-book "article-manifest")
(fn2-book-layer :d)

(defconst *fn2-cursor-overview-sid* 3)
;; A page breaks before a row when TX has less room than a number, a TAB, a
;; first piece of the line and CR LF (a row is then split across pages).
(defconst *fn2-cursor-row-room* 64)
;; NEXT, LAST, STAT copy the line up to its Message-ID with room left for
;; the 223 line after it (3 + 20 + 250 + 10 + CR LF).
(defconst *fn2-cursor-single-room* 300)
;; Range and identity steps: pool reads a step.
(defconst *fn2-cursor-step-budget* 4096)
;; A whole-schema scan (LIST, LISTGROUP with no name) saves its resume key at
;; the front of TX, which the connection keeps across the scan's pages: the
;; pages start after this key area (a group name is at most 250 octets).
(defconst *fn2-cursor-key-room* 256)
(assert-event (< *fn2-groups-name-max* *fn2-cursor-key-room*))
;; A LIST row: a name, three numbers, the status, their spaces and CR LF.
(defconst *fn2-cursor-list-room* 336)
(assert-event (<= (+ *fn2-groups-name-max* 3 (* 3 21) 4) *fn2-cursor-list-room*))
;; LIST's variants (the grammar's keyword order) the cursor serves.
(defconst *fn2-cursor-list-active* 0)
(defconst *fn2-cursor-list-times* 1)
(defconst *fn2-cursor-list-counts* 2)
(defconst *fn2-cursor-list-newsgroups* 7)
(defconst *fn2-cursor-list-subscriptions* 9)
;; HDR/XHDR and NEWNEWS: room in TX before reading an overview line to
;; extract a header field or Message-ID.
(defconst *fn2-cursor-hdr-room* 512)
;; Stored octets copied onto the wire per run (one storage unit).
(defconst *fn2-cursor-stuff-bytes* 4096)
;; Argument kinds after the parse: absent, a number or range (A..B), a
;; Message-ID or a token (the span A, length B in RX).
(defconst *fn2-cursor-arg-none* 0)
(defconst *fn2-cursor-arg-range* 1)
(defconst *fn2-cursor-arg-span* 2)
(defconst *fn2-cursor-arg-keyword* 3)

; ---------------------------------------------------------------------------
; Pure helpers over the command tag.
(defun fn2-cursor-selects-p (tag)
  (declare (xargs :guard t))
  (or (equal tag *fn2-nntp-command-group*) (equal tag *fn2-nntp-command-listgroup*)))
(defun fn2-cursor-overview-p (tag)
  (declare (xargs :guard t))
  (or (equal tag *fn2-nntp-command-over*) (equal tag *fn2-nntp-command-xover*)))
(defun fn2-cursor-hdr-p (tag)
  (declare (xargs :guard t))
  (or (equal tag *fn2-nntp-command-hdr*) (equal tag *fn2-nntp-command-xhdr*)
      (equal tag *fn2-nntp-command-xpat*)))
;; The reply a tag gives for WHAT (a keyword); 0 (no reply) when it has none.
(defun fn2-cursor-reply-of (tag what)
  (declare (xargs :guard t))
  (cond
   ((equal tag *fn2-nntp-command-group*)
    (case what (:selected *fn2-nntp-reply-group-selected*) (:no-group *fn2-nntp-reply-group-no-group*)
      (otherwise *fn2-nntp-reply-group-no-projection*)))
   ((equal tag *fn2-nntp-command-listgroup*)
    (case what (:selected *fn2-nntp-reply-listgroup-listed*) (:no-group *fn2-nntp-reply-listgroup-no-group*)
      (:no-group-selected *fn2-nntp-reply-listgroup-no-group-selected*)
      (otherwise *fn2-nntp-reply-listgroup-no-projection*)))
   ((equal tag *fn2-nntp-command-next*)
    (case what (:found *fn2-nntp-reply-next-moved*) (:no-group-selected *fn2-nntp-reply-next-no-group-selected*)
      (:no-current *fn2-nntp-reply-next-no-current*) (:none *fn2-nntp-reply-next-no-next*)
      (otherwise *fn2-nntp-reply-next-no-projection*)))
   ((equal tag *fn2-nntp-command-last*)
    (case what (:found *fn2-nntp-reply-last-moved*) (:no-group-selected *fn2-nntp-reply-last-no-group-selected*)
      (:no-current *fn2-nntp-reply-last-no-current*) (:none *fn2-nntp-reply-last-no-previous*)
      (otherwise *fn2-nntp-reply-last-no-projection*)))
   ((equal tag *fn2-nntp-command-stat*)
    (case what (:found *fn2-nntp-reply-stat-sent*) (:no-group-selected *fn2-nntp-reply-stat-no-group-selected*)
      (:no-current *fn2-nntp-reply-stat-no-current*) (:none *fn2-nntp-reply-stat-no-number*)
      (:no-msgid *fn2-nntp-reply-stat-no-msgid*)
      (otherwise *fn2-nntp-reply-stat-no-projection*)))
   ((equal tag *fn2-nntp-command-article*)
    (case what (:found *fn2-nntp-reply-article-sent*) (:no-group-selected *fn2-nntp-reply-article-no-group-selected*)
      (:no-current *fn2-nntp-reply-article-no-current*) (:none *fn2-nntp-reply-article-no-number*)
      (:no-msgid *fn2-nntp-reply-article-no-msgid*)
      (otherwise *fn2-nntp-reply-article-no-projection*)))
   ((equal tag *fn2-nntp-command-head*)
    (case what (:found *fn2-nntp-reply-head-sent*) (:no-group-selected *fn2-nntp-reply-head-no-group-selected*)
      (:no-current *fn2-nntp-reply-head-no-current*) (:none *fn2-nntp-reply-head-no-number*)
      (:no-msgid *fn2-nntp-reply-head-no-msgid*)
      (otherwise *fn2-nntp-reply-head-no-projection*)))
   ((equal tag *fn2-nntp-command-body*)
    (case what (:found *fn2-nntp-reply-body-sent*) (:no-group-selected *fn2-nntp-reply-body-no-group-selected*)
      (:no-current *fn2-nntp-reply-body-no-current*) (:none *fn2-nntp-reply-body-no-number*)
      (:no-msgid *fn2-nntp-reply-body-no-msgid*)
      (otherwise *fn2-nntp-reply-body-no-projection*)))
   ((equal tag *fn2-nntp-command-over*)
    (case what (:found *fn2-nntp-reply-over-overview*) (:no-group-selected *fn2-nntp-reply-over-no-group-selected*)
      (:no-current *fn2-nntp-reply-over-no-current*) (:none *fn2-nntp-reply-over-empty-range*)
      (:no-msgid *fn2-nntp-reply-over-no-msgid*)
      (otherwise *fn2-nntp-reply-over-no-projection*)))
   ((equal tag *fn2-nntp-command-list*)
    (case what (:newsgroups *fn2-nntp-reply-list-newsgroups*)
      (:times *fn2-nntp-reply-list-times*)
      (:subscriptions *fn2-nntp-reply-list-subscriptions*)
      (:active *fn2-nntp-reply-list-active*)
      (otherwise *fn2-nntp-reply-list-no-projection*)))
   ((equal tag *fn2-nntp-command-xover*)
    (case what (:found *fn2-nntp-reply-xover-overview*) (:no-group-selected *fn2-nntp-reply-xover-no-group-selected*)
      (:no-current *fn2-nntp-reply-xover-no-current*) (:none *fn2-nntp-reply-xover-none-selected*)
      (otherwise *fn2-nntp-reply-xover-no-projection*)))
   ((equal tag *fn2-nntp-command-hdr*)
    (case what (:found *fn2-nntp-reply-hdr-headers*) (:no-group-selected *fn2-nntp-reply-hdr-no-group-selected*)
      (:no-current *fn2-nntp-reply-hdr-no-current*) (:none *fn2-nntp-reply-hdr-empty-range*)
      (:no-msgid *fn2-nntp-reply-hdr-no-msgid*)
      (otherwise *fn2-nntp-reply-hdr-no-projection*)))
   ((equal tag *fn2-nntp-command-xhdr*)
    (case what (:found *fn2-nntp-reply-xhdr-header*) (:no-group-selected *fn2-nntp-reply-xhdr-no-group-selected*)
      (:no-current *fn2-nntp-reply-xhdr-no-current*) (:none *fn2-nntp-reply-xhdr-none-selected*)
      (:no-msgid *fn2-nntp-reply-xhdr-no-msgid*)
      (otherwise *fn2-nntp-reply-xhdr-no-projection*)))
   ((equal tag *fn2-nntp-command-xpat*)
    (case what (:found *fn2-nntp-reply-xpat-header*) (:no-group-selected *fn2-nntp-reply-xpat-no-group-selected*)
      (:no-msgid *fn2-nntp-reply-xpat-no-msgid*)
      (otherwise *fn2-nntp-reply-xpat-no-projection*)))
   ((equal tag *fn2-nntp-command-xfn-zarticle*)
    (case what (:found *fn2-nntp-reply-xfn-zarticle-sent*) (:no-msgid *fn2-nntp-reply-xfn-zarticle-no-msgid*)
      (otherwise *fn2-nntp-reply-xfn-zarticle-no-projection*)))
   ((equal tag *fn2-nntp-command-newgroups*)
    (case what (:listed *fn2-nntp-reply-newgroups-listed*)
      (otherwise *fn2-nntp-reply-newgroups-no-projection*)))
   ((equal tag *fn2-nntp-command-newnews*)
    (case what (:listed *fn2-nntp-reply-newnews-listed*)
      (otherwise *fn2-nntp-reply-newnews-no-projection*)))
   ((equal tag *fn2-nntp-command-check*)
    (case what (:wanted *fn2-nntp-reply-check-wanted*) (:not-wanted *fn2-nntp-reply-check-not-wanted*)
      (otherwise *fn2-nntp-reply-check-later*)))
   ((equal tag *fn2-nntp-command-ihave*)
    (case what (:not-wanted *fn2-nntp-reply-ihave-duplicate*)
      (otherwise *fn2-nntp-reply-ihave-retry*)))
   (t 0)))
;; NEXT, LAST, STAT, ARTICLE, HEAD, BODY, and XFN-ZARTICLE: one article.
(defun fn2-cursor-single-p (tag)
  (declare (xargs :guard t))
  (or (equal tag *fn2-nntp-command-next*) (equal tag *fn2-nntp-command-last*) (equal tag *fn2-nntp-command-stat*)
      (equal tag *fn2-nntp-command-article*) (equal tag *fn2-nntp-command-head*) (equal tag *fn2-nntp-command-body*)
      (equal tag *fn2-nntp-command-xfn-zarticle*)))
;; LIST's variant: its keyword's, ACTIVE when none.
(defun fn2-cursor-list-variant (k0 a0)
  (declare (xargs :guard t))
  (if (equal k0 *fn2-cursor-arg-keyword*) (nfix a0) *fn2-cursor-list-active*))
(defun fn2-cursor-list-reply (k0 a0)
  (declare (xargs :guard t))
  (let ((v (fn2-cursor-list-variant k0 a0)))
    (cond ((equal v *fn2-cursor-list-newsgroups*) *fn2-nntp-reply-list-newsgroups*)
          ((equal v *fn2-cursor-list-times*) *fn2-nntp-reply-list-times*)
          ((equal v *fn2-cursor-list-subscriptions*) *fn2-nntp-reply-list-subscriptions*)
          (t *fn2-nntp-reply-list-active*))))
(defcost fn2-cursor-list-variant :child fn2-cursor-list-variant :doc "LIST's variant (ACTIVE when no keyword).")
(defcost fn2-cursor-list-reply :child fn2-cursor-list-reply :doc "The 215 reply for a LIST variant.")
(defcost fn2-cursor-selects-p :child fn2-cursor-selects-p :doc "GROUP or LISTGROUP.")
(defcost fn2-cursor-overview-p :child fn2-cursor-overview-p :doc "OVER or XOVER.")
(defcost fn2-cursor-hdr-p :child fn2-cursor-hdr-p :doc "HDR or XHDR.")
(defcost fn2-cursor-single-p :child fn2-cursor-single-p :doc "NEXT, LAST or STAT.")
(defcost fn2-cursor-reply-of :child fn2-cursor-reply-of :doc "The reply a command tag gives for an outcome.")
(defthm fn2-cursor-reply-of-natp (natp (fn2-cursor-reply-of tag what)) :rule-classes :type-prescription)
(defthm fn2-cursor-list-reply-natp (natp (fn2-cursor-list-reply k0 a0)) :rule-classes :type-prescription)
(in-theory (disable fn2-cursor-reply-of fn2-cursor-list-reply))

; ---------------------------------------------------------------------------
; The cursor's pool operations, over fn2-pool only. Each writes at TX's fill
; (the typed renderer and fn2-gram-put append) under the owner it is given.

;; The line [s, e) of RX, parsed again: (mv code tag k0 a0 b0 k1 a1 b1), each
;; argument as its kind (*fn2-cursor-arg-...*) and its two values.
(defun fn2-cursor-arg-kind (f)
  (declare (xargs :guard t))
  (cond ((member-eq f '(:number :range)) *fn2-cursor-arg-range*)
        ((eq f :span) *fn2-cursor-arg-span*)
        ((eq f :keyword) *fn2-cursor-arg-keyword*)
        (t *fn2-cursor-arg-none*)))
(defun fn2-cursor-parse-line (s e mask slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp s) (natp e))))
  (mv-let (code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3)
    (fn2-nntp-parse-line s e mask slot gen okind oslot ogen fn2-pool)
    (declare (ignore nargs f3 a3 b3))
    (let ((ok (and (eq code :ok) (natp tag) (< tag 256))))
      (mv (if ok :ok :refused) (if ok tag 0)
          (fn2-cursor-arg-kind f0) (nfix a0) (if (eq f0 :number) (nfix a0) (nfix b0))
          (fn2-cursor-arg-kind f1) (nfix a1) (if (eq f1 :number) (nfix a1) (nfix b1))
          (nfix a2) (if (eq f2 :number) (nfix a2) (nfix b2))))))

;; TX's fill, 0 for a slot out of range.
(defun fn2-cursor-pool-fill (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-fill slot fn2-pool)) 0))

;; One typed status line (the grammar's renderer). ARTICLE, HEAD and BODY
;; follow it with the stored octets (fn2-cursor-stuff, after B's block read).
(local (in-theory (disable fn2-gram-find fn2-gram-digits)))
;; Spans of an overview line (HDR, NEWNEWS): its next TAB and LF.
(defun fn2-cursor-span-len (from to)
  (declare (xargs :guard t))
  (nfix (- (nfix to) (nfix from))))
(defthm fn2-cursor-span-len-natp (natp (fn2-cursor-span-len from to)) :rule-classes :type-prescription)
(in-theory (disable fn2-cursor-span-len))
(defun fn2-cursor-next-tab (from to slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp from) (natp to))))
  (fn2-gram-find (fn2-cursor-span-len from to) from 9 slot gen okind oslot ogen fn2-pool))
(defthm fn2-cursor-next-tab-natp
  (natp (mv-nth 1 (fn2-cursor-next-tab from to slot gen okind oslot ogen fn2-pool)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-cursor-next-tab))
(defun fn2-cursor-next-lf (from to slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp from) (natp to))))
  (fn2-gram-find (fn2-cursor-span-len from to) from 10 slot gen okind oslot ogen fn2-pool))
(defthm fn2-cursor-next-lf-natp
  (natp (mv-nth 1 (fn2-cursor-next-lf from to slot gen okind oslot ogen fn2-pool)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-cursor-next-lf))
(defun fn2-cursor-render (cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n0) (natp n1) (natp n2) (natp soff) (natp slen))
                  :guard-hints (("Goal" :in-theory (disable fn2-nntp-reply-template fn2-nntp-reply-admitted
                                                            fn2-nntp-reply-command fn2-nntp-reply-layer)))))
  (fn2-nntp-render cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-cursor-render (cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool)
  :position 1 :rows nil
  :hints (("Goal" :in-theory (disable fn2-nntp-reply-template fn2-nntp-reply-admitted
                                      fn2-nntp-reply-command fn2-nntp-reply-layer))))
(in-theory (disable fn2-cursor-render))
;; The stored source, dot-stuffed onto the wire (RFC 3977 3.1.1): the
;; octets [I, I+N) of the cursor's lease (under its own owner OKIND OSLOT OGEN)
;; appended to TX (under the connection's owner TK TS TG), resumable. ST is
;; MODE*4 + BOL*2 + PEND: MODE 0 the whole article, 1 its header (it ends
;; at the empty line), 2 the header skipped before the body, 3 the body;
;; BOL the next octet starts a line; PEND a CR that started a line and is
;; held until the octet after it says whether the line is empty. A line
;; starting with "." gets a second one. An empty line ends HEAD (:end); in
;; BODY it is where the body starts. TX keeps four octets of room (two
;; octets per source octet at most, and the terminator's three): with less,
;; the copy stops (:full) and the page goes. (mv code used st fn2-pool),
;; USED the lease octets consumed.
(defun fn2-cursor-stuff-loop (n i st used lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp i) (natp st) (natp used))))
  (b* ((mode (floor (nfix st) 4)) (bol (logbitp 1 (nfix st))) (pend (logbitp 0 (nfix st)))
       (emit (not (equal mode 2)))
       ((when (zp n)) (mv :ok (nfix used) (nfix st) fn2-pool))
       ((when (< (fn2-pool-slot-capacity tslot fn2-pool) (+ (fn2-gram-fill tslot fn2-pool) 4)))
        (mv :full (nfix used) (nfix st) fn2-pool))
       ((mv ok b) (fn2-gram-read lslot lgen i okind oslot ogen fn2-pool))
       ((unless ok) (mv :fault (nfix used) (nfix st) fn2-pool))
       (used (+ 1 (nfix used))))
    (cond
     ;; a held CR and an LF: the line is empty
     ((and pend (equal b *fn2-gram-lf*))
      (cond ((equal mode 1) (mv :end used (+ 4 2) fn2-pool))
            ((equal mode 2)
             (fn2-cursor-stuff-loop (- n 1) (+ 1 i) (+ 12 2) used lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool))
            (t (b* (((mv code fn2-pool) (fn2-gram-put-crlf tslot tgen tk ts tg fn2-pool))
                    ((unless (eq code :ok)) (mv :fault used (nfix st) fn2-pool)))
                 (fn2-cursor-stuff-loop (- n 1) (+ 1 i) (+ (* 4 mode) 2) used lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)))))
     ;; a CR starting a line: held
     ((and bol (not pend) (equal b *fn2-gram-cr*))
      (fn2-cursor-stuff-loop (- n 1) (+ 1 i) (+ (* 4 mode) 1) used lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool))
     (t (b* (((mv code fn2-pool) (if (and emit pend) (fn2-gram-put *fn2-gram-cr* tslot tgen tk ts tg fn2-pool)
                                   (mv :ok fn2-pool)))
             ((unless (eq code :ok)) (mv :fault used (nfix st) fn2-pool))
             ((mv code fn2-pool) (if (and emit bol (not pend) (equal b *fn2-gram-dot*))
                                     (fn2-gram-put *fn2-gram-dot* tslot tgen tk ts tg fn2-pool)
                                   (mv :ok fn2-pool)))
             ((unless (eq code :ok)) (mv :fault used (nfix st) fn2-pool))
             ((mv code fn2-pool) (if emit (fn2-gram-put b tslot tgen tk ts tg fn2-pool) (mv :ok fn2-pool)))
             ((unless (eq code :ok)) (mv :fault used (nfix st) fn2-pool)))
          (fn2-cursor-stuff-loop (- n 1) (+ 1 i) (+ (* 4 mode) (if (equal b *fn2-gram-lf*) 2 0)) used
                                 lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool))))))
(fn2-pool-preserves fn2-cursor-stuff-loop (n i st used lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)
  :position 3 :rows nil
  :hints (("Goal" :induct (fn2-cursor-stuff-loop n i st used lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)
                  :in-theory (disable fn2-gram-read fn2-gram-fill fn2-gram-put fn2-gram-put-crlf logbitp
                                      fn2-pool-slot-capacity nfix))))
(defun fn2-cursor-pool-stuff (from to st lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp from) (natp to) (natp st))))
  (mv-let (code used st fn2-pool)
    (fn2-cursor-stuff-loop (min *fn2-cursor-stuff-bytes* (nfix (- (nfix to) (nfix from)))) (nfix from) (nfix st) 0
                           lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)
    (mv code (nfix used) (nfix st) fn2-pool)))
(fn2-pool-preserves fn2-cursor-pool-stuff (from to st lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool)
  :position 3 :rows nil)
(defthm fn2-cursor-pool-stuff-used-natp
  (natp (mv-nth 1 (fn2-cursor-pool-stuff from to st lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-cursor-pool-stuff))))
(defthm fn2-cursor-pool-stuff-st-natp
  (natp (mv-nth 2 (fn2-cursor-pool-stuff from to st lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-cursor-pool-stuff))))
(in-theory (disable fn2-cursor-stuff-loop fn2-cursor-pool-stuff))
;; HDR over stored headers (RFC 3977 §8.5): the named field's value read
;; from the article's stored octets, the lease's octets [FROM, TO) scanned
;; one octet per step of a state machine that survives the unit boundary.
;; ST: 0 a line starts, 1 the name matched for K octets, 2 after its colon,
;; 3 the value, 4 a CR in the value, 5 a CR LF in the value (a fold when
;; white space follows), 6 another line, 7 a CR in it, 8 a CR at a line's
;; start (the header block ends at its LF). The first field of the name
;; wins; the value loses one leading space and its folds' CR LF, and TAB,
;; NUL, CR and LF become a space (the NOV transformation). Answers (mv code
;; nst nk consume emit done): EMIT an octet to append or NIL; CONSUME
;; whether the octet is used up (a state that only changes is read again).
(defun fn2-cursor-hscan-step (st k b match b0)
  (declare (xargs :guard (and (natp st) (natp k) (natp b) (natp b0))))
  (let ((cr (equal b *fn2-gram-cr*)) (lf (equal b *fn2-gram-lf*)) (wsp (or (equal b 32) (equal b 9))))
    (case st
      (0 (cond (cr (mv 8 0 t nil nil)) ((and (< 0 b0) match) (mv 1 1 t nil nil)) (t (mv 6 0 t nil nil))))
      (1 (cond ((and (< k b0) match) (mv 1 (+ 1 k) t nil nil))
               ((and (equal k b0) (equal b 58)) (mv 2 0 t nil nil))
               (cr (mv 7 0 t nil nil))
               (t (mv 6 0 t nil nil))))
      (2 (if (equal b 32) (mv 3 0 t nil nil) (mv 3 0 nil nil nil)))
      (3 (cond (cr (mv 4 0 t nil nil)) ((or lf (equal b 9) (equal b 0)) (mv 3 0 t 32 nil)) (t (mv 3 0 t b nil))))
      (4 (if lf (mv 5 0 t nil nil) (mv 3 0 nil 32 nil)))
      (5 (if wsp (mv 3 0 t 32 nil) (mv 5 0 nil nil t)))
      (7 (cond (lf (mv 0 0 t nil nil)) (cr (mv 7 0 t nil nil)) (t (mv 6 0 t nil nil))))
      (8 (if lf (mv 8 0 t nil t) (mv 6 0 nil nil nil)))
      (otherwise (if cr (mv 7 0 t nil nil) (mv 6 0 t nil nil))))))
;; N steps over the lease (LSLOT LGEN, owner OKIND OSLOT OGEN) from octet I
;; to TO, the name the span [A0, A0+B0) of RX (RSLOT RGEN) and the value
;; appended to TX (TSLOT TGEN), both the connection's (TK TS TG). TX keeps
;; three octets of room (the octet and the value's CR LF): with less the
;; scan stops (:full) and the page goes. (mv code used st k fn2-pool):
;; :done once the value (empty when the block ends first) and its CR LF
;; are in TX; :ok when the octets ran out first.
(defun fn2-cursor-hscan-loop (n i to st k used a0 b0 rslot rgen lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp i) (natp to) (natp st) (natp k) (natp used)
                              (natp a0) (natp b0))))
  (b* ((i (nfix i)) (st (nfix st)) (k (nfix k)) (used (nfix used))
       ((when (or (zp n) (>= i (nfix to)))) (mv :ok used st k fn2-pool))
       ((when (< (fn2-pool-slot-capacity tslot fn2-pool) (+ (fn2-gram-fill tslot fn2-pool) 3)))
        (mv :full used st k fn2-pool))
       ((mv ok b) (fn2-gram-read lslot lgen i okind oslot ogen fn2-pool))
       ((unless ok) (mv :fault used st k fn2-pool))
       ((mv okn nb) (if (< k (nfix b0)) (fn2-gram-read rslot rgen (+ (nfix a0) k) tk ts tg fn2-pool) (mv t 0)))
       ((unless okn) (mv :fault used st k fn2-pool))
       (match (and (< k (nfix b0)) (equal (fn2-gram-upcase b) (fn2-gram-upcase nb))))
       ((mv nst nk consume emit done) (fn2-cursor-hscan-step st k b match (nfix b0)))
       (used (if consume (+ 1 used) used))
       ((mv code fn2-pool) (if (natp emit) (fn2-gram-put emit tslot tgen tk ts tg fn2-pool) (mv :ok fn2-pool)))
       ((unless (eq code :ok)) (mv :fault used st k fn2-pool))
       ((when done)
        (b* (((mv code fn2-pool) (fn2-gram-put-crlf tslot tgen tk ts tg fn2-pool)))
          (mv (if (eq code :ok) :done :fault) used (nfix nst) (nfix nk) fn2-pool))))
    (fn2-cursor-hscan-loop (- n 1) (if consume (+ 1 i) i) to (nfix nst) (nfix nk) used a0 b0 rslot rgen lslot lgen okind oslot ogen
                           tslot tgen tk ts tg fn2-pool)))
(fn2-pool-preserves fn2-cursor-hscan-loop (n i to st k used a0 b0 rslot rgen lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)
  :position 4 :rows nil
  :hints (("Goal" :induct (fn2-cursor-hscan-loop n i to st k used a0 b0 rslot rgen lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)
                  :in-theory (disable fn2-gram-read fn2-gram-fill fn2-gram-put fn2-gram-put-crlf fn2-gram-upcase
                                      fn2-cursor-hscan-step fn2-pool-slot-capacity nfix))))
(defun fn2-cursor-pool-hscan (from to st k a0 b0 rslot rgen lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp from) (natp to) (natp st) (natp k)
                                               (natp a0) (natp b0))))
  (mv-let (code used st k fn2-pool)
    (fn2-cursor-hscan-loop (+ 1 (* 2 (min *fn2-cursor-stuff-bytes* (nfix (- (nfix to) (nfix from))))))
                           (nfix from) (min (nfix to) (+ (nfix from) *fn2-cursor-stuff-bytes*)) (nfix st) (nfix k) 0
                           a0 b0 rslot rgen lslot lgen okind oslot ogen tslot tgen tk ts tg fn2-pool)
    (mv code (nfix used) (nfix st) (nfix k) fn2-pool)))
(fn2-pool-preserves fn2-cursor-pool-hscan (from to st k a0 b0 rslot rgen lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool)
  :position 4 :rows nil :hints (("Goal" :in-theory (disable fn2-cursor-hscan-loop))))
(defthm fn2-cursor-pool-hscan-naturals
  (and (natp (mv-nth 1 (fn2-cursor-pool-hscan from to st k a0 b0 rslot rgen lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool)))
       (natp (mv-nth 2 (fn2-cursor-pool-hscan from to st k a0 b0 rslot rgen lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool)))
       (natp (mv-nth 3 (fn2-cursor-pool-hscan from to st k a0 b0 rslot rgen lslot lgen tslot tgen tk ts tg okind oslot ogen fn2-pool))))
  :hints (("Goal" :in-theory (enable fn2-cursor-pool-hscan))))
(in-theory (disable fn2-cursor-hscan-step fn2-cursor-hscan-loop fn2-cursor-pool-hscan))
;; The lease's pool class: the smallest that holds two storage units (a
;; block named through a source manifest is read at the lease's fill, after
;; the manifest unit that names it, and checked against that entry there).
(defun fn2-cursor-lease-class-of (fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-pool-class-for (* 2 *fn2-commit-unit-bytes*) fn2-pool))

;; The entry of the next block of stored octets named through a source
;; manifest (article-manifest.lisp), from the manifest unit the lease holds:
;; MPOS the manifest octet it starts at (0: the header first, its stored
;; length checked against TOTAL), decoded in the stripe of read row X (its
;; lookups are done; the stripe is idle). (mv code mpos logical-offset
;; length unit epoch alloc hoff cvoff fn2-fields), MPOS where the entry after
;; it starts, HOFF and CVOFF where the lease holds the entry's BLAKE3 and
;; chaining value (B's block read checks the block against them).
(defun fn2-cursor-manifest-entry-of (x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (b* (((mv c base) (fn2-read-stripe x (fn2-fc-rows fn2-fc) fn2-reads fn2-id-decides fn2-fields))
       ((unless (eq c :ok)) (mv :bounds 0 0 0 0 0 0 0 0 fn2-fields))
       (mpos (nfix mpos))
       (u0 (* *fn2-commit-unit-bytes* (floor mpos *fn2-commit-unit-bytes*)))
       ((mv c at fn2-fields)
        (if (equal mpos 0)
            (mv-let (c h fn2-fields)
              (fn2-am-get-header base total lslot lgen 0 *fn2-commit-unit-bytes* okind oslot ogen fn2-fields fn2-pool)
              (mv c (fn2-am-entry-at h) fn2-fields))
          (mv :ok mpos fn2-fields)))
       ((unless (and (eq c :ok) (<= u0 at) (< (- at u0) *fn2-commit-unit-bytes*))) (mv :bounds 0 0 0 0 0 0 0 0 fn2-fields))
       ((mv c next lo len unit epoch alloc fn2-fields)
        (fn2-am-get-entry base lslot lgen (- at u0) *fn2-commit-unit-bytes* okind oslot ogen fn2-fields fn2-pool))
       (h (+ (nfix base) *fn2-format-source-manifest-entry-field-block-expected-hash*))
       (cv (+ (nfix base) *fn2-format-source-manifest-entry-field-subtree-cv*))
       ((unless (and (eq c :ok) (< h (nfix (fn2-fields-rows fn2-fields))) (< cv (nfix (fn2-fields-rows fn2-fields)))
                     (equal (fn2-fields-ref-slot h fn2-fields) lslot) (equal (fn2-fields-ref-len h fn2-fields) 32)
                     (equal (fn2-fields-ref-slot cv fn2-fields) lslot) (equal (fn2-fields-ref-len cv fn2-fields) 32)))
        (mv :bounds 0 0 0 0 0 0 0 0 fn2-fields)))
    (mv :ok (fn2-am-entry-at (+ u0 next)) lo len unit epoch alloc
        (nfix (fn2-fields-ref-off h fn2-fields)) (nfix (fn2-fields-ref-off cv fn2-fields)) fn2-fields)))
(defthm fn2-cursor-manifest-entry-of-shape
  (implies (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
           (and (fn2-fieldsp (mv-nth 9 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool)))
                (fn2-fields-wfp (mv-nth 9 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool)))
                (equal (fn2-fields-rows (mv-nth 9 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool)))
                       (fn2-fields-rows fn2-fields))))
  :hints (("Goal" :in-theory (disable fn2-fields-rows fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp))))
(defthm fn2-cursor-manifest-entry-of-natp-1 (natp (mv-nth 1 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool))) :rule-classes :type-prescription)
(defthm fn2-cursor-manifest-entry-of-natp-2 (natp (mv-nth 2 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool))) :rule-classes :type-prescription)
(defthm fn2-cursor-manifest-entry-of-natp-3 (natp (mv-nth 3 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool))) :rule-classes :type-prescription)
(defthm fn2-cursor-manifest-entry-of-natp-4 (natp (mv-nth 4 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool))) :rule-classes :type-prescription)
(defthm fn2-cursor-manifest-entry-of-natp-5 (natp (mv-nth 5 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool))) :rule-classes :type-prescription)
(defthm fn2-cursor-manifest-entry-of-natp-6 (natp (mv-nth 6 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool))) :rule-classes :type-prescription)
(defthm fn2-cursor-manifest-entry-of-natp-7 (natp (mv-nth 7 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool))) :rule-classes :type-prescription)
(defthm fn2-cursor-manifest-entry-of-natp-8 (natp (mv-nth 8 (fn2-cursor-manifest-entry-of x lslot lgen mpos total okind oslot ogen fn2-reads fn2-id-decides fn2-fc fn2-fields fn2-pool))) :rule-classes :type-prescription)
(in-theory (disable fn2-cursor-manifest-entry-of))

;; WHAT 0: "N TAB"; 1: "N CR LF"; 2: CR LF; 3: ". CR LF" (the terminator).
(defun fn2-cursor-pool-put (what n slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n))))
  (case what
    (0 (mv-let (code fn2-pool) (fn2-gram-put-number n slot gen okind oslot ogen fn2-pool)
         (if (not (eq code :ok)) (mv code fn2-pool) (fn2-gram-put 9 slot gen okind oslot ogen fn2-pool))))
    (1 (mv-let (code fn2-pool) (fn2-gram-put-number n slot gen okind oslot ogen fn2-pool)
         (if (not (eq code :ok)) (mv code fn2-pool) (fn2-gram-put-crlf slot gen okind oslot ogen fn2-pool))))
    (2 (fn2-gram-put-crlf slot gen okind oslot ogen fn2-pool))
    (otherwise (mv-let (code fn2-pool) (fn2-gram-put *fn2-gram-dot* slot gen okind oslot ogen fn2-pool)
                 (if (not (eq code :ok)) (mv code fn2-pool) (fn2-gram-put-crlf slot gen okind oslot ogen fn2-pool))))))
(fn2-pool-preserves fn2-cursor-pool-put (what n slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-cursor-pool-put))

;; N spaces at the slot's fill.
(defun fn2-cursor-pad-loop (n slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n))))
  (if (zp n) (mv :ok fn2-pool)
    (mv-let (code fn2-pool) (fn2-gram-put 32 slot gen okind oslot ogen fn2-pool)
      (if (not (eq code :ok)) (mv code fn2-pool)
        (fn2-cursor-pad-loop (- n 1) slot gen okind oslot ogen fn2-pool)))))
(fn2-pool-preserves fn2-cursor-pad-loop (n slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
;; TX filled with spaces up to K octets (the scan's key area), when it holds fewer.
(defun fn2-cursor-pool-pad (k slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp k))))
  (fn2-cursor-pad-loop (nfix (- (nfix k) (fn2-cursor-pool-fill slot fn2-pool))) slot gen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-cursor-pool-pad (k slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
;; A LIST row after its name: " (no description)" for NEWSGROUPS (WHAT 7),
;; nothing for SUBSCRIPTIONS (WHAT 9), else " HIGH LOW [COUNT] STATUS"
;; (COUNT for COUNTS, WHAT 2; STATUS y where the connection serves posting,
;; else n); then CR LF.
(defun fn2-cursor-pool-tail (what high low count posting slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp high) (natp low) (natp count))))
  (b* (((mv code fn2-pool)
        (cond ((equal what *fn2-cursor-list-subscriptions*)
               (mv :ok fn2-pool))
              ((equal what *fn2-cursor-list-newsgroups*)
               (fn2-answer-put-text 0 " (no description)" slot gen okind oslot ogen fn2-pool))
              (t
               (b* (((mv code fn2-pool) (fn2-gram-put 32 slot gen okind oslot ogen fn2-pool))
                    ((unless (eq code :ok)) (mv code fn2-pool))
                    ((mv code fn2-pool) (fn2-gram-put-number high slot gen okind oslot ogen fn2-pool))
                    ((unless (eq code :ok)) (mv code fn2-pool))
                    ((mv code fn2-pool) (fn2-gram-put 32 slot gen okind oslot ogen fn2-pool))
                    ((unless (eq code :ok)) (mv code fn2-pool))
                    ((mv code fn2-pool) (fn2-gram-put-number low slot gen okind oslot ogen fn2-pool))
                    ((unless (eq code :ok)) (mv code fn2-pool))
                    ((mv code fn2-pool) (if (equal what *fn2-cursor-list-counts*)
                                            (fn2-gram-put 32 slot gen okind oslot ogen fn2-pool)
                                          (mv :ok fn2-pool)))
                    ((unless (eq code :ok)) (mv code fn2-pool))
                    ((mv code fn2-pool) (if (equal what *fn2-cursor-list-counts*)
                                            (fn2-gram-put-number count slot gen okind oslot ogen fn2-pool)
                                          (mv :ok fn2-pool)))
                    ((unless (eq code :ok)) (mv code fn2-pool))
                    ((mv code fn2-pool) (fn2-gram-put 32 slot gen okind oslot ogen fn2-pool))
                    ((unless (eq code :ok)) (mv code fn2-pool)))
                 (fn2-gram-put (if (equal posting 1) 121 110) slot gen okind oslot ogen fn2-pool)))))
       ((unless (eq code :ok)) (mv code fn2-pool)))
    (fn2-gram-put-crlf slot gen okind oslot ogen fn2-pool)))
(fn2-pool-preserves fn2-cursor-pool-tail (what high low count posting slot gen okind oslot ogen fn2-pool)
  :position 1 :rows nil)
(in-theory (disable fn2-cursor-pad-loop fn2-cursor-pool-pad fn2-cursor-pool-tail))

;; The Message-ID of an overview line at [from, to) of a slot: its fourth
;; TAB-separated field (subject, from, date, message-id, ...), as (mv code
;; start length).
(defun fn2-cursor-mid-span (slot gen from to okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp from) (natp to))))
  (b* ((left (nfix (- to from)))
       ((mv f1 t1) (fn2-gram-find left from 9 slot gen okind oslot ogen fn2-pool))
       ((mv f2 t2) (fn2-gram-find (nfix (- to (+ 1 t1))) (+ 1 t1) 9 slot gen okind oslot ogen fn2-pool))
       ((mv f3 t3) (fn2-gram-find (nfix (- to (+ 1 t2))) (+ 1 t2) 9 slot gen okind oslot ogen fn2-pool))
       ((mv f4 t4) (fn2-gram-find (nfix (- to (+ 1 t3))) (+ 1 t3) 9 slot gen okind oslot ogen fn2-pool)))
    (if (and f1 f2 f3 f4 (< (+ 1 t3) t4)) (mv :ok (+ 1 t3) (- t4 (+ 1 t3))) (mv :refused 0 0))))
(defthm fn2-cursor-mid-span-types
  (and (natp (mv-nth 1 (fn2-cursor-mid-span slot gen from to okind oslot ogen fn2-pool)))
       (natp (mv-nth 2 (fn2-cursor-mid-span slot gen from to okind oslot ogen fn2-pool)))))
(in-theory (disable fn2-cursor-parse-line fn2-cursor-mid-span fn2-cursor-pool-fill))

(defun fn2-cursor-truncate-to (at slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp at))))
  (let ((at (nfix at)))
    (if (and (eq (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok)
             (unsigned-byte-p 32 at) (<= at (fn2-pool-cap slot fn2-pool)))
        (fn2-pool-set-fill slot at fn2-pool)
      fn2-pool)))
(fn2-pool-preserves fn2-cursor-truncate-to (at slot gen okind oslot ogen fn2-pool) :position nil :rows nil)
(in-theory (disable fn2-cursor-truncate-to))

(defun fn2-cursor-move-loop (left src dst slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp src) (natp dst))))
  (if (zp left) (mv :ok fn2-pool)
    (mv-let (ok b) (fn2-gram-read slot gen (nfix src) okind oslot ogen fn2-pool)
      (if (not ok) (mv :refused fn2-pool)
        (mv-let (wc fn2-pool) (fn2-pool-write slot gen (nfix dst) b okind oslot ogen fn2-pool)
          (if (not (eq wc :ok)) (mv wc fn2-pool)
            (fn2-cursor-move-loop (- left 1) (+ 1 (nfix src)) (+ 1 (nfix dst)) slot gen okind oslot ogen fn2-pool)))))))
;; the pool's read and write closed (D26: 45 s opened, 0.1 s closed)
(fn2-pool-preserves fn2-cursor-move-loop (left src dst slot gen okind oslot ogen fn2-pool) :position 1 :rows nil
  :hints (("Goal" :in-theory (disable fn2-pool-write fn2-gram-read))))
(in-theory (disable fn2-cursor-move-loop))

(defun fn2-cursor-move-line (src len at slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp src) (natp len) (natp at))))
  (mv-let (mc fn2-pool) (fn2-cursor-move-loop (nfix len) (nfix src) (nfix at) slot gen okind oslot ogen fn2-pool)
    (if (not (eq mc :ok)) (mv mc fn2-pool)
      (let ((fn2-pool (fn2-cursor-truncate-to (+ (nfix at) (nfix len)) slot gen okind oslot ogen fn2-pool)))
        (fn2-gram-put-crlf slot gen okind oslot ogen fn2-pool)))))
(fn2-pool-preserves fn2-cursor-move-line (src len at slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-cursor-move-line))

;; The overview line's Xref field (its eighth TAB-separated field, PRF-206's
;; full form "Xref: SERVER group:number") as a header line at the slot's
;; fill, CR LF ended; the line read from [AT, TO), up to an LF. No field:
;; nothing. A field without its "Xref: " label gets it.
(defun fn2-cursor-put-xref (at to slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp at) (natp to))))
  (b* (((mv has-lf lf-pos) (fn2-cursor-next-lf at to slot gen okind oslot ogen fn2-pool))
       (ov-to (if has-lf lf-pos to))
       ((mv f1 t1) (fn2-cursor-next-tab at ov-to slot gen okind oslot ogen fn2-pool))
       ((mv f2 t2) (fn2-cursor-next-tab (+ 1 t1) ov-to slot gen okind oslot ogen fn2-pool))
       ((mv f3 t3) (fn2-cursor-next-tab (+ 1 t2) ov-to slot gen okind oslot ogen fn2-pool))
       ((mv f4 t4) (fn2-cursor-next-tab (+ 1 t3) ov-to slot gen okind oslot ogen fn2-pool))
       ((mv f5 t5) (fn2-cursor-next-tab (+ 1 t4) ov-to slot gen okind oslot ogen fn2-pool))
       ((mv f6 t6) (fn2-cursor-next-tab (+ 1 t5) ov-to slot gen okind oslot ogen fn2-pool))
       ((mv f7 t7) (fn2-cursor-next-tab (+ 1 t6) ov-to slot gen okind oslot ogen fn2-pool))
       ((unless (and f1 f2 f3 f4 f5 f6 f7 (< (+ 1 t7) ov-to))) (mv :ok fn2-pool))
       (xs (+ 1 t7)) (xl (nfix (- ov-to xs)))
       (labelled (and (<= 6 xl) (fn2-gram-match xs 6 "XREF: " slot gen okind oslot ogen fn2-pool)))
       ((mv code fn2-pool)
        (if labelled (mv :ok fn2-pool)
          (fn2-gram-put-template 0 "Xref: " 0 0 0 0 slot gen 0 0 slot gen okind oslot ogen fn2-pool)))
       ((unless (eq code :ok)) (mv code fn2-pool))
       ((mv code fn2-pool) (fn2-gram-put-span xl xs slot gen slot gen okind oslot ogen fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool)))
    (fn2-gram-put-crlf slot gen okind oslot ogen fn2-pool)))
(fn2-pool-preserves fn2-cursor-put-xref (at to slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
;; ARTICLE's and HEAD's opening: the 22x line, then (XREF) the overview's
;; Xref field as the article's first header line (RFC 5536 3.2.14: the
;; serving node's; fn1 and H's model put it before the stored source). The
;; overview line is TX's scratch at [AT, ROFF) (the page is sent from
;; ROFF) and the 22x line's Message-ID is its span [MS, MS+ML): both lines
;; are rendered after it, at the fill ROFF, so no copy reads what another
;; wrote.
(defun fn2-cursor-pool-art-open (cmd reply mask n xref at roff ms ml slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp at) (natp roff) (natp ms) (natp ml))
                  :guard-hints (("Goal" :in-theory (disable fn2-nntp-reply-template fn2-nntp-reply-admitted
                                                            fn2-nntp-reply-command fn2-nntp-reply-layer)))))
  (b* ((at (nfix at)) (roff (max at (nfix roff)))
       ((unless (equal (fn2-gram-fill slot fn2-pool) roff)) (mv :fault fn2-pool))
       ((mv code fn2-pool) (fn2-cursor-render cmd reply mask (nfix n) 0 0 slot gen (nfix ms) (nfix ml)
                                              slot gen okind oslot ogen fn2-pool))
       ((unless (eq code :ok)) (mv :fault fn2-pool))
       ((mv code fn2-pool) (if xref (fn2-cursor-put-xref at roff slot gen okind oslot ogen fn2-pool) (mv :ok fn2-pool)))
       ((unless (eq code :ok)) (mv :fault fn2-pool)))
    (mv :ok fn2-pool)))
(fn2-pool-preserves fn2-cursor-pool-art-open (cmd reply mask n xref at roff ms ml slot gen okind oslot ogen fn2-pool)
  :position 1 :rows nil
  :hints (("Goal" :in-theory (disable fn2-nntp-reply-template fn2-nntp-reply-admitted
                                      fn2-nntp-reply-command fn2-nntp-reply-layer nfix))))
(in-theory (disable fn2-cursor-put-xref fn2-cursor-pool-art-open))

(defun fn2-cursor-pool-list-filter (variant k1 a1 b1 at copied rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp variant) (natp k1) (natp a1) (natp b1)
                              (natp at) (natp copied))))
  (let ((keep (and (not (equal (nfix variant) *fn2-cursor-list-times*))
                   (or (not (equal (nfix k1) *fn2-cursor-arg-span*))
                       (fn2-wildmat-match-p (nfix a1) (+ (nfix a1) (nfix b1)) rslot rgen
                                            (nfix at) (+ (nfix at) (nfix copied)) tslot tgen
                                            okind oslot ogen fn2-pool)))))
    (if keep
        (mv :ok t fn2-pool)
      (let ((fn2-pool (fn2-cursor-truncate-to at tslot tgen okind oslot ogen fn2-pool)))
        (mv :ok nil fn2-pool)))))
(fn2-pool-preserves fn2-cursor-pool-list-filter
  (variant k1 a1 b1 at copied rslot rgen tslot tgen okind oslot ogen fn2-pool) :position 2 :rows nil)
(in-theory (disable fn2-cursor-pool-list-filter))

(defun fn2-cursor-pool-newnews-filter (a0 b0 at copied rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp a0) (natp b0) (natp at) (natp copied))))
  (let* ((keep (fn2-wildmat-match-p (nfix a0) (+ (nfix a0) (nfix b0)) rslot rgen
                                    (nfix at) (+ (nfix at) (nfix copied)) tslot tgen
                                    okind oslot ogen fn2-pool))
         (fn2-pool (fn2-cursor-truncate-to at tslot tgen okind oslot ogen fn2-pool)))
    (mv :ok (and keep t) fn2-pool)))
(fn2-pool-preserves fn2-cursor-pool-newnews-filter
  (a0 b0 at copied rslot rgen tslot tgen okind oslot ogen fn2-pool) :position 2 :rows nil)
(in-theory (disable fn2-cursor-pool-newnews-filter))

(defun fn2-cursor-span-eq-p (len s1 s2 slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix len)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp len) (natp s1) (natp s2))))
  (if (zp len) t
    (mv-let (ok1 b1) (fn2-gram-read slot gen (nfix s1) okind oslot ogen fn2-pool)
      (mv-let (ok2 b2) (fn2-gram-read slot gen (nfix s2) okind oslot ogen fn2-pool)
        (and ok1 ok2 (= b1 b2)
             (fn2-cursor-span-eq-p (- len 1) (+ 1 (nfix s1)) (+ 1 (nfix s2)) slot gen okind oslot ogen fn2-pool))))))
(in-theory (disable fn2-cursor-span-eq-p))

(defun fn2-cursor-mid-seen-p (fuel i at ms ml slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix fuel)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp fuel) (natp i) (natp at) (natp ms) (natp ml))))
  (if (or (zp fuel) (>= (nfix i) (nfix at))) nil
    (mv-let (has-lf lf-pos) (fn2-cursor-next-lf (nfix i) (nfix at) slot gen okind oslot ogen fn2-pool)
      (if (or (not has-lf) (>= lf-pos (nfix at))) nil
        (let ((line-end (nfix (- lf-pos 1))))
          (or (and (equal (nfix (- line-end (nfix i))) (nfix ml))
                   (fn2-cursor-span-eq-p (nfix ml) (nfix i) (nfix ms) slot gen okind oslot ogen fn2-pool))
              (fn2-cursor-mid-seen-p (- fuel 1) (+ 1 lf-pos) at ms ml slot gen okind oslot ogen fn2-pool)))))))
(in-theory (disable fn2-cursor-mid-seen-p))

(defun fn2-cursor-pool-newnews-mid (roff at to tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp roff) (natp at) (natp to))))
  (mv-let (mcode ms ml) (fn2-cursor-mid-span tslot tgen at to okind oslot ogen fn2-pool)
    (if (or (not (eq mcode :ok))
            (fn2-cursor-mid-seen-p (nfix (- (nfix at) (nfix roff))) roff at ms ml tslot tgen okind oslot ogen fn2-pool))
        (let ((fn2-pool (fn2-cursor-truncate-to at tslot tgen okind oslot ogen fn2-pool)))
          (mv :ok fn2-pool))
      (fn2-cursor-move-line ms ml at tslot tgen okind oslot ogen fn2-pool))))
(fn2-pool-preserves fn2-cursor-pool-newnews-mid (roff at to tslot tgen okind oslot ogen fn2-pool)
  :position 1 :rows nil)
(in-theory (disable fn2-cursor-pool-newnews-mid))

(defun fn2-cursor-pool-hdr-label (tag n k1 a1 b1 rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp tag) (natp n) (natp k1) (natp a1) (natp b1))))
  (b* (((mv code fn2-pool)
        (if (and (or (equal (nfix tag) *fn2-nntp-command-xhdr*)
                     (equal (nfix tag) *fn2-nntp-command-xpat*))
                 (equal (nfix k1) *fn2-cursor-arg-span*))
            (fn2-gram-put-span (nfix b1) (nfix a1) (nfix rslot) (nfix rgen) tslot tgen okind oslot ogen fn2-pool)
          (fn2-gram-put-number (if (equal (nfix k1) *fn2-cursor-arg-span*) 0 (nfix n))
                               tslot tgen okind oslot ogen fn2-pool)))
       ((unless (eq code :ok)) (mv code fn2-pool)))
    (fn2-gram-put 32 tslot tgen okind oslot ogen fn2-pool)))
(fn2-pool-preserves fn2-cursor-pool-hdr-label (tag n k1 a1 b1 rslot rgen tslot tgen okind oslot ogen fn2-pool)
  :position 1 :rows nil)
(in-theory (disable fn2-cursor-pool-hdr-label))


;; A header the overview line does not carry (not one of its seven fields
;; nor Xref on HDR/XHDR, nor a metadata item): its value is read from the
;; stored octets. XPAT Xref reads stored headers (specs/nntp.md:428).
(defun fn2-cursor-hdr-stored-p (tag a0 b0 rslot rgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp tag) (natp a0) (natp b0))))
  (mv-let (ok c) (fn2-gram-read rslot rgen (nfix a0) okind oslot ogen fn2-pool)
    (not (or (not ok) (equal c 58) (zp b0)
             (fn2-gram-match a0 b0 "SUBJECT" rslot rgen okind oslot ogen fn2-pool)
             (fn2-gram-match a0 b0 "FROM" rslot rgen okind oslot ogen fn2-pool)
             (fn2-gram-match a0 b0 "DATE" rslot rgen okind oslot ogen fn2-pool)
             (fn2-gram-match a0 b0 "MESSAGE-ID" rslot rgen okind oslot ogen fn2-pool)
             (fn2-gram-match a0 b0 "REFERENCES" rslot rgen okind oslot ogen fn2-pool)
             (and (not (equal (nfix tag) *fn2-nntp-command-xpat*))
                  (fn2-gram-match a0 b0 "XREF" rslot rgen okind oslot ogen fn2-pool))))))
(local (in-theory (disable fn2-gram-match)))
(defun fn2-cursor-pool-hdr-val (tag a0 b0 at to rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp tag) (natp a0) (natp b0) (natp at) (natp to))))
  (let ((tag (nfix tag)) (a0 (nfix a0)) (b0 (nfix b0)) (at (nfix at)) (to (nfix to)))
    (if (or (fn2-gram-match a0 b0 ":FN-VERIFIED" rslot rgen okind oslot ogen fn2-pool)
            (fn2-gram-match a0 b0 ":FN-CONTROL" rslot rgen okind oslot ogen fn2-pool)
            (fn2-gram-match a0 b0 ":FN-ENROLLMENT" rslot rgen okind oslot ogen fn2-pool))
        (b* ((fn2-pool (fn2-cursor-truncate-to at tslot tgen okind oslot ogen fn2-pool))
             ((mv code fn2-pool) (fn2-answer-put-text 0 "absent no-field" tslot tgen okind oslot ogen fn2-pool))
             ((unless (eq code :ok)) (mv code fn2-pool)))
          (fn2-gram-put-crlf tslot tgen okind oslot ogen fn2-pool))
      (b* (((when (fn2-cursor-hdr-stored-p tag a0 b0 rslot rgen okind oslot ogen fn2-pool))
            (let ((fn2-pool (fn2-cursor-truncate-to at tslot tgen okind oslot ogen fn2-pool))) (mv :stored fn2-pool)))
           ((mv has-lf lf-pos) (fn2-cursor-next-lf at to tslot tgen okind oslot ogen fn2-pool))
           (ov-to (if has-lf lf-pos to))
           ((mv f1 t1) (fn2-cursor-next-tab at ov-to tslot tgen okind oslot ogen fn2-pool))
           ((mv f2 t2) (fn2-cursor-next-tab (+ 1 t1) ov-to tslot tgen okind oslot ogen fn2-pool))
           ((mv f3 t3) (fn2-cursor-next-tab (+ 1 t2) ov-to tslot tgen okind oslot ogen fn2-pool))
           ((mv f4 t4) (fn2-cursor-next-tab (+ 1 t3) ov-to tslot tgen okind oslot ogen fn2-pool))
           ((mv f5 t5) (fn2-cursor-next-tab (+ 1 t4) ov-to tslot tgen okind oslot ogen fn2-pool))
           ((mv f6 t6) (fn2-cursor-next-tab (+ 1 t5) ov-to tslot tgen okind oslot ogen fn2-pool))
           ((mv f7 t7) (fn2-cursor-next-tab (+ 1 t6) ov-to tslot tgen okind oslot ogen fn2-pool))
           ((unless (and f1 f2 f3 f4 f5 f6)) (mv :refused fn2-pool))
           (lines-to (if f7 t7 ov-to))
           (has-xref (and f7 (< (+ 1 t7) ov-to)))
           ((mv vs ve)
            (cond ((fn2-gram-match a0 b0 "SUBJECT" rslot rgen okind oslot ogen fn2-pool)
                   (mv at (max at t1)))
                  ((fn2-gram-match a0 b0 "FROM" rslot rgen okind oslot ogen fn2-pool)
                   (mv (+ 1 t1) (max (+ 1 t1) t2)))
                  ((fn2-gram-match a0 b0 "DATE" rslot rgen okind oslot ogen fn2-pool)
                   (mv (+ 1 t2) (max (+ 1 t2) t3)))
                  ((fn2-gram-match a0 b0 "MESSAGE-ID" rslot rgen okind oslot ogen fn2-pool)
                   (mv (+ 1 t3) (max (+ 1 t3) t4)))
                  ((fn2-gram-match a0 b0 "REFERENCES" rslot rgen okind oslot ogen fn2-pool)
                   (mv (+ 1 t4) (max (+ 1 t4) t5)))
                  ((fn2-gram-match a0 b0 ":BYTES" rslot rgen okind oslot ogen fn2-pool)
                   (mv (+ 1 t5) (max (+ 1 t5) t6)))
                  ((fn2-gram-match a0 b0 ":LINES" rslot rgen okind oslot ogen fn2-pool)
                   (mv (+ 1 t6) (max (+ 1 t6) lines-to)))
                  ((fn2-gram-match a0 b0 "XREF" rslot rgen okind oslot ogen fn2-pool)
                   (if has-xref
                       (let ((xs (if (and (<= (+ 7 t7) ov-to)
                                          (fn2-gram-match (+ 1 t7) 6 "XREF: " tslot tgen okind oslot ogen fn2-pool))
                                     (+ 7 t7)
                                   (+ 1 t7))))
                         (mv xs (max xs ov-to)))
                     (mv at at)))
                  (t (mv at at)))))
        (fn2-cursor-move-line vs (nfix (- ve vs)) at tslot tgen okind oslot ogen fn2-pool)))))
(fn2-pool-preserves fn2-cursor-pool-hdr-val (tag a0 b0 at to rslot rgen tslot tgen okind oslot ogen fn2-pool)
  :position 1 :rows nil
  :hints (("Goal" :in-theory (disable fn2-gram-match fn2-cursor-next-tab fn2-cursor-next-lf fn2-cursor-hdr-stored-p
                                      fn2-cursor-truncate-to fn2-answer-put-text fn2-gram-put-crlf
                                      fn2-cursor-move-line nfix))))
(in-theory (disable fn2-cursor-pool-hdr-val))

;; XPAT: TX holds "<label> <value>\r\n" with <label> at LAT and <value> at VAT.
;; Truncate TX back to LAT when the value does not match XPAT's wildmat.
(defun fn2-cursor-pool-xpat-filter (tag a2 b2 lat vat rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp tag) (natp a2) (natp b2)
                              (natp lat) (natp vat))))
  (if (not (equal (nfix tag) *fn2-nntp-command-xpat*))
      (mv :ok fn2-pool)
    (let* ((tfill (fn2-cursor-pool-fill tslot fn2-pool))
           (vs (nfix vat))
           (ve (max vs (nfix (- tfill 2))))
           (keep (fn2-xpat-wildmat-match-p (nfix a2) (+ (nfix a2) (nfix b2)) rslot rgen
                                           vs ve tslot tgen okind oslot ogen fn2-pool))
           (fn2-pool (if keep fn2-pool
                       (fn2-cursor-truncate-to lat tslot tgen okind oslot ogen fn2-pool))))
      (mv :ok fn2-pool))))
(fn2-pool-preserves fn2-cursor-pool-xpat-filter
  (tag a2 b2 lat vat rslot rgen tslot tgen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-cursor-pool-xpat-filter))

(defcost fn2-cursor-parse :child fn2-cursor-parse-line :answers (:ok :refused) :bytes 512
 :doc "Parse the connection's command line again (at most 512 octets of its RX, under its owner).")
(defcost fn2-cursor-tx-fill :child fn2-cursor-pool-fill :doc "A pool slot's fill (0 out of range).")
(defcost fn2-cursor-tx-cap :child fn2-pool-slot-capacity :doc "A pool slot's capacity (0 out of range).")
(defcost fn2-cursor-say :child fn2-cursor-render :answers t :bytes 1024 :tables (fn2-core-pool)
 :doc "Render one typed status line (numbers and one span) at the slot's fill.")
(defcost fn2-cursor-art-open :child fn2-cursor-pool-art-open :answers (:ok :fault) :faults (:fault) :bytes 4096
 :tables (fn2-core-pool)
 :doc "ARTICLE/HEAD/BODY's 22x line and, for ARTICLE and HEAD, the overview's Xref field as the first header line.")
(defcost fn2-cursor-put-line :child fn2-cursor-pool-put :answers t :bytes 64 :tables (fn2-core-pool)
 :doc "Append a number and TAB, a number line, CR LF, or the terminator.")
(defcost fn2-cursor-reset :child fn2-pool-reset :answers t :tables (fn2-core-pool)
 :doc "Empty TX (under the connection's owner) before a refusal replaces a status line.")
(defcost fn2-cursor-free-head :child fn2-machines-free-head-of :doc "The cursor partition's free head.")
(defcost fn2-cursor-gen-limit :child fn2-machines-gen-limit :doc "The profile's generation limit.")
(defcost fn2-cursor-reclaim :child fn2-machines-reclaim :tables (fn2-core-machines)
  :effects ((:release (:cursor-row))) :doc "Return a drained cursor row to its partition's free chain.")
(defcost fn2-cursor-pad :child fn2-cursor-pool-pad :answers t :bytes 256 :tables (fn2-core-pool)
 :doc "Fill TX with spaces up to the scan's key area (at most 256 octets).")
(defcost fn2-cursor-tail :child fn2-cursor-pool-tail :answers t :bytes 128 :tables (fn2-core-pool)
 :doc "A LIST row after its name: the description, or the numbers and the status; then CR LF.")
(defcost fn2-cursor-mid :child fn2-cursor-mid-span :answers (:ok :refused) :bytes 1024
 :doc "Find an overview line's Message-ID field (at most 1,024 octets read).")
(defcost fn2-cursor-list-filter :child fn2-cursor-pool-list-filter :answers (:ok) :bytes 1024 :tables (fn2-core-pool)
 :doc "Filter a LIST group name by variant and wildmat, truncating TX when excluded.")
(defcost fn2-cursor-newnews-filter :child fn2-cursor-pool-newnews-filter :answers (:ok) :bytes 1024 :tables (fn2-core-pool)
 :doc "Check whether a group name matches NEWNEWS's wildmat, truncating TX back to AT.")
(defcost fn2-cursor-newnews-mid :child fn2-cursor-pool-newnews-mid :answers t :bytes 1024 :tables (fn2-core-pool)
 :doc "Extract an overview line's Message-ID and append it once to the NEWNEWS page.")
(defcost fn2-cursor-hdr-label :child fn2-cursor-pool-hdr-label :answers t :bytes 256 :tables (fn2-core-pool)
 :doc "Append the article number or Message-ID label and a space for HDR/XHDR.")
(defcost fn2-cursor-hdr-val :child fn2-cursor-pool-hdr-val :answers t :bytes 1024 :tables (fn2-core-pool)
 :doc "Extract the requested header or metadata value from an overview line and append CR LF (:stored: a header the line lacks, TX back at AT).")
(defcost fn2-cursor-xpat-filter :child fn2-cursor-pool-xpat-filter :answers (:ok) :bytes 1024 :tables (fn2-core-pool)
 :doc "Filter a rendered HDR/XHDR/XPAT row by XPAT's wildmat, truncating TX back to LAT when excluded.")
(defcost fn2-cursor-stuff :child fn2-cursor-pool-stuff :answers (:ok :full :end :fault) :faults (:fault) :bytes 8192
 :tables (fn2-core-pool)
 :doc "Copy at most 4,096 stored octets from the lease onto TX, dot-stuffed; (mv code used st).")
(defcost fn2-cursor-hscan :child fn2-cursor-pool-hscan :answers (:ok :done :full :fault) :faults (:fault) :bytes 8192
 :tables (fn2-core-pool)
 :doc "Scan at most 4,096 stored octets of the lease for HDR's field, its value appended to TX; (mv code used st k).")
(defcost fn2-cursor-lease-reserve :child fn2-pool-reserve :answers (:ok :exhausted :bounds :state) :tables (fn2-core-pool)
 :doc "Reserve the cursor's read lease (two storage units) under its own owner: (mv code slot gen).")
(defcost fn2-cursor-lease-release :child fn2-core-release-children :answers t :tables (fn2-core-pool fn2-core-control)
 :doc "Return the cursor's read lease.")
(defcost fn2-cursor-manifest-entry :child fn2-cursor-manifest-entry-of :answers (:ok :bounds)
 :bytes 512 :tables (fn2-core-reads fn2-core-id-decides fn2-core-fc fn2-core-fields fn2-core-pool)
 :doc "Decode the next block's source-manifest entry from the manifest unit in the lease: (mv code mpos lo len unit epoch alloc hoff cvoff).")
(defcost fn2-cursor-lease-class :child fn2-cursor-lease-class-of :doc "The pool class of the cursor's read lease (nil: none).")
(defcost fn2-cursor-copy-span :child fn2-gram-put-span :answers t :bytes 256 :tables (fn2-core-pool)
 :doc "Copy a Message-ID span from RX into TX.")

; ---------------------------------------------------------------------------
; The kind. A cursor row in slot S reads through read row 2S, and LIST's
; per-group counts through 2S+1 beside the scan (machines-b.lisp's layout:
; :capacity is (fn2-b-cursor-rows profile)).
(defmachine-arms fn2-cursor :children
 :subarms
 (;; the page is ready: TX is the connection's move; wake it and wait
  (hand (:set (turn 0)) (:wake-row row-conn) (:next :send) (:charge :steps *fn2-work-transition*))
  ;; a status line alone (REPLY), the last page
  (refuse :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-cursor-say row-tag row-reply row-mask 0 0 0 row-tx-slot row-tx-gen 0 0 row-tx-slot row-tx-gen
                               :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
    :accept (:ok))
   (:set (done 1) (roff 0) (update *fn2-cursor-update-none*))
   (:goto hand))
  ;; the overview range of the selected group over numbers [LO, HI], at the view
  (range :on-refusal ((:stop :machine-phase))
   (:let g (if (equal row-step 8) row-lgroup row-group))
   (:do (c1) (fn2-read-key (* 2 row-slot) ':lo 0 g) :accept (:ok))
   (:do (c2) (fn2-read-key (* 2 row-slot) ':lo 1 row-lo) :accept (:ok))
   (:do (c3) (fn2-read-key (* 2 row-slot) ':hi 0 g) :accept (:ok))
   (:do (c4) (fn2-read-key (* 2 row-slot) ':hi 1 row-hi) :accept (:ok))
   (:do (c5) (fn2-read-range (* 2 row-slot) *fn2-cursor-overview-sid*
                             *fn2-overview-entry-field-position* (if (equal row-pin 0) *fn2-none* row-pin))
    :accept (:ok))
   (:set (have 0) (next row-lo))
   (:next :render) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
  ;; OVER/XOVER, HDR/XHDR: the status line first (TX is reset if the range is empty)
  (over-head :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :found) row-mask 0 0 0
                               row-tx-slot row-tx-gen 0 0 row-tx-slot row-tx-gen
                               :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
    :accept (:ok))
   (:goto range))
  (seek-name :on-refusal ((:stop :machine-phase))
     (:do (kc) (fn2-read-key-octets (* 2 row-slot) 0 row-rx-slot row-rx-gen row-a0 row-b0
                                    :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (step 1)) (:charge :steps *fn2-work-transition* :runnable t))
  (seek-group :on-refusal ((:stop :machine-phase))
     (:do (lc) (fn2-read-lookup (* 2 row-slot) *fn2-groups-sid* *fn2-cursor-step-budget*)
      :accept ()
      :case (((:ok) (:do (vc g) (fn2-read-value (* 2 row-slot) *fn2-groups-entry-field-group*) :accept (:ok))
                    (:do (fc v) (fn2-read-frontier) :accept (:ok))
                    (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
                    (:set (sel g) (spin v) (step 2))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:absent) (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
                        (:set (reply (fn2-cursor-reply-of row-tag :no-group))) (:goto refuse))
             (:otherwise (:stop :machine-phase)))))
  (seek-counts-key :on-refusal ((:stop :machine-phase))
     (:do (kc) (fn2-read-key (* 2 row-slot) ':lo 0 row-sel) :accept (:ok))
     (:set (step 3)) (:charge :steps *fn2-work-transition* :runnable t))
  (seek-counts :on-refusal ((:stop :machine-phase))
     (:do (lc) (fn2-read-lookup (* 2 row-slot) *fn2-txn-counts-sid* *fn2-cursor-step-budget*)
      :accept ()
      :case (((:ok) (:do (c1 n) (fn2-read-value (* 2 row-slot) *fn2-group-counts-entry-field-count*) :accept (:ok))
                    (:do (c2 l) (fn2-read-value (* 2 row-slot) *fn2-group-counts-entry-field-low*) :accept (:ok))
                    (:do (c3 h) (fn2-read-value (* 2 row-slot) *fn2-group-counts-entry-field-high*) :accept (:ok))
                    (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
                    (:set (count n) (low (if (equal n 0) (+ 1 (nfix h)) l)) (high h) (step 4))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:absent) (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
                        (:set (count 0) (low 1) (high 0) (step 4))
                        (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
  (seek-selected :on-refusal ((:stop :machine-phase))
     ;; the group's name: the argument in RX, or (LISTGROUP with no name) the
     ;; key the directory scan left at the front of TX
     (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :selected) row-mask row-count row-low row-high
                                 (if (equal row-k0 *fn2-cursor-arg-span*) row-rx-slot row-tx-slot)
                                 (if (equal row-k0 *fn2-cursor-arg-span*) row-rx-gen row-tx-gen)
                                 (if (equal row-k0 *fn2-cursor-arg-span*) row-a0 0)
                                 (if (equal row-k0 *fn2-cursor-arg-span*) row-b0 row-klen)
                                 row-tx-slot row-tx-gen
                                 :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (update *fn2-cursor-update-selection*) (ncurrent (if (equal row-count 0) 0 row-low)) (seen 1))
     (:if (equal row-tag *fn2-nntp-command-group*)
          ((:set (done 1) (roff 0)) (:goto hand))
          ((:set (group row-sel) (pin row-spin)
                 (lo (if (equal row-k1 *fn2-cursor-arg-range*) (max row-a1 row-low) row-low))
                 (hi (if (equal row-k1 *fn2-cursor-arg-range*) (min row-b1 row-high) row-high)))
           (:goto range))))
  (seek-identity :on-refusal ((:stop :machine-phase))
     (:do (ic article candidates)
          (fn2-read-identity (* 2 row-slot) row-rx-slot row-rx-gen
                             (if (fn2-cursor-hdr-p row-tag) row-a1 row-a0)
                             (if (fn2-cursor-hdr-p row-tag) row-b1 row-b0)
                             :okind row-conn-kind :oslot row-conn :ogen row-conn-gen :budget *fn2-cursor-step-budget*)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:found) (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
                       (:cond ((equal row-tag *fn2-nntp-command-check*)
                               (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :not-wanted) row-mask 0 0 0
                                                           row-rx-slot row-rx-gen row-a0 row-b0 row-tx-slot row-tx-gen
                                                           :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                                :accept (:ok))
                               (:set (done 1) (roff 0) (update *fn2-cursor-update-none*)) (:goto hand))
                              ((equal row-tag *fn2-nntp-command-ihave*)
                               (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :not-wanted) row-mask 0 0 0
                                                           row-tx-slot row-tx-gen 0 0 row-tx-slot row-tx-gen
                                                           :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                                :accept (:ok))
                               (:set (done 1) (roff 0) (update *fn2-cursor-update-none*)) (:goto hand))
                              ((or (equal row-pin 0) (<= (nfix article) row-pin))
                               (:if (equal row-tag *fn2-nntp-command-stat*)
                                    ((:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :found) row-mask 0 0 0
                                                                row-rx-slot row-rx-gen row-a0 row-b0 row-tx-slot row-tx-gen
                                                                :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                                      :accept (:ok))
                                     (:set (done 1) (roff 0) (update *fn2-cursor-update-none*)) (:goto hand))
                                    ((:set (spin article) (found 0) (lgroup (if (< 0 row-group) row-group 1))
                                           (lo 1) (hi *fn2-none*) (step 8))
                                     (:if (or (fn2-cursor-overview-p row-tag) (fn2-cursor-hdr-p row-tag))
                                          ((:goto over-head))
                                          ((:goto range))))))
                              (t (:set (reply (fn2-cursor-reply-of row-tag :no-msgid))) (:goto refuse))))
             ((:evidence :absent) (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
                                  (:cond ((equal row-tag *fn2-nntp-command-check*)
                                          (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :wanted) row-mask 0 0 0
                                                                      row-rx-slot row-rx-gen row-a0 row-b0 row-tx-slot row-tx-gen
                                                                      :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                                           :accept (:ok))
                                          (:set (done 1) (roff 0) (update *fn2-cursor-update-none*)) (:goto hand))
                                         ((equal row-tag *fn2-nntp-command-ihave*)
                                          (:do (code) (fn2-cursor-copy-span row-b0 row-a0 row-rx-slot row-rx-gen
                                                                            row-tx-slot row-tx-gen
                                                                            :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                                           :accept (:ok))
                                          (:set (done 1) (roff row-b0) (update *fn2-cursor-update-ihave*) (ncurrent row-b0))
                                          (:goto hand))
                                         (t (:set (reply (fn2-cursor-reply-of row-tag :no-msgid))) (:goto refuse))))
             (:otherwise (:stop :machine-phase)))))
  ;; the range's end, by what was read (render-step's :end, one sub-arm a branch)
  (end-last :on-refusal ((:stop :machine-phase))
     ;; LAST walked its range: read the last entry again
     (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
     (:set (lo row-found) (hi row-found) (step 7)) (:goto range))
  (end-match :on-refusal ((:stop :machine-phase))
     (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
     (:if (< row-found 8)
          ((:set (lgroup (+ 1 row-found)) (found (+ 1 row-found)) (lo 1) (hi *fn2-none*)) (:goto range))
          ((:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
            :accept (:ok))
           (:set (reply (fn2-cursor-reply-of row-tag :no-msgid)))
           (:goto refuse))))
  (end-single :on-refusal ((:stop :machine-phase))
     ;; NEXT/LAST: no next or previous article; STAT n: no such number;
     ;; STAT: the current article is gone
     (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
     (:set (reply (fn2-cursor-reply-of row-tag (if (or (equal row-k0 *fn2-cursor-arg-range*)
                                                       (equal row-tag *fn2-nntp-command-next*)
                                                       (equal row-tag *fn2-nntp-command-last*))
                                                   :none :no-current))))
     (:goto refuse))
  (end-empty :on-refusal ((:stop :machine-phase))
     ;; an empty overview/HDR range: the status line goes, the refusal replaces it
     (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
     (:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (reply (fn2-cursor-reply-of row-tag
                                       (if (equal (if (fn2-cursor-hdr-p row-tag) row-k1 row-k0)
                                                  *fn2-cursor-arg-range*)
                                           :none :no-current))))
     (:goto refuse))
  (end-list :on-refusal ((:stop :machine-phase))
     ;; the rows' terminator
     (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
     (:do (code) (fn2-cursor-put-line 3 0 row-tx-slot row-tx-gen
                                      :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (done 1)) (:goto hand))
  ;; LISTGROUP with no name: the selected group's name is read back from the
  ;; group directory, scanned in name order into TX's key area (the page
  ;; starts after it); then the group is selected again as by name
  (lg-start :on-refusal ((:stop :machine-phase))
     (:do (pc) (fn2-cursor-pad *fn2-cursor-key-room* row-tx-slot row-tx-gen
                               :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:do (sc) (fn2-read-scan (* 2 row-slot) *fn2-groups-sid* row-tx-slot row-tx-gen row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:set (roff *fn2-cursor-key-room*) (step 10)) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
  (lg-step :on-refusal ((:stop :machine-phase))
     (:do (nc) (fn2-read-scan-next (* 2 row-slot) *fn2-cursor-step-budget*)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:entry) (:do (vc g) (fn2-read-value (* 2 row-slot) *fn2-groups-entry-field-group*) :accept (:ok))
                       (:if (equal g row-group)
                            ;; its key is TX[0, KLEN): the name's length, nothing copied
                            ((:do (oc copied left) (fn2-read-octets (* 2 row-slot) *fn2-groups-entry-field-name* 0 0
                                                                    row-tx-slot row-tx-gen 0
                                                                    row-conn-kind row-conn row-conn-gen)
                              :accept (:ok))
                             (:set (klen left) (step 11)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                            ((:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))))
             ;; the selected group is not in the directory: unavailable
             ((:end) (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
                     (:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn
                                                 :ogen row-conn-gen)
                      :accept (:ok))
                     (:set (reply (fn2-cursor-reply-of row-tag :no-projection))) (:goto refuse))
             (:otherwise (:stop :machine-phase)))))
  (lg-found :on-refusal ((:stop :machine-phase))
     (:do (fc v) (fn2-read-frontier) :accept (:ok))
     (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
     (:set (sel row-group) (spin v) (step 2))
     (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
  ;; LIST ACTIVE, ACTIVE.TIMES, COUNTS, NEWSGROUPS, SUBSCRIPTIONS: the 215
  ;; line after TX's key area, then the group directory scanned in name order
  (list-start :on-refusal ((:stop :machine-phase))
     (:do (pc) (fn2-cursor-pad *fn2-cursor-key-room* row-tx-slot row-tx-gen
                               :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:do (code) (fn2-cursor-say row-tag (fn2-cursor-list-reply row-k0 row-a0)
                                 row-mask 0 0 0 row-tx-slot row-tx-gen 0 0 row-tx-slot row-tx-gen
                                 :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:do (sc) (fn2-read-scan (* 2 row-slot) *fn2-groups-sid* row-tx-slot row-tx-gen row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:set (roff *fn2-cursor-key-room*) (have 0) (step 9) (update *fn2-cursor-update-none*))
     (:next :render) (:charge :bytes 1024 :steps *fn2-work-transition* :runnable t))
  ;; the next group: its name copied after the page's rows, filtered by
  ;; variant and wildmat, then rendered at once (NEWSGROUPS, SUBSCRIPTIONS)
  ;; or its counts looked up next
  (list-step :on-refusal ((:stop :machine-phase))
     (:do (nc) (fn2-read-scan-next (* 2 row-slot) *fn2-cursor-step-budget*)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:entry)
              (:let at (nfix (fn2-cursor-tx-fill row-tx-slot)))
              (:let v (fn2-cursor-list-variant row-k0 row-a0))
              (:do (vc g) (fn2-read-value (* 2 row-slot) *fn2-groups-entry-field-group*) :accept (:ok))
              (:do (oc copied left) (fn2-read-octets (* 2 row-slot) *fn2-groups-entry-field-name* 0 *fn2-groups-name-max*
                                                     row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
               :accept (:ok))
              (:do (fc keep) (fn2-cursor-list-filter v row-k1 row-a1 row-b1 at (nfix copied)
                                                     row-rx-slot row-rx-gen row-tx-slot row-tx-gen
                                                     :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
               :accept (:ok))
              (:if (not keep)
                   ((:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                   ((:if (or (equal v *fn2-cursor-list-newsgroups*)
                             (equal v *fn2-cursor-list-subscriptions*))
                         ((:do (tc) (fn2-cursor-tail v 0 0 0 0 row-tx-slot row-tx-gen
                                                     :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                           :accept (:ok))
                          (:set (seen 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                         ((:set (lgroup g) (have 1) (seen 1))
                          (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))))))
             ((:end) (:goto end-list))
             (:otherwise (:stop :machine-phase)))))
  ;; the group's counts through the second read row: its key, then the lookup
  (list-key :on-refusal ((:stop :machine-phase))
     (:do (kc) (fn2-read-key (+ 1 (* 2 row-slot)) ':lo 0 row-lgroup) :accept (:ok))
     (:set (have 2)) (:charge :steps *fn2-work-transition* :runnable t))
  (list-counts :on-refusal ((:stop :machine-phase))
     (:do (lc) (fn2-read-lookup (+ 1 (* 2 row-slot)) *fn2-txn-counts-sid* *fn2-cursor-step-budget*)
      :accept ()
      :case (((:ok) (:do (c1 n) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-group-counts-entry-field-count*) :accept (:ok))
                    (:do (c2 l) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-group-counts-entry-field-low*) :accept (:ok))
                    (:do (c3 h) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-group-counts-entry-field-high*) :accept (:ok))
                    (:do (rc) (fn2-read-release (+ 1 (* 2 row-slot))) :accept (:ok))
                    (:do (tc) (fn2-cursor-tail (fn2-cursor-list-variant row-k0 row-a0) (nfix h)
                                               (if (equal n 0) (+ 1 (nfix h)) (nfix l)) (nfix n) row-posting
                                               row-tx-slot row-tx-gen
                                               :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                     :accept (:ok))
                    (:set (have 0)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ;; a group nothing was accepted into: 0 high + 1 high, high 0
             ((:absent) (:do (rc) (fn2-read-release (+ 1 (* 2 row-slot))) :accept (:ok))
                        (:do (tc) (fn2-cursor-tail (fn2-cursor-list-variant row-k0 row-a0) 0 1 0 row-posting
                                                   row-tx-slot row-tx-gen
                                                   :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                         :accept (:ok))
                        (:set (have 0)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
  ;; LIST's page: a row needs its room (a page with rows breaks before one)
  (list-render :on-refusal ((:stop :machine-phase))
     (:cond ((equal row-have 1) (:goto list-key))
            ((equal row-have 2) (:goto list-counts))
            ((and (< row-roff (nfix (fn2-cursor-tx-fill row-tx-slot)))
                  (< (nfix (fn2-cursor-tx-cap row-tx-slot))
                     (+ (nfix (fn2-cursor-tx-fill row-tx-slot)) *fn2-cursor-list-room*)))
             (:goto hand))
            (t (:goto list-step))))
  ;; NEWGROUPS: 231 status line and terminator (no group creation timestamps stored)
  (newgroups-done :on-refusal ((:stop :machine-phase))
     (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :listed) row-mask 0 0 0
                                 row-tx-slot row-tx-gen 0 0 row-tx-slot row-tx-gen
                                 :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:do (c2) (fn2-cursor-put-line 3 0 row-tx-slot row-tx-gen
                                    :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (done 1) (roff 0) (update *fn2-cursor-update-none*))
     (:goto hand))
  ;; NEWNEWS: scan groups on 2S, filter by wildmat, scan overview on 2S+1
  (newnews-start :on-refusal ((:stop :machine-phase))
     (:do (pc) (fn2-cursor-pad *fn2-cursor-key-room* row-tx-slot row-tx-gen
                               :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :listed) row-mask 0 0 0
                                 row-tx-slot row-tx-gen 0 0 row-tx-slot row-tx-gen
                                 :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:do (sc) (fn2-read-scan (* 2 row-slot) *fn2-groups-sid* row-tx-slot row-tx-gen row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:set (roff *fn2-cursor-key-room*) (have 0) (step 12) (update *fn2-cursor-update-none*))
     (:next :render) (:charge :bytes 1024 :steps *fn2-work-transition* :runnable t))
  (newnews-group-step :on-refusal ((:stop :machine-phase))
     (:do (nc) (fn2-read-scan-next (* 2 row-slot) *fn2-cursor-step-budget*)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:entry)
              (:let at (nfix (fn2-cursor-tx-fill row-tx-slot)))
              (:do (vc g) (fn2-read-value (* 2 row-slot) *fn2-groups-entry-field-group*) :accept (:ok))
              (:do (oc copied left) (fn2-read-octets (* 2 row-slot) *fn2-groups-entry-field-name* 0 *fn2-groups-name-max*
                                                     row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
               :accept (:ok))
              (:do (fc keep) (fn2-cursor-newnews-filter row-a0 row-b0 at (nfix copied)
                                                        row-rx-slot row-rx-gen row-tx-slot row-tx-gen
                                                        :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
               :accept (:ok))
              (:if keep
                   ((:set (lgroup g) (lo 1) (hi *fn2-none*) (have 1))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                   ((:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))))
             ((:end) (:goto end-list))
             (:otherwise (:stop :machine-phase)))))
  (newnews-ov-start :on-refusal ((:stop :machine-phase))
     (:do (c1) (fn2-read-key (+ 1 (* 2 row-slot)) ':lo 0 row-lgroup) :accept (:ok))
     (:do (c2) (fn2-read-key (+ 1 (* 2 row-slot)) ':lo 1 row-lo) :accept (:ok))
     (:do (c3) (fn2-read-key (+ 1 (* 2 row-slot)) ':hi 0 row-lgroup) :accept (:ok))
     (:do (c4) (fn2-read-key (+ 1 (* 2 row-slot)) ':hi 1 row-hi) :accept (:ok))
     (:do (c5) (fn2-read-range (+ 1 (* 2 row-slot)) *fn2-cursor-overview-sid*
                               *fn2-overview-entry-field-position* (if (equal row-pin 0) *fn2-none* row-pin))
      :accept (:ok))
     (:set (have 2) (next row-lo))
     (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
  (newnews-ov-step :on-refusal ((:stop :machine-phase))
     (:do (nc) (fn2-read-next (+ 1 (* 2 row-slot)) *fn2-cursor-step-budget*)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:entry) (:set (have 3)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:end) (:do (rc) (fn2-read-release (+ 1 (* 2 row-slot))) :accept (:ok))
                     (:set (have 0)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
  (newnews-ov-emit :on-refusal ((:stop :machine-phase))
     (:let at (nfix (fn2-cursor-tx-fill row-tx-slot)))
     (:let room (nfix (- (nfix (fn2-cursor-tx-cap row-tx-slot)) (+ at 32))))
     (:do (vc n) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-overview-entry-field-number*) :accept (:ok :stale)
      :why ":stale: the range restarts at the next number")
     (:if (eq vc :ok)
          ((:do (oc copied left) (fn2-read-octets (+ 1 (* 2 row-slot)) *fn2-overview-entry-field-line*
                                                  0 (min room 4096)
                                                  row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
            :accept (:ok))
           (:do (mc) (fn2-cursor-newnews-mid row-roff at (+ at (nfix copied))
                                             row-tx-slot row-tx-gen
                                             :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
            :accept (:ok))
           (:set (seen 1) (have 2) (next (+ 1 (nfix n))))
           (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((:do (rc) (fn2-read-release (+ 1 (* 2 row-slot))) :accept (:ok))
           (:set (lo row-next) (have 1)) (:charge :steps *fn2-work-transition* :runnable t))))
  (newnews-render :on-refusal ((:stop :machine-phase))
     (:cond ((equal row-have 1) (:goto newnews-ov-start))
            ((equal row-have 2) (:goto newnews-ov-step))
            ((and (< row-roff (nfix (fn2-cursor-tx-fill row-tx-slot)))
                  (< (nfix (fn2-cursor-tx-cap row-tx-slot))
                     (+ (nfix (fn2-cursor-tx-fill row-tx-slot)) *fn2-cursor-hdr-room*)))
             (:goto hand))
            ((equal row-have 3) (:goto newnews-ov-emit))
            (t (:goto newnews-group-step))))
  (render-step :on-refusal ((:stop :machine-phase))
     (:do (nc) (fn2-read-next (* 2 row-slot) *fn2-cursor-step-budget*)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:entry) (:set (have 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:end) (:cond ((and (equal row-step 6) (< 0 row-found)) (:goto end-last))
                            ((and (equal row-step 8) (equal row-seen 0)) (:goto end-match))
                            ((fn2-cursor-single-p row-tag) (:goto end-single))
                            ((and (equal row-seen 0) (not (equal row-tag *fn2-nntp-command-xpat*))) (:goto end-empty))
                            (t (:goto end-list))))
             (:otherwise (:stop :machine-phase)))))
  (render-walk :on-refusal ((:stop :machine-phase))
     (:do (vc n) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-number*) :accept (:ok :stale)
      :why ":stale: the walk restarts after the last number it remembered")
     (:if (eq vc :ok) ((:set (found n) (have 0) (next (+ 1 (nfix n)))) (:charge :steps *fn2-work-transition* :runnable t))
          ((:set (lo row-next)) (:goto range))))
  (render-match :on-refusal ((:stop :machine-phase))
     (:do (vc a) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-article*) :accept (:ok :stale)
      :why ":stale: the range restarts at the next number")
     (:if (not (eq vc :ok))
          ((:set (lo row-next)) (:goto range))
          ((:if (equal a row-spin)
                ((:set (have 2)) (:charge :steps *fn2-work-transition* :runnable t))
                ((:set (have 0)) (:charge :steps *fn2-work-transition* :runnable t))))))
  ;; the line copied into TX with room left for the 220/221/222/223 line, then
  ;; its Message-ID found and the reply rendered (5-step :do chain auto-split)
  (render-single :on-refusal ((:stop :machine-phase))
     (:let at (nfix (fn2-cursor-tx-fill row-tx-slot)))
     (:do (vc n) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-number*) :accept (:ok))
     (:do (oc copied left) (fn2-read-octets (* 2 row-slot) *fn2-overview-entry-field-line* 0
                                            (min 4096 (nfix (- (nfix (fn2-cursor-tx-cap row-tx-slot))
                                                               (+ at *fn2-cursor-single-room*))))
                                            row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:let roff (+ at (nfix copied)))
     (:let ncur (if (equal row-k0 *fn2-cursor-arg-span*) 0 n))
     (:do (mc ms ml) (fn2-cursor-mid row-tx-slot row-tx-gen at roff
                                     :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok)
      ;; :refused: no Message-ID field in the part of the line TX holds
      :case (((:refused) (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
                         (:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn
                                                     :ogen row-conn-gen)
                          :accept (:ok))
                         (:set (ncurrent ncur) (roff roff) (reply (fn2-cursor-reply-of row-tag :no-projection)) (lpos 0))
                         (:goto refuse))))
     (:if (or (equal row-tag *fn2-nntp-command-article*) (equal row-tag *fn2-nntp-command-head*)
              (equal row-tag *fn2-nntp-command-body*) (equal row-tag *fn2-nntp-command-xfn-zarticle*))
          ;; ARTICLE, HEAD, BODY, XFN-ZARTICLE: the article's location first; the 22x line
          ;; goes once its stored octets are leased and read (art-copy)
          ((:do (ac art) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-article*) :accept (:ok))
           (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
           (:set (ncurrent ncur) (roff roff) (lpos 0) (art art) (oat at) (mso ms) (mln ml) (said 0)
                 (update (if (equal row-k0 *fn2-cursor-arg-range*) *fn2-cursor-update-current* *fn2-cursor-update-none*))
                 (step 20))
           (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :found) row-mask ncur 0 0
                                       row-tx-slot row-tx-gen (nfix ms) (nfix ml) row-tx-slot row-tx-gen
                                       :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
            :accept (:ok))
           (:do (rc) (fn2-read-release (* 2 row-slot)) :accept (:ok))
           (:set (ncurrent ncur) (roff roff) (done 1) (lpos 0)
                 (update (if (or (equal row-tag *fn2-nntp-command-next*) (equal row-tag *fn2-nntp-command-last*)
                                 (equal row-k0 *fn2-cursor-arg-range*))
                             *fn2-cursor-update-current* *fn2-cursor-update-none*)))
           (:goto hand))))
  ;; the range goes on at the next number (the lease stays for the next row)
  (hdr-next :on-refusal ((:stop :machine-phase))
     (:do (fc) (fn2-cursor-xpat-filter row-tag row-a2 row-b2 row-lat row-oat
                                       row-rx-slot row-rx-gen row-tx-slot row-tx-gen
                                       :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (hmode 0) (hk 0) (ast 0) (step row-hstep) (seen 1) (have 0) (lpos 0))
     (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
  ;; the stored octets ended inside the header block, or there are none
  (hdr-end :on-refusal ((:stop :machine-phase))
     (:do (tc) (fn2-cursor-put-line 2 0 row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:goto hdr-next))
  ;; HDR's field in the stored octets read so far (the header block ends
  ;; the scan, so the body is never read); a page breaks inside a long value
  (hdr-copy :on-refusal ((:stop :machine-phase))
     (:let base (if (equal row-mkind 1) *fn2-commit-unit-bytes* 0))
     (:do (hc used st k) (fn2-cursor-hscan (+ base row-loff) (+ base row-plen) row-ast row-hk row-a0 row-b0 row-rx-slot row-rx-gen
                                          row-lslot row-lgen row-tx-slot row-tx-gen row-conn-kind row-conn row-conn-gen)
      :accept ()
      :case (((:full) (:if (equal row-tag *fn2-nntp-command-xpat*)
                           ((:set (step 25)) (:goto art-fail))
                           ((:set (loff (+ row-loff (nfix used))) (ast st) (hk k))
                            (:goto hand))))
             ((:ok) (:cond ((< (+ row-loff (nfix used)) row-plen)
                            (:set (loff (+ row-loff (nfix used))) (ast st) (hk k))
                            (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                           ((< (+ row-apos row-plen) row-alen)
                            (:set (loff 0) (apos (+ row-apos row-plen)) (ast st) (hk k) (step 23))
                            (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                           (t (:goto hdr-end))))
             ((:done) (:goto hdr-next))
             (:otherwise (:stop :machine-phase)))))
  ;; ARTICLE/HEAD/BODY's stored octets (D6 3/n, S-ARTICLE-LOCATION): the
  ;; article row through read row 2S+1 (its location), a lease of one
  ;; storage unit, B's block read of each unit into it, and the octets
  ;; dot-stuffed onto TX page by page; the terminator, the lease returned.
  (art-key :on-refusal ((:stop :machine-phase))
     (:do (kc) (fn2-read-key (+ 1 (* 2 row-slot)) ':lo *fn2-article-entry-field-article* row-art) :accept (:ok))
     (:set (step 21)) (:charge :steps *fn2-work-transition* :runnable t))
  (art-refuse :on-refusal ((:stop :machine-phase))
     (:if (equal row-hmode 1)
          ;; HDR over an article with no stored octets: an empty value
          ((:goto hdr-end))
          ((:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
            :accept (:ok))
           (:set (reply (fn2-cursor-reply-of row-tag :no-projection)) (step 0))
           (:goto refuse))))
  (art-lookup :on-refusal ((:stop :machine-phase))
     (:do (lc) (fn2-read-lookup (+ 1 (* 2 row-slot)) *fn2-txn-article-sid* *fn2-cursor-step-budget*)
      :accept ()
      :case (((:ok) (:do (c1 u) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-location-unit*) :accept (:ok))
                    (:do (c2 e) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-location-epoch*) :accept (:ok))
                    (:do (c3 a) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-location-allocation*) :accept (:ok))
                    (:do (c4 b) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-bytes*) :accept (:ok))
                    (:do (c5 k) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-location-kind*) :accept (:ok))
                    (:do (rc) (fn2-read-release (+ 1 (* 2 row-slot))) :accept (:ok))
                    (:if (and (or (equal k *fn2-txn-location-raw-source*) (equal k *fn2-txn-location-source-manifest*))
                              (< 0 (nfix b)))
                         ((:set (lunit u) (lepoch e) (lalloc a) (alen b) (apos 0)
                                (mkind (if (equal k *fn2-txn-location-source-manifest*) 1 0)) (mpos 0) (bready 0) (mread 0)
                                (ast (if (equal row-hmode 1) 0
                                       (+ 2 (* 4 (cond ((equal row-tag *fn2-nntp-command-head*) 1)
                                                       ((equal row-tag *fn2-nntp-command-body*) 2)
                                                       (t 0))))))
                                (step 22))
                          (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                         ((:goto art-refuse))))
             ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:absent) (:do (rc) (fn2-read-release (+ 1 (* 2 row-slot))) :accept (:ok)) (:goto art-refuse))
             (:otherwise (:stop :machine-phase)))))
  (art-lease :on-refusal ((:stop :machine-phase))
     (:let class (fn2-cursor-lease-class))
     (:cond ((equal row-lease *fn2-cursor-lease-held*)
             (:set (step 23)) (:charge :steps *fn2-work-transition* :runnable t))
            ((null class) (:goto art-refuse))
            (t
           (:do (code ls lg) (fn2-cursor-lease-reserve class) :effects ((:acquire (:storage-window)))
            :case (((:exhausted) (:park :pool class :steps *fn2-work-transition*))
                   (:otherwise (:goto art-refuse))))
           (:set (lslot ls) (lgen lg) (lease *fn2-cursor-lease-held*) (step 23))
           (:charge :steps *fn2-work-transition* :runnable t))))
  ;; a failed read: the lease returned; before the 22x line the reply is
  ;; refused; after it the reply cannot be completed, so what TX holds is
  ;; dropped and the connection closes (UPDATE close; this replaced the
  ;; core's stop :machine-phase)
  (art-fail :on-refusal ((:stop :machine-phase))
     (:cond ((equal row-lease *fn2-cursor-lease-held*)
             (:do (lc) (fn2-cursor-lease-release row-lslot row-lgen) :effects ((:release (:storage-window))) :accept (:ok :retired)
              :why ":retired: the lease's slot reached its generation limit and leaves the pool")
             (:set (lease *fn2-cursor-lease-none*) (lslot *fn2-none*) (lgen 0))
             (:charge :steps *fn2-work-transition* :runnable t))
            ((equal row-said 0) (:goto art-refuse))
            (t (:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                :accept (:ok))
               (:set (done 1) (roff 0) (update *fn2-cursor-update-close*) (step 0))
               (:goto hand))))
  ;; one extent's octets are read unit by unit from LUNIT; octets named
  ;; through a source manifest read the manifest's unit holding the next
  ;; block's entry (art-entry decodes it), then the block, with no reset
  ;; between: the block lands at the lease's fill, [4096, 4096+BLEN), beside
  ;; the entry it is checked against (:fetch)
  (art-read :on-refusal ((:stop :machine-phase))
     (:let pos row-apos)
     (:let off (mod pos *fn2-commit-unit-bytes*))
     (:let len (min (- *fn2-commit-unit-bytes* off) (nfix (- row-alen pos))))
     (:if (not (and (natp budget) (< 0 budget))) ((:yield))
          ((:cond
            ((equal row-mkind 0)
             (:do (zc) (fn2-cursor-reset row-lslot row-lgen) :accept (:ok))
             (:issue (fn2-block-read (+ row-lunit (floor pos *fn2-commit-unit-bytes*)) row-lepoch row-lalloc off len
                                     row-lslot row-lgen :principal row-principal-slot)
              :ok ((:set (plen len) (loff 0) (rready 0) (mread 0)) (:next :fetch)
                   (:wait :completion :bytes 4096 :steps *fn2-work-small*))))
            ((equal row-bready 0)
             (:do (zc) (fn2-cursor-reset row-lslot row-lgen) :accept (:ok))
             (:issue (fn2-block-read (+ row-lunit (floor row-mpos *fn2-commit-unit-bytes*)) row-lepoch row-lalloc
                                     0 *fn2-commit-unit-bytes* row-lslot row-lgen :principal row-principal-slot)
              :ok ((:set (plen *fn2-commit-unit-bytes*) (loff 0) (rready 0) (mread 1)) (:next :fetch)
                   (:wait :completion :bytes 4096 :steps *fn2-work-small*))))
            (t
             (:issue (fn2-block-read row-bunit row-bepoch row-balloc 0 row-blen
                                     row-lslot row-lgen :principal row-principal-slot)
              :ok ((:set (plen row-blen) (loff 0) (rready 0) (mread 0) (bready 0)) (:next :fetch)
                   (:wait :completion :bytes 4096 :steps *fn2-work-small*))))))))
  ;; the next block's manifest entry: it must name the octets from APOS on
  (art-entry :on-refusal ((:stop :machine-phase))
     (:do (ec mp lo len unit epoch alloc hoff cvoff)
          (fn2-cursor-manifest-entry (+ 1 (* 2 row-slot)) row-lslot row-lgen row-mpos row-alen)
      :accept (:ok :bounds) :why ":bounds: a manifest that does not name the next octets fails the read")
     (:if (and (eq ec :ok) (equal lo row-apos) (< 0 len) (<= len *fn2-commit-unit-bytes*)
               (<= (+ row-apos len) row-alen) (unsigned-byte-p 32 hoff) (unsigned-byte-p 32 cvoff))
          ((:set (mpos mp) (bunit unit) (bepoch epoch) (balloc alloc) (blen len) (bhash hoff) (bcv cvoff)
                 (bready 1) (step 23))
           (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
          ((:set (step 25)) (:goto art-fail))))
     ;; :stale or :bounds (a location the allocator no longer names) stops
     ;; the core by the arm's refusal: the store contradicts its own row
  (art-end :on-refusal ((:stop :machine-phase))
     (:do (tc) (fn2-cursor-put-line 3 0 row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:if (equal row-lease *fn2-cursor-lease-held*)
          ((:do (lc) (fn2-cursor-lease-release row-lslot row-lgen) :effects ((:release (:storage-window))) :accept (:ok :retired)
            :why ":retired: the lease's slot reached its generation limit and leaves the pool")
           (:set (lease *fn2-cursor-lease-none*) (lslot *fn2-none*) (lgen 0) (done 1) (step 0))
           (:goto hand))
          ((:set (done 1) (step 0))
           (:goto hand))))
  (art-copy :on-refusal ((:stop :machine-phase))
     (:cond ((equal row-hmode 1) (:goto hdr-copy))
            ((equal row-said 0)
             (:do (code) (fn2-cursor-art-open row-tag (fn2-cursor-reply-of row-tag :found) row-mask row-ncurrent
                                              (not (equal row-tag *fn2-nntp-command-body*))
                                              row-oat row-roff row-mso row-mln row-tx-slot row-tx-gen
                                              :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
              :accept (:ok))
             (:set (said 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
            (t (:do (sc used st) (fn2-cursor-stuff (+ (if (equal row-mkind 1) *fn2-commit-unit-bytes* 0) row-loff)
                                                   (+ (if (equal row-mkind 1) *fn2-commit-unit-bytes* 0) row-plen)
                                                   row-ast row-lslot row-lgen
                                                   row-tx-slot row-tx-gen row-conn-kind row-conn row-conn-gen)
                :accept ()
                :case (((:full) (:set (loff (+ row-loff (nfix used))) (ast st))
                                (:goto hand))
                       ((:ok) (:cond ((< (+ row-loff (nfix used)) row-plen)
                                      (:set (loff (+ row-loff (nfix used))) (ast st))
                                      (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                                     ((< (+ row-apos row-plen) row-alen)
                                      (:set (loff 0) (apos (+ row-apos row-plen)) (ast st) (step 23))
                                      (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                                     (t (:set (ast st)) (:goto art-end))))
                       ((:end) (:set (ast st)) (:goto art-end))
                       (:otherwise (:stop :machine-phase)))))))
  (render-number :on-refusal ((:stop :machine-phase))
     (:do (vc n) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-number*) :accept (:ok :stale)
      :why ":stale: the range restarts at the next number")
     (:if (eq vc :ok)
          ((:do (code) (fn2-cursor-put-line 1 (nfix n) row-tx-slot row-tx-gen
                                            :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
            :accept (:ok))
           (:set (have 0) (next (+ 1 (nfix n)))) (:charge :bytes 64 :steps *fn2-work-transition* :runnable t))
          ((:set (lo row-next)) (:goto range))))
  (render-piece :on-refusal ((:stop :machine-phase))
     (:let at (nfix (fn2-cursor-tx-fill row-tx-slot)))
     (:let room (nfix (- (nfix (fn2-cursor-tx-cap row-tx-slot)) (+ at 2))))
     (:do (vc n) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-number*) :accept (:ok))
     (:do (oc copied left) (fn2-read-octets (* 2 row-slot) *fn2-overview-entry-field-line* row-lpos (min room 4096)
                                            row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:if (equal left 0)
          ((:do (c2) (fn2-cursor-put-line 2 at row-tx-slot row-tx-gen
                                          :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
            :accept (:ok))
           (:set (seen 1) (have 0) (lpos 0) (next (+ 1 (nfix n))))
           (:charge :bytes 6144 :steps *fn2-work-transition* :runnable t))
          ((:set (seen 1) (lpos (+ row-lpos (nfix copied))) (roff 0)) (:goto hand))))
  ;; "N TAB line CR LF", the line copied in pieces that fit TX: a piece that
  ;; leaves part of the line breaks the page, and the next page goes on from
  ;; LPOS (a row longer than TX is split, never refused)
  (render-row :on-refusal ((:stop :machine-phase))
     (:do (vc n) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-number*) :accept (:ok :stale)
      :why ":stale: the range restarts at the next number")
     (:if (eq vc :ok)
          ((:if (equal row-lpos 0)
                ((:do (c1) (fn2-cursor-put-line 0 (if (and (equal row-step 8) (not (equal row-lgroup row-group)))
                                                      0 (nfix n))
                                                row-tx-slot row-tx-gen
                                                :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                  :accept (:ok))
                 (:goto render-piece))
                ((:goto render-piece))))
          ((:set (lo row-next)) (:goto range))))
  ;; HDR/XHDR/XPAT: "<num-or-id> <value> CR LF"
  (render-hdr-val :on-refusal ((:stop :machine-phase))
     (:let at (nfix (fn2-cursor-tx-fill row-tx-slot)))
     (:let room (nfix (- (nfix (fn2-cursor-tx-cap row-tx-slot)) (+ at 32))))
     (:do (vc n) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-number*) :accept (:ok))
     (:do (oc copied left) (fn2-read-octets (* 2 row-slot) *fn2-overview-entry-field-line* 0 (min room 4096)
                                            row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:do (hc) (fn2-cursor-hdr-val row-tag row-a0 row-b0 at (+ at (nfix copied))
                                   row-rx-slot row-rx-gen row-tx-slot row-tx-gen
                                   :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept ()
      :case (((:ok) (:do (fc) (fn2-cursor-xpat-filter row-tag row-a2 row-b2 row-lat at
                                                      row-rx-slot row-rx-gen row-tx-slot row-tx-gen
                                                      :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                     :accept (:ok))
                    (:set (seen 1) (have 0) (lpos 0) (next (+ 1 (nfix n))))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ;; a header the overview lacks: the article's stored octets
             ;; (art-key on), scanned for it (hdr-copy); the range's step
             ;; comes back after (hdr-next); the 225 line went, so a failed
             ;; read closes the connection (SAID)
             ((:stored)
              (:do (ac art) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-article*) :accept (:ok))
              (:set (art art) (oat at) (hmode 1) (hk 0) (hstep row-step) (said 1) (next (+ 1 (nfix n))) (step 20))
              (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
  (render-hdr :on-refusal ((:stop :machine-phase))
     (:let lat (nfix (fn2-cursor-tx-fill row-tx-slot)))
     (:do (vc n) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-number*) :accept (:ok :stale)
      :why ":stale: the range restarts at the next number")
     (:if (eq vc :ok)
          ((:do (lc) (fn2-cursor-hdr-label row-tag
                                           (if (and (equal row-step 8) (not (equal row-lgroup row-group)))
                                               0 (nfix n))
                                           row-k1 row-a1 row-b1
                                           row-rx-slot row-rx-gen row-tx-slot row-tx-gen
                                           :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
            :accept (:ok))
           (:set (lat lat))
           (:goto render-hdr-val))
          ((:set (lo row-next)) (:goto range)))))
 :arms
 ((:free (:idle))
  ;; the line, parsed again under the connection's owner
  (:select :on-refusal ((:stop :machine-phase))
   (:do (pcode ptag pk0 pa0 pb0 pk1 pa1 pb1 pa2 pb2)
        (fn2-cursor-parse row-line-s row-line-e row-mask row-rx-slot row-rx-gen
                          :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
    :accept (:ok))
   (:set (tag ptag) (k0 pk0) (a0 pa0) (b0 pb0) (k1 pk1) (a1 pa1) (b1 pb1) (a2 pa2) (b2 pb2) (step 0) (turn 1))
   (:next :seek) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
  (:seek :on-refusal ((:stop :machine-phase))
   (:cond
    ;; LIST ACTIVE, ACTIVE.TIMES, COUNTS, NEWSGROUPS, SUBSCRIPTIONS: the group directory
    ((equal row-tag *fn2-nntp-command-list*) (:goto list-start))
    ((equal row-tag *fn2-nntp-command-newgroups*) (:goto newgroups-done))
    ((equal row-tag *fn2-nntp-command-newnews*) (:goto newnews-start))
    ;; GROUP g / LISTGROUP g: the name in the group directory
    ((and (fn2-cursor-selects-p row-tag) (equal row-k0 *fn2-cursor-arg-span*) (equal row-step 0)) (:goto seek-name))
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 1)) (:goto seek-group))
    ;; the group's counts: count, low, high (an empty group 0, high + 1, high)
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 2)) (:goto seek-counts-key))
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 3)) (:goto seek-counts))
    ;; the 211 line; GROUP is done, LISTGROUP lists the numbers in its range
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 4)) (:goto seek-selected))
    ;; LISTGROUP with no name lists the selected group, its name read back
    ;; from the group directory first
    ((and (fn2-cursor-selects-p row-tag) (equal row-group 0))
     (:set (reply (fn2-cursor-reply-of row-tag :no-group-selected))) (:goto refuse))
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 0)) (:goto lg-start))
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 10)) (:goto lg-step))
    ((fn2-cursor-selects-p row-tag) (:goto lg-found))
    ;; STAT/ARTICLE/HEAD/BODY/OVER <id>, HDR/XHDR <field> <id>, CHECK/IHAVE <id>: the identity read
    ((or (and (or (fn2-cursor-single-p row-tag) (equal row-tag *fn2-nntp-command-over*)
                  (equal row-tag *fn2-nntp-command-check*) (equal row-tag *fn2-nntp-command-ihave*))
              (equal row-k0 *fn2-cursor-arg-span*))
         (and (fn2-cursor-hdr-p row-tag) (equal row-k1 *fn2-cursor-arg-span*)))
     (:goto seek-identity))
    ;; every other command reads the selected group
    ((equal row-group 0) (:set (reply (fn2-cursor-reply-of row-tag :no-group-selected))) (:goto refuse))
    ;; HDR/XHDR [range]: the current article when no second argument
    ((fn2-cursor-hdr-p row-tag)
     (:if (not (equal row-k1 *fn2-cursor-arg-range*))
          ((:if (equal row-current 0) ((:set (reply (fn2-cursor-reply-of row-tag :no-current))) (:goto refuse))
                ((:set (lo row-current) (hi row-current) (step 5)) (:goto over-head))))
          ((:set (lo row-a1) (hi row-b1) (step 5)) (:goto over-head))))
    ;; NEXT: the first article after the current one
    ((equal row-tag *fn2-nntp-command-next*)
     (:if (equal row-current 0) ((:set (reply (fn2-cursor-reply-of row-tag :no-current))) (:goto refuse))
          ((:set (lo (+ 1 row-current)) (hi *fn2-none*) (step 5)) (:goto range))))
    ;; LAST: the last article before the current one (walked forward, then read again)
    ((equal row-tag *fn2-nntp-command-last*)
     (:cond ((equal row-current 0) (:set (reply (fn2-cursor-reply-of row-tag :no-current))) (:goto refuse))
            ((<= row-current 1) (:set (reply (fn2-cursor-reply-of row-tag :none))) (:goto refuse))
            (t (:set (lo 1) (hi (- row-current 1)) (found 0) (step 6)) (:goto range))))
    ;; STAT [n], OVER/XOVER [range]: the current article when no argument
    ((not (equal row-k0 *fn2-cursor-arg-range*))
     (:if (equal row-current 0) ((:set (reply (fn2-cursor-reply-of row-tag :no-current))) (:goto refuse))
          ((:set (lo row-current) (hi row-current) (step 5))
           (:if (fn2-cursor-overview-p row-tag) ((:goto over-head)) ((:goto range))))))
    (t (:set (lo row-a0) (hi (if (fn2-cursor-overview-p row-tag) row-b0 row-a0)) (step 5))
       (:if (fn2-cursor-overview-p row-tag) ((:goto over-head)) ((:goto range))))))
  ;; one range step, or the delivered entry rendered (a page breaks before a
  ;; row TX has no room for)
  (:render :on-refusal ((:stop :machine-phase))
   (:cond
    ((equal row-step 20) (:goto art-key))
    ((equal row-step 21) (:goto art-lookup))
    ((equal row-step 22) (:goto art-lease))
    ((equal row-step 23) (:goto art-read))
    ((equal row-step 24) (:goto art-copy))
    ((equal row-step 25) (:goto art-fail))
    ((equal row-step 26) (:goto art-entry))
    ((equal row-tag *fn2-nntp-command-list*) (:goto list-render))
    ((equal row-tag *fn2-nntp-command-newnews*) (:goto newnews-render))
    ((equal row-have 0) (:goto render-step))
    ;; LAST's walk: remember the number, step on
    ((equal row-step 6) (:goto render-walk))
    ((and (equal row-step 8) (< row-have 2)) (:goto render-match))
    ;; NEXT, LAST, STAT, ARTICLE, HEAD, BODY
    ((fn2-cursor-single-p row-tag) (:goto render-single))
    ;; a page break: TX has no room for another row
    ((and (< 0 (nfix (fn2-cursor-tx-fill row-tx-slot)))
          (< (nfix (fn2-cursor-tx-cap row-tx-slot))
             (+ (nfix (fn2-cursor-tx-fill row-tx-slot))
                (if (equal row-tag *fn2-nntp-command-xpat*)
                    2048
                  (if (fn2-cursor-hdr-p row-tag) *fn2-cursor-hdr-room* *fn2-cursor-row-room*)))))
     (:set (roff 0)) (:goto hand))
    ;; LISTGROUP: the number
    ((equal row-tag *fn2-nntp-command-listgroup*) (:goto render-number))
    ;; HDR/XHDR: "<num-or-id> <value>"
    ((fn2-cursor-hdr-p row-tag) (:goto render-hdr))
    ;; OVER/XOVER: a row, "N TAB line" (the 224 line is written before the range)
    (t (:goto render-row))))
  ;; TX is the connection's until it sets TURN again
  (:send
   (:cond ((equal row-cancel 1) (:next :finish) (:charge :steps *fn2-work-transition* :runnable t))
          ((equal row-turn 0) (:charge :steps *fn2-work-empty*))
          ((equal row-done 1) (:next :finish) (:charge :steps *fn2-work-transition* :runnable t))
          (t (:next :render) (:charge :steps *fn2-work-transition* :runnable t))))
  ;; B's block read is in flight; its result decides: a manifest unit is
  ;; decoded (art-entry); a block named through it is checked against its
  ;; entry by B's completion (BLAKE3 and chaining value), a mismatch failing
  ;; the read as an I/O failure does (art-fail: refused before the 22x line,
  ;; the connection closed after it)
  (:fetch :on-refusal ((:stop :machine-phase))
   (:cond ((equal row-rready 0) (:charge :steps *fn2-work-poll*))
          ((not (and (equal row-revent *fn2-event-read-result*) (equal row-routcome *fn2-outcome-done*)))
           (:set (rready 0) (step 25)) (:next :render) (:charge :steps *fn2-work-transition* :runnable t))
          ((equal row-mread 1)
           (:set (rready 0) (mread 0) (step (if (equal row-rcount row-plen) 26 25))) (:next :render)
           (:charge :steps *fn2-work-transition* :runnable t))
          (t
           (:do (dc) (fn2-block-read-done row-rcount row-plen (if (equal row-mkind 1) 1 0) row-lslot row-lgen
                                          (if (equal row-mkind 1) *fn2-commit-unit-bytes* 0) row-bhash row-bcv
                                          (floor row-apos *fn2-commit-unit-bytes*))
            :accept (:ok :io :hash)
            :why ":io: fewer octets than asked; :hash: a block its manifest entry does not name (S9a)")
           (:set (rready 0) (step (if (eq dc :ok) 24 25))) (:next :render)
           (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))))
  (:finish :on-refusal ((:stop :machine-phase))
   (:do (rc1) (fn2-read-release (* 2 row-slot)) :accept (:ok))
   (:do (rc2) (fn2-read-release (+ 1 (* 2 row-slot))) :accept (:ok))
   (:if (equal row-lease *fn2-cursor-lease-held*)
        ((:do (lc) (fn2-cursor-lease-release row-lslot row-lgen) :effects ((:release (:storage-window))) :accept (:ok :retired)
      :why ":retired: the lease's slot reached its generation limit and leaves the pool")
         (:set (lease *fn2-cursor-lease-none*) (lslot *fn2-none*) (lgen 0))
         (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
        ((:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))
  (:draining
   (:let next (fn2-cursor-free-head *fn2-cursor-admission-ordinal*))
   (:let retire (>= row-generation (fn2-cursor-gen-limit)))
   (:set (generation (if retire row-generation (+ 1 row-generation))) (conn *fn2-none*) (conn-gen 0)
         (rx-slot *fn2-none*) (rx-gen 0) (tx-slot *fn2-none*) (tx-gen 0) (next-free next)
         (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-cursor-reclaim id *fn2-cursor-admission-ordinal* retire))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle)))
 :observes
 ((:read-result (:set (revent event) (routcome outcome) (rcount count) (rready 1)) (:wake))))
