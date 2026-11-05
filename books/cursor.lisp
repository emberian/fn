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
  (or (equal tag *fn2-nntp-command-hdr*) (equal tag *fn2-nntp-command-xhdr*)))
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
;; NEXT, LAST and STAT: one article, its 223 line.
(defun fn2-cursor-single-p (tag)
  (declare (xargs :guard t))
  (or (equal tag *fn2-nntp-command-next*) (equal tag *fn2-nntp-command-last*) (equal tag *fn2-nntp-command-stat*)
      (equal tag *fn2-nntp-command-article*) (equal tag *fn2-nntp-command-head*) (equal tag *fn2-nntp-command-body*)))
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
    (declare (ignore nargs f2 a2 b2 f3 a3 b3))
    (let ((ok (and (eq code :ok) (natp tag) (< tag 256))))
      (mv (if ok :ok :refused) (if ok tag 0)
          (fn2-cursor-arg-kind f0) (nfix a0) (if (eq f0 :number) (nfix a0) (nfix b0))
          (fn2-cursor-arg-kind f1) (nfix a1) (if (eq f1 :number) (nfix a1) (nfix b1))))))

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
                                      fn2-pool-slot-capacity))))
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
;; The lease's pool class: the smallest that holds one storage unit.
(defun fn2-cursor-lease-class-of (fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-pool-class-for *fn2-commit-unit-bytes* fn2-pool))

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
                                      fn2-nntp-reply-command fn2-nntp-reply-layer))))
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
        (if (and (equal (nfix tag) *fn2-nntp-command-xhdr*) (equal (nfix k1) *fn2-cursor-arg-span*))
            (fn2-gram-put-span (nfix b1) (nfix a1) (nfix rslot) (nfix rgen) tslot tgen okind oslot ogen fn2-pool)
          (fn2-gram-put-number (if (equal (nfix k1) *fn2-cursor-arg-span*) 0 (nfix n))
                               tslot tgen okind oslot ogen fn2-pool)))
       ((unless (eq code :ok)) (mv code fn2-pool)))
    (fn2-gram-put 32 tslot tgen okind oslot ogen fn2-pool)))
(fn2-pool-preserves fn2-cursor-pool-hdr-label (tag n k1 a1 b1 rslot rgen tslot tgen okind oslot ogen fn2-pool)
  :position 1 :rows nil)
(in-theory (disable fn2-cursor-pool-hdr-label))

(defun fn2-cursor-ci-span-eq-p (len s1 slot1 gen1 s2 slot2 gen2 okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix len)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp len) (natp s1) (natp s2))))
  (if (zp len) t
    (mv-let (ok1 b1) (fn2-gram-read slot1 gen1 (nfix s1) okind oslot ogen fn2-pool)
      (mv-let (ok2 b2) (fn2-gram-read slot2 gen2 (nfix s2) okind oslot ogen fn2-pool)
        (and ok1 ok2 (= (fn2-gram-upcase b1) (fn2-gram-upcase b2))
             (fn2-cursor-ci-span-eq-p (- len 1) (+ 1 (nfix s1)) slot1 gen1 (+ 1 (nfix s2)) slot2 gen2
                                      okind oslot ogen fn2-pool))))))
(in-theory (disable fn2-cursor-ci-span-eq-p))

(defun fn2-cursor-skip-wsp (fuel i end slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix fuel)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp fuel) (natp i) (natp end))))
  (if (or (zp fuel) (>= (nfix i) (nfix end))) (nfix i)
    (mv-let (ok b) (fn2-gram-read slot gen (nfix i) okind oslot ogen fn2-pool)
      (if (and ok (or (= b 32) (= b 9)))
          (fn2-cursor-skip-wsp (- fuel 1) (+ 1 (nfix i)) end slot gen okind oslot ogen fn2-pool)
        (nfix i)))))
(defthm fn2-cursor-skip-wsp-natp
  (natp (fn2-cursor-skip-wsp fuel i end slot gen okind oslot ogen fn2-pool))
  :rule-classes :type-prescription)
(in-theory (disable fn2-cursor-skip-wsp))

(defun fn2-cursor-scan-extra-hdr (fuel i to a0 b0 rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix fuel)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp fuel) (natp i) (natp to) (natp a0) (natp b0))))
  (if (or (zp fuel) (>= (nfix i) (nfix to))) (mv nil 0 0)
    (mv-let (has-lf lf-pos) (fn2-cursor-next-lf (nfix i) (nfix to) tslot tgen okind oslot ogen fn2-pool)
      (let* ((line-e (if has-lf lf-pos (nfix to)))
             (val-e (if (< (nfix i) line-e)
                        (mv-let (okc cb) (fn2-gram-read tslot tgen (- line-e 1) okind oslot ogen fn2-pool)
                          (if (and okc (= cb 13)) (- line-e 1) line-e))
                      line-e)))
        (if (<= val-e (nfix i))
            (mv nil 0 0)
          (mv-let (okcol col-pos) (fn2-gram-read tslot tgen (+ (nfix i) (nfix b0)) okind oslot ogen fn2-pool)
            (if (and (<= (+ (nfix i) (nfix b0) 1) val-e)
                     okcol (= col-pos 58)
                     (fn2-cursor-ci-span-eq-p (nfix b0) (nfix a0) rslot rgen (nfix i) tslot tgen
                                              okind oslot ogen fn2-pool))
                (let ((vs (fn2-cursor-skip-wsp (nfix (- val-e (+ (nfix i) (nfix b0) 1)))
                                               (+ (nfix i) (nfix b0) 1) val-e tslot tgen
                                               okind oslot ogen fn2-pool)))
                  (mv t vs (max vs val-e)))
              (if has-lf
                  (fn2-cursor-scan-extra-hdr (- fuel 1) (+ 1 lf-pos) to a0 b0 rslot rgen tslot tgen
                                             okind oslot ogen fn2-pool)
                (mv nil 0 0)))))))))
(defthm fn2-cursor-scan-extra-hdr-types
  (and (natp (mv-nth 1 (fn2-cursor-scan-extra-hdr fuel i to a0 b0 rslot rgen tslot tgen okind oslot ogen fn2-pool)))
       (natp (mv-nth 2 (fn2-cursor-scan-extra-hdr fuel i to a0 b0 rslot rgen tslot tgen okind oslot ogen fn2-pool))))
  :hints (("Goal" :in-theory (disable fn2-gram-read fn2-cursor-ci-span-eq-p nfix))))
(in-theory (disable fn2-cursor-scan-extra-hdr))

(local (in-theory (disable fn2-gram-match)))
(defun fn2-cursor-pool-hdr-val (a0 b0 at to rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp a0) (natp b0) (natp at) (natp to))))
  (let ((a0 (nfix a0)) (b0 (nfix b0)) (at (nfix at)) (to (nfix to)))
    (if (or (fn2-gram-match a0 b0 ":FN-VERIFIED" rslot rgen okind oslot ogen fn2-pool)
            (fn2-gram-match a0 b0 ":FN-CONTROL" rslot rgen okind oslot ogen fn2-pool)
            (fn2-gram-match a0 b0 ":FN-ENROLLMENT" rslot rgen okind oslot ogen fn2-pool))
        (b* ((fn2-pool (fn2-cursor-truncate-to at tslot tgen okind oslot ogen fn2-pool))
             ((mv code fn2-pool) (fn2-answer-put-text 0 "absent no-field" tslot tgen okind oslot ogen fn2-pool))
             ((unless (eq code :ok)) (mv code fn2-pool)))
          (fn2-gram-put-crlf tslot tgen okind oslot ogen fn2-pool))
      (b* (((mv has-lf lf-pos) (fn2-cursor-next-lf at to tslot tgen okind oslot ogen fn2-pool))
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
                  (has-lf
                   (mv-let (found es ee)
                     (fn2-cursor-scan-extra-hdr (nfix (- to (+ 1 lf-pos))) (+ 1 lf-pos) to
                                                a0 b0 rslot rgen tslot tgen okind oslot ogen fn2-pool)
                     (if found (mv es (max es ee)) (mv at at))))
                  (t (mv at at)))))
        (fn2-cursor-move-line vs (nfix (- ve vs)) at tslot tgen okind oslot ogen fn2-pool)))))
(fn2-pool-preserves fn2-cursor-pool-hdr-val (a0 b0 at to rslot rgen tslot tgen okind oslot ogen fn2-pool)
  :position 1 :rows nil
  :hints (("Goal" :in-theory (disable fn2-gram-match fn2-cursor-next-tab fn2-cursor-next-lf fn2-cursor-scan-extra-hdr
                                      fn2-cursor-truncate-to fn2-answer-put-text fn2-gram-put-crlf
                                      fn2-cursor-move-line nfix))))
(in-theory (disable fn2-cursor-pool-hdr-val))

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
 :doc "Extract the requested header or metadata value from an overview line and append CR LF.")
(defcost fn2-cursor-stuff :child fn2-cursor-pool-stuff :answers (:ok :full :end :fault) :faults (:fault) :bytes 8192
 :tables (fn2-core-pool)
 :doc "Copy at most 4,096 stored octets from the lease onto TX, dot-stuffed; (mv code used st).")
(defcost fn2-cursor-lease-reserve :child fn2-pool-reserve :answers (:ok :exhausted :bounds :state) :tables (fn2-core-pool)
 :doc "Reserve the cursor's read lease (one storage unit) under its own owner: (mv code slot gen).")
(defcost fn2-cursor-lease-release :child fn2-core-release-children :answers t :tables (fn2-core-pool fn2-core-control)
 :doc "Return the cursor's read lease.")
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
                            ((equal row-seen 0) (:goto end-empty))
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
              (equal row-tag *fn2-nntp-command-body*))
          ;; ARTICLE, HEAD, BODY: the article's location first; the 22x line
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
  ;; ARTICLE/HEAD/BODY's stored octets (D6 3/n, S-ARTICLE-LOCATION): the
  ;; article row through read row 2S+1 (its location), a lease of one
  ;; storage unit, B's block read of each unit into it, and the octets
  ;; dot-stuffed onto TX page by page; the terminator, the lease returned.
  (art-key :on-refusal ((:stop :machine-phase))
     (:do (kc) (fn2-read-key (+ 1 (* 2 row-slot)) ':lo *fn2-article-entry-field-article* row-art) :accept (:ok))
     (:set (step 21)) (:charge :steps *fn2-work-transition* :runnable t))
  (art-refuse :on-refusal ((:stop :machine-phase))
     (:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (reply (fn2-cursor-reply-of row-tag :no-projection)) (step 0))
     (:goto refuse))
  (art-lookup :on-refusal ((:stop :machine-phase))
     (:do (lc) (fn2-read-lookup (+ 1 (* 2 row-slot)) *fn2-txn-article-sid* *fn2-cursor-step-budget*)
      :accept ()
      :case (((:ok) (:do (c1 u) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-location-unit*) :accept (:ok))
                    (:do (c2 e) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-location-epoch*) :accept (:ok))
                    (:do (c3 a) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-location-allocation*) :accept (:ok))
                    (:do (c4 b) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-bytes*) :accept (:ok))
                    (:do (c5 k) (fn2-read-value (+ 1 (* 2 row-slot)) *fn2-article-entry-field-location-kind*) :accept (:ok))
                    (:do (rc) (fn2-read-release (+ 1 (* 2 row-slot))) :accept (:ok))
                    (:if (and (equal k *fn2-txn-location-raw-source*) (< 0 (nfix b)))
                         ((:set (lunit u) (lepoch e) (lalloc a) (alen b) (apos 0)
                                (ast (+ 2 (* 4 (cond ((equal row-tag *fn2-nntp-command-head*) 1)
                                                     ((equal row-tag *fn2-nntp-command-body*) 2)
                                                     (t 0)))))
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
  (art-read :on-refusal ((:stop :machine-phase))
     (:let pos row-apos)
     (:let off (mod pos *fn2-commit-unit-bytes*))
     (:let len (min (- *fn2-commit-unit-bytes* off) (nfix (- row-alen pos))))
     (:if (not (and (natp budget) (< 0 budget))) ((:yield))
          ((:do (zc) (fn2-cursor-reset row-lslot row-lgen) :accept (:ok))
           (:issue (fn2-block-read (+ row-lunit (floor pos *fn2-commit-unit-bytes*)) row-lepoch row-lalloc off len
                                   row-lslot row-lgen :principal row-principal-slot)
            :ok ((:set (plen len) (loff 0) (rready 0)) (:next :fetch)
                 (:wait :completion :bytes 4096 :steps *fn2-work-small*))))))
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
     (:cond ((equal row-said 0)
             (:do (code) (fn2-cursor-art-open row-tag (fn2-cursor-reply-of row-tag :found) row-mask row-ncurrent
                                              (not (equal row-tag *fn2-nntp-command-body*))
                                              row-oat row-roff row-mso row-mln row-tx-slot row-tx-gen
                                              :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
              :accept (:ok))
             (:set (said 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
            (t (:do (sc used st) (fn2-cursor-stuff row-loff row-plen row-ast row-lslot row-lgen
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
  ;; HDR/XHDR: "<num-or-id> <value> CR LF"
  (render-hdr-val :on-refusal ((:stop :machine-phase))
     (:let at (nfix (fn2-cursor-tx-fill row-tx-slot)))
     (:let room (nfix (- (nfix (fn2-cursor-tx-cap row-tx-slot)) (+ at 32))))
     (:do (vc n) (fn2-read-value (* 2 row-slot) *fn2-overview-entry-field-number*) :accept (:ok))
     (:do (oc copied left) (fn2-read-octets (* 2 row-slot) *fn2-overview-entry-field-line* 0 (min room 4096)
                                            row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:do (hc) (fn2-cursor-hdr-val row-a0 row-b0 at (+ at (nfix copied))
                                   row-rx-slot row-rx-gen row-tx-slot row-tx-gen
                                   :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (seen 1) (have 0) (lpos 0) (next (+ 1 (nfix n))))
     (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
  (render-hdr :on-refusal ((:stop :machine-phase))
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
           (:goto render-hdr-val))
          ((:set (lo row-next)) (:goto range)))))
 :arms
 ((:free (:idle))
  ;; the line, parsed again under the connection's owner
  (:select :on-refusal ((:stop :machine-phase))
   (:do (pcode ptag pk0 pa0 pb0 pk1 pa1 pb1)
        (fn2-cursor-parse row-line-s row-line-e row-mask row-rx-slot row-rx-gen
                          :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
    :accept (:ok))
   (:set (tag ptag) (k0 pk0) (a0 pa0) (b0 pb0) (k1 pk1) (a1 pa1) (b1 pb1) (step 0) (turn 1))
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
                (if (fn2-cursor-hdr-p row-tag) *fn2-cursor-hdr-room* *fn2-cursor-row-room*))))
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
  ;; B's block read is in flight; its result decides
  (:fetch :on-refusal ((:stop :machine-phase))
   (:cond ((equal row-rready 0) (:charge :steps *fn2-work-poll*))
          ((and (equal row-revent *fn2-event-read-result*) (equal row-routcome *fn2-outcome-done*)
                (equal row-rcount row-plen))
           (:set (rready 0) (step 24)) (:next :render) (:charge :steps *fn2-work-transition* :runnable t))
          (t (:set (rready 0) (step 25)) (:next :render) (:charge :steps *fn2-work-transition* :runnable t))))
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
