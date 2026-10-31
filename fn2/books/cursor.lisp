; The query cursor machine fn2-cursor (layer D, quest D6; fn2/docs/d-machines-
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
(include-book "txn")
(include-book "machines-c-read")
(include-book "machine-arms")
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
;; UPDATE: what the reply moves the connection's selection to.
(defconst *fn2-cursor-update-none* 0)
(defconst *fn2-cursor-update-current* 1)
(defconst *fn2-cursor-update-selection* 2)
;; Argument kinds after the parse: absent, a number or range (A..B), a
;; Message-ID or a token (the span A, length B in RX).
(defconst *fn2-cursor-arg-none* 0)
(defconst *fn2-cursor-arg-range* 1)
(defconst *fn2-cursor-arg-span* 2)

; ---------------------------------------------------------------------------
; Pure helpers over the command tag.
(defun fn2-cursor-selects-p (tag)
  (declare (xargs :guard t))
  (or (equal tag *fn2-nntp-command-group*) (equal tag *fn2-nntp-command-listgroup*)))
(defun fn2-cursor-overview-p (tag)
  (declare (xargs :guard t))
  (or (equal tag *fn2-nntp-command-over*) (equal tag *fn2-nntp-command-xover*)))
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
   ((equal tag *fn2-nntp-command-over*)
    (case what (:found *fn2-nntp-reply-over-overview*) (:no-group-selected *fn2-nntp-reply-over-no-group-selected*)
      (:no-current *fn2-nntp-reply-over-no-current*) (:none *fn2-nntp-reply-over-empty-range*)
      (:no-msgid *fn2-nntp-reply-over-no-msgid*)
      (otherwise *fn2-nntp-reply-over-no-projection*)))
   ((equal tag *fn2-nntp-command-xover*)
    (case what (:found *fn2-nntp-reply-xover-overview*) (:no-group-selected *fn2-nntp-reply-xover-no-group-selected*)
      (:no-current *fn2-nntp-reply-xover-no-current*) (:none *fn2-nntp-reply-xover-none-selected*)
      (otherwise *fn2-nntp-reply-xover-no-projection*)))
   (t 0)))
;; NEXT, LAST and STAT: one article, its 223 line.
(defun fn2-cursor-single-p (tag)
  (declare (xargs :guard t))
  (or (equal tag *fn2-nntp-command-next*) (equal tag *fn2-nntp-command-last*) (equal tag *fn2-nntp-command-stat*)))
(defcost fn2-cursor-selects-p :child fn2-cursor-selects-p :doc "GROUP or LISTGROUP.")
(defcost fn2-cursor-overview-p :child fn2-cursor-overview-p :doc "OVER or XOVER.")
(defcost fn2-cursor-single-p :child fn2-cursor-single-p :doc "NEXT, LAST or STAT.")
(defcost fn2-cursor-reply-of :child fn2-cursor-reply-of :doc "The reply a command tag gives for an outcome.")
(defthm fn2-cursor-reply-of-natp (natp (fn2-cursor-reply-of tag what)) :rule-classes :type-prescription)
(in-theory (disable fn2-cursor-reply-of))

; ---------------------------------------------------------------------------
; The cursor's pool operations, over fn2-pool only. Each writes at TX's fill
; (the typed renderer and fn2-gram-put append) under the owner it is given.

;; The line [s, e) of RX, parsed again: (mv code tag k0 a0 b0 k1 a1 b1), each
;; argument as its kind (*fn2-cursor-arg-...*) and its two values.
(defun fn2-cursor-arg-kind (f)
  (declare (xargs :guard t))
  (cond ((member-eq f '(:number :range)) *fn2-cursor-arg-range*)
        ((eq f :span) *fn2-cursor-arg-span*)
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

;; One typed status line (the grammar's renderer), its own preservation facts.
(defun fn2-cursor-render (cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n0) (natp n1) (natp n2) (natp soff) (natp slen))))
  (fn2-nntp-render cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-cursor-render (cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool)
  :position 1 :rows nil)
(in-theory (disable fn2-cursor-render))
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
(in-theory (disable fn2-cursor-parse-line fn2-cursor-mid-span fn2-cursor-pool-fill))

(defcost fn2-cursor-parse :child fn2-cursor-parse-line :answers (:ok :refused) :bytes 512
 :doc "Parse the connection's command line again (at most 512 octets of its RX, under its owner).")
(defcost fn2-cursor-tx-fill :child fn2-cursor-pool-fill :doc "A pool slot's fill (0 out of range).")
(defcost fn2-cursor-tx-cap :child fn2-pool-slot-capacity :doc "A pool slot's capacity (0 out of range).")
(defcost fn2-cursor-say :child fn2-cursor-render :answers t :bytes 1024 :tables (fn2-core-pool)
 :doc "Render one typed status line (numbers and one span) at the slot's fill.")
(defcost fn2-cursor-put-line :child fn2-cursor-pool-put :answers t :bytes 64 :tables (fn2-core-pool)
 :doc "Append a number and TAB, a number line, CR LF, or the terminator.")
(defcost fn2-cursor-reset :child fn2-pool-reset :answers t :tables (fn2-core-pool)
 :doc "Empty TX (under the connection's owner) before a refusal replaces a status line.")
(defcost fn2-cursor-free-head :child fn2-machines-free-head-of :doc "The cursor partition's free head.")
(defcost fn2-cursor-gen-limit :child fn2-machines-gen-limit :doc "The profile's generation limit.")
(defcost fn2-cursor-reclaim :child fn2-machines-reclaim :tables (fn2-core-machines)
  :effects ((:release (:cursor-row))) :doc "Return a drained cursor row to its partition's free chain.")
(defcost fn2-cursor-mid :child fn2-cursor-mid-span :answers (:ok :refused) :bytes 1024
 :doc "Find an overview line's Message-ID field (at most 1,024 octets read).")

; ---------------------------------------------------------------------------
; The kind. Read row X is the row's slot (one read row per cursor row:
; :capacity is (fn2-b-read-rows profile)).
(defmachine fn2-cursor
 :phases (:free :select :seek :render :send :finish :draining :retired)
 :fields ((conn :link) (conn-gen :u60) (conn-kind :u8) (mask :u8)
          (rx-slot :link) (rx-gen :u60) (line-s :u32) (line-e :u32) (tx-slot :link) (tx-gen :u60)
          (group :u60) (current :u60) (pin :u60)
          (tag :u8) (k0 :u8) (a0 :u32) (b0 :u32) (k1 :u8) (a1 :u32) (b1 :u32)
          (step :u8) (lo :u32) (hi :u32) (next :u32) (found :u32) (count :u32) (low :u32) (high :u32)
          (sel :u60) (ncurrent :u60) (spin :u60) (update :u8) (reply :u16) (roff :u32)
          (lpos :u32) (seen :bool) (have :bool) (turn :bool) (done :bool) (cancel :bool)
          (stopped :bool) (next-free :link))
 :holds ((:select :cursor-row) (:seek :cursor-row) (:render :cursor-row) (:send :cursor-row)
         (:finish :cursor-row) (:draining :cursor-row))
 :budget (:bytes 8192 :steps 32 :descriptors 4)
 :capacity (fn2-b-read-rows profile)
 :taken (:phase :select :rows :cursor-row :ranges ()
         :copy (conn conn-gen conn-kind mask rx-slot rx-gen line-s line-e tx-slot tx-gen group current pin)
         :clear (tag k0 a0 b0 k1 a1 b1 step lo hi next found count low high sel ncurrent spin update reply roff
                 lpos seen have turn done cancel stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (conn *fn2-none*) (rx-slot *fn2-none*) (tx-slot *fn2-none*) (next-free fn2-machine-initial-next-free))
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
   (:do (c1) (fn2-read-key row-slot ':lo 0 row-group) :accept (:ok))
   (:do (c2) (fn2-read-key row-slot ':lo 1 row-lo) :accept (:ok))
   (:do (c3) (fn2-read-key row-slot ':hi 0 row-group) :accept (:ok))
   (:do (c4) (fn2-read-key row-slot ':hi 1 row-hi) :accept (:ok))
   (:do (c5) (fn2-read-range row-slot *fn2-cursor-overview-sid* *fn2-overview-entry-field-position* row-pin)
    :accept (:ok))
   (:set (have 0) (next row-lo))
   (:next :render) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
  ;; OVER/XOVER: the 224 line first (TX is reset if the range is empty)
  (over-head :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :found) row-mask 0 0 0
                               row-tx-slot row-tx-gen 0 0 row-tx-slot row-tx-gen
                               :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
    :accept (:ok))
   (:goto range))
  (seek-name :on-refusal ((:stop :machine-phase))
     (:do (kc) (fn2-read-key-octets row-slot 0 row-rx-slot row-rx-gen row-a0 row-b0
                                    :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (step 1)) (:charge :steps *fn2-work-transition* :runnable t))
  (seek-group :on-refusal ((:stop :machine-phase))
     (:do (lc) (fn2-read-lookup row-slot *fn2-groups-sid* *fn2-cursor-step-budget*)
      :accept ()
      :case (((:ok) (:do (vc g) (fn2-read-value row-slot *fn2-groups-entry-field-group*) :accept (:ok))
                    (:do (fc v) (fn2-read-frontier) :accept (:ok))
                    (:do (rc) (fn2-read-release row-slot) :accept (:ok))
                    (:set (sel g) (spin v) (step 2))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:absent) (:do (rc) (fn2-read-release row-slot) :accept (:ok))
                        (:set (reply (fn2-cursor-reply-of row-tag :no-group))) (:goto refuse))
             (:otherwise (:stop :machine-phase)))))
  (seek-counts-key :on-refusal ((:stop :machine-phase))
     (:do (kc) (fn2-read-key row-slot ':lo 0 row-sel) :accept (:ok))
     (:set (step 3)) (:charge :steps *fn2-work-transition* :runnable t))
  (seek-counts :on-refusal ((:stop :machine-phase))
     (:do (lc) (fn2-read-lookup row-slot *fn2-txn-counts-sid* *fn2-cursor-step-budget*)
      :accept ()
      :case (((:ok) (:do (c1 n) (fn2-read-value row-slot *fn2-group-counts-entry-field-count*) :accept (:ok))
                    (:do (c2 l) (fn2-read-value row-slot *fn2-group-counts-entry-field-low*) :accept (:ok))
                    (:do (c3 h) (fn2-read-value row-slot *fn2-group-counts-entry-field-high*) :accept (:ok))
                    (:do (rc) (fn2-read-release row-slot) :accept (:ok))
                    (:set (count n) (low (if (equal n 0) (+ 1 (nfix h)) l)) (high h) (step 4))
                    (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:absent) (:do (rc) (fn2-read-release row-slot) :accept (:ok))
                        (:set (count 0) (low 1) (high 0) (step 4))
                        (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
  (seek-selected :on-refusal ((:stop :machine-phase))
     (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :selected) row-mask row-count row-low row-high
                                 row-rx-slot row-rx-gen row-a0 row-b0 row-tx-slot row-tx-gen
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
          (fn2-read-identity row-slot row-rx-slot row-rx-gen row-a0 row-b0
                             :okind row-conn-kind :oslot row-conn :ogen row-conn-gen :budget *fn2-cursor-step-budget*)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:found) (:do (rc) (fn2-read-release row-slot) :accept (:ok))
                       (:if (or (equal row-pin 0) (<= (nfix article) row-pin))
                            ((:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :found) row-mask 0 0 0
                                                        row-rx-slot row-rx-gen row-a0 row-b0 row-tx-slot row-tx-gen
                                                        :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                              :accept (:ok))
                             (:set (done 1) (roff 0) (update *fn2-cursor-update-none*)) (:goto hand))
                            ((:set (reply (fn2-cursor-reply-of row-tag :no-msgid))) (:goto refuse))))
             ((:evidence :absent) (:do (rc) (fn2-read-release row-slot) :accept (:ok))
                                  (:set (reply (fn2-cursor-reply-of row-tag :no-msgid))) (:goto refuse))
             (:otherwise (:stop :machine-phase)))))
  ;; the range's end, by what was read (render-step's :end, one sub-arm a branch)
  (end-last :on-refusal ((:stop :machine-phase))
     ;; LAST walked its range: read the last entry again
     (:do (rc) (fn2-read-release row-slot) :accept (:ok))
     (:set (lo row-found) (hi row-found) (step 7)) (:goto range))
  (end-single :on-refusal ((:stop :machine-phase))
     ;; NEXT/LAST: no next or previous article; STAT n: no such number;
     ;; STAT: the current article is gone
     (:do (rc) (fn2-read-release row-slot) :accept (:ok))
     (:set (reply (fn2-cursor-reply-of row-tag (if (or (equal row-k0 *fn2-cursor-arg-range*)
                                                       (not (equal row-tag *fn2-nntp-command-stat*)))
                                                   :none :no-current))))
     (:goto refuse))
  (end-empty :on-refusal ((:stop :machine-phase))
     ;; an empty overview range: the 224 line goes, the refusal replaces it
     (:do (rc) (fn2-read-release row-slot) :accept (:ok))
     (:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (reply (fn2-cursor-reply-of row-tag (if (equal row-k0 *fn2-cursor-arg-range*) :none :no-current))))
     (:goto refuse))
  (end-list :on-refusal ((:stop :machine-phase))
     ;; the rows' terminator
     (:do (rc) (fn2-read-release row-slot) :accept (:ok))
     (:do (code) (fn2-cursor-put-line 3 0 row-tx-slot row-tx-gen
                                      :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:set (done 1)) (:goto hand))
  (render-step :on-refusal ((:stop :machine-phase))
     (:do (nc) (fn2-read-next row-slot *fn2-cursor-step-budget*)
      :accept ()
      :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:entry) (:set (have 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
             ((:end) (:cond ((and (equal row-step 6) (< 0 row-found)) (:goto end-last))
                            ((fn2-cursor-single-p row-tag) (:goto end-single))
                            ((equal row-seen 0) (:goto end-empty))
                            (t (:goto end-list))))
             (:otherwise (:stop :machine-phase)))))
  (render-walk :on-refusal ((:stop :machine-phase))
     (:do (vc n) (fn2-read-value row-slot *fn2-overview-entry-field-number*) :accept (:ok :stale)
      :why ":stale: the walk restarts after the last number it remembered")
     (:if (eq vc :ok) ((:set (found n) (have 0) (next (+ 1 (nfix n)))) (:charge :steps *fn2-work-transition* :runnable t))
          ((:set (lo row-next)) (:goto range))))
  ;; NEXT, LAST, STAT: the 223 line after the copied line [LPOS, ROFF) of TX,
  ;; its Message-ID found there
  (render-say :on-refusal ((:stop :machine-phase))
     (:do (mc ms ml) (fn2-cursor-mid row-tx-slot row-tx-gen row-lpos row-roff
                                     :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok)
      ;; :refused: no Message-ID field in the part of the line TX holds
      :case (((:refused) (:do (rc) (fn2-read-release row-slot) :accept (:ok))
                         (:do (xc) (fn2-cursor-reset row-tx-slot row-tx-gen :okind row-conn-kind :oslot row-conn
                                                     :ogen row-conn-gen)
                          :accept (:ok))
                         (:set (reply (fn2-cursor-reply-of row-tag :no-projection)) (lpos 0)) (:goto refuse))))
     (:do (code) (fn2-cursor-say row-tag (fn2-cursor-reply-of row-tag :found) row-mask row-ncurrent 0 0
                                 row-tx-slot row-tx-gen (nfix ms) (nfix ml) row-tx-slot row-tx-gen
                                 :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
      :accept (:ok))
     (:do (rc) (fn2-read-release row-slot) :accept (:ok))
     (:set (done 1) (lpos 0)
           (update (if (or (equal row-tag *fn2-nntp-command-next*) (equal row-tag *fn2-nntp-command-last*)
                           (equal row-k0 *fn2-cursor-arg-range*))
                       *fn2-cursor-update-current* *fn2-cursor-update-none*)))
     (:goto hand))
  ;; the line copied into TX with room left for the 223 line
  (render-single :on-refusal ((:stop :machine-phase))
     (:let at (nfix (fn2-cursor-tx-fill row-tx-slot)))
     (:do (vc n) (fn2-read-value row-slot *fn2-overview-entry-field-number*) :accept (:ok))
     (:do (oc copied left) (fn2-read-octets row-slot *fn2-overview-entry-field-line* 0
                                            (min 4096 (nfix (- (nfix (fn2-cursor-tx-cap row-tx-slot))
                                                               (+ at *fn2-cursor-single-room*))))
                                            row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:set (ncurrent n) (lpos at) (roff (+ at (nfix copied))))
     (:goto render-say))
  (render-number :on-refusal ((:stop :machine-phase))
     (:do (vc n) (fn2-read-value row-slot *fn2-overview-entry-field-number*) :accept (:ok :stale)
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
     (:do (vc n) (fn2-read-value row-slot *fn2-overview-entry-field-number*) :accept (:ok))
     (:do (oc copied left) (fn2-read-octets row-slot *fn2-overview-entry-field-line* row-lpos (min room 4096)
                                            row-tx-slot row-tx-gen at row-conn-kind row-conn row-conn-gen)
      :accept (:ok))
     (:if (equal left 0)
          ((:do (c2) (fn2-cursor-put-line 2 0 row-tx-slot row-tx-gen
                                          :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
            :accept (:ok))
           (:set (seen 1) (have 0) (lpos 0) (next (+ 1 (nfix n))))
           (:charge :bytes 6144 :steps *fn2-work-transition* :runnable t))
          ((:set (seen 1) (lpos (+ row-lpos (nfix copied))) (roff 0)) (:goto hand))))
  ;; "N TAB line CR LF", the line copied in pieces that fit TX: a piece that
  ;; leaves part of the line breaks the page, and the next page goes on from
  ;; LPOS (a row longer than TX is split, never refused)
  (render-row :on-refusal ((:stop :machine-phase))
     (:do (vc n) (fn2-read-value row-slot *fn2-overview-entry-field-number*) :accept (:ok :stale)
      :why ":stale: the range restarts at the next number")
     (:if (eq vc :ok)
          ((:if (equal row-lpos 0)
                ((:do (c1) (fn2-cursor-put-line 0 (nfix n) row-tx-slot row-tx-gen
                                                :okind row-conn-kind :oslot row-conn :ogen row-conn-gen)
                  :accept (:ok))
                 (:goto render-piece))
                ((:goto render-piece))))
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
    ;; GROUP g / LISTGROUP g: the name in the group directory
    ((and (fn2-cursor-selects-p row-tag) (equal row-k0 *fn2-cursor-arg-span*) (equal row-step 0)) (:goto seek-name))
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 1)) (:goto seek-group))
    ;; the group's counts: count, low, high (an empty group 0, high + 1, high)
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 2)) (:goto seek-counts-key))
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 3)) (:goto seek-counts))
    ;; the 211 line; GROUP is done, LISTGROUP lists the numbers in its range
    ((and (fn2-cursor-selects-p row-tag) (equal row-step 4)) (:goto seek-selected))
    ;; LISTGROUP with no name lists the current group: its name is not read
    ;; back yet (the group directory is keyed by name), so 503 until 1/n-b
    ((fn2-cursor-selects-p row-tag)
     (:set (reply (fn2-cursor-reply-of row-tag (if (equal row-group 0) :no-group-selected :no-projection))))
     (:goto refuse))
    ;; STAT <id>: the identity read; OVER <id> waits on the article's overview
    ;; address (D5 2/n): 503
    ((and (equal row-tag *fn2-nntp-command-stat*) (equal row-k0 *fn2-cursor-arg-span*)) (:goto seek-identity))
    ((and (equal row-tag *fn2-nntp-command-over*) (equal row-k0 *fn2-cursor-arg-span*))
     (:set (reply (fn2-cursor-reply-of row-tag :no-projection))) (:goto refuse))
    ;; every other command reads the selected group
    ((equal row-group 0) (:set (reply (fn2-cursor-reply-of row-tag :no-group-selected))) (:goto refuse))
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
    ((equal row-have 0) (:goto render-step))
    ;; LAST's walk: remember the number, step on
    ((equal row-step 6) (:goto render-walk))
    ;; NEXT, LAST, STAT: the line, its Message-ID found, then the 223 line after it
    ((fn2-cursor-single-p row-tag) (:goto render-single))
    ;; a page break: TX has no room for another row
    ((and (< 0 (nfix (fn2-cursor-tx-fill row-tx-slot)))
          (< (nfix (fn2-cursor-tx-cap row-tx-slot)) (+ (nfix (fn2-cursor-tx-fill row-tx-slot)) *fn2-cursor-row-room*)))
     (:set (roff 0)) (:goto hand))
    ;; LISTGROUP: the number
    ((equal row-tag *fn2-nntp-command-listgroup*) (:goto render-number))
    ;; OVER/XOVER: a row, "N TAB line" (the 224 line is written before the range)
    (t (:goto render-row))))
  ;; TX is the connection's until it sets TURN again
  (:send
   (:cond ((equal row-cancel 1) (:next :finish) (:charge :steps *fn2-work-transition* :runnable t))
          ((equal row-turn 0) (:charge :steps *fn2-work-empty*))
          ((equal row-done 1) (:next :finish) (:charge :steps *fn2-work-transition* :runnable t))
          (t (:next :render) (:charge :steps *fn2-work-transition* :runnable t))))
  (:finish :on-refusal ((:stop :machine-phase))
   (:do (rc) (fn2-read-release row-slot) :accept (:ok))
   (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
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
 :observes ())
(defmachine-arms fn2-cursor :children)

; MACHINE-FORM 6.5 P4: the take in child form, proved here; the admission
; section makes its core face (the connection's :query takes a cursor).
(defmachine-registry fn2-cursor)
