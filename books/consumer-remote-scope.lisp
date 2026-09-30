; Bounded current READ/moderation projection and remote definition producer.
; The owner borrows its already installed fn-own-config, never reconstructs
; fn-oag-post-config or validates the whole configuration on a request.
(in-package "ACL2")
(include-book "consumer-remote-ingress")
(include-book "consumer-remote-fields")
(include-book "consumer-account-carried")
(include-book "group-access")
(include-book "moderation")

; The maintained owner lineage supplies this key in the same span as current
; account authentication and installed configuration capture. No pointer hash
; or entire-root comparison is used. Absence is not an authority namespace.
(defun fn-crs-key (ingress configured-generation)
 (declare (xargs :guard t))
 (list :remote-source (fn-cp-nth 6 ingress) (fn-cp-nth 4 ingress)
       (fn-cp-nth 5 ingress) (fn-cp-nth 3 ingress) configured-generation))

; A fixed18 spine. ROOT/CLOSED/SERVED are literal borrowed children from the
; captured installed config; the owner owes their lifetime across all yields.
; key,login,phase,access,read,groups,servedRoot,closedRoot,scan,moderators,
; previous,count,reversed,reversedMeta,built,builtMeta,queryWireOctets.
(defun fn-crs-state (key login phase access read groups served closed scan mods prev n rev rm built bm wire)
 (declare (xargs :guard t))
 (list :remote-scope key login phase access read groups served closed scan mods prev n rev rm built bm wire))

(defun fn-crs-begin (ingress configured-generation installed-config groups)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 0 ingress) :authenticated)) ingress
  (list :yield
   (fn-crs-state (fn-crs-key ingress configured-generation)
    (fn-cp-nth 2 (fn-cp-nth 1 ingress)) :access
    (fn-gac-listing-table (fn-inj-config-listing installed-config)) nil groups
    (fn-inj-config-groups installed-config) (fn-inj-config-closed installed-config)
    nil nil nil 0 nil nil nil nil 0))))

(defun fn-crs-wire (s)
 (declare (xargs :guard t))
 (nfix (fn-cp-nth 17 s)))
(in-theory (disable fn-crs-wire))

; Exactly one row, group, or moderator-name cell is inspected per tick;
; exactly one list cell is rebuilt per :reverse tick. Pattern/name comparisons
; are bounded by the maintained config/request field widths, not table size.
; Current-key must be recomputed after current named-account authentication.
(defun fn-crs-tick (s current-key g)
 (declare (xargs :guard t))
 (let* ((key (fn-cp-nth 1 s)) (login (fn-cp-nth 2 s)) (phase (fn-cp-nth 3 s))
        (access (fn-cp-nth 4 s)) (read (fn-cp-nth 5 s)) (groups (fn-cp-nth 6 s))
        (served (fn-cp-nth 7 s)) (closed (fn-cp-nth 8 s)) (scan (fn-cp-nth 9 s))
        (mods (fn-cp-nth 10 s)) (prev (fn-cp-nth 11 s)) (n (nfix (fn-cp-nth 12 s)))
        (rev (fn-cp-nth 13 s)) (rm (fn-cp-nth 14 s))
        (built (fn-cp-nth 15 s)) (bm (fn-cp-nth 16 s))
        (wire (fn-crs-wire s)))
  (cond
   ((not (equal key current-key)) '(:refused :scope-changed))
   ((eq phase :ready) (list :ready s))
   ((eq phase :access)
    (if (not (consp access))
        (list :yield (fn-crs-state key login :groups nil nil groups served closed nil nil prev n rev rm nil nil wire))
     (let ((row (car access)))
      (if (and (equal (fn-cp-nth 3 row) 3)
               (equal (fn-gac-text-octets (fn-cp-nth 0 row)) login))
          (let ((text (fn-cp-nth 1 row)))
           (list :yield (fn-crs-state key login :groups nil
             (if (equal text "*") nil (if (stringp text) text ""))
             groups served closed nil nil prev n rev rm nil nil wire)))
        (list :yield (fn-crs-state key login :access (cdr access) nil
                       groups served closed nil nil prev n rev rm nil nil wire))))))
   ((eq phase :groups)
    (cond ((not (consp groups))
           (if (and (null groups) (posp n))
               (list :yield (fn-crs-state key login :reverse nil read nil served closed nil nil prev n rev rm nil nil wire))
             '(:refused :query)))
          ((or (<= (nfix g) n) (not (fn-crs-namep (fn-cp-nth 0 groups)))
               (and prev (or (not (lexorder prev (fn-cp-nth 0 groups))) (equal prev (fn-cp-nth 0 groups)))))
           '(:refused :query))
          ((and read (not (fn-gac-readablep read (coerce (fn-nntp-octets-chars (fn-cp-nth 0 groups)) 'string))))
           '(:refused :read-scope))
          (t (list :yield (fn-crs-state key login :served nil read groups served closed served nil prev n rev rm nil nil wire)))))
   ((eq phase :served)
    (cond ((not (consp scan)) '(:refused :read-scope))
          ((equal (car scan) (fn-cp-nth 0 groups))
           (list :yield (fn-crs-state key login :closed nil read groups served closed closed nil prev n rev rm nil nil wire)))
          (t (list :yield (fn-crs-state key login :served nil read groups served closed (cdr scan) nil prev n rev rm nil nil wire)))))
   ((eq phase :closed)
    (if (not (consp scan))
        (list :yield (fn-crs-state key login :accept nil read groups served closed nil nil prev n rev rm nil nil wire))
      (let ((entry (car scan)))
       (if (and (consp entry) (fn-nntp-moderated-entryp entry) (eq (car entry) :moderated)
                (equal (fn-mod-entry-queue entry) (fn-cp-nth 0 groups)))
           (list :yield (fn-crs-state key login :moderators nil read groups served closed
                          (cdr scan) (fn-mod-entry-moderators entry) prev n rev rm nil nil wire))
         (list :yield (fn-crs-state key login :closed nil read groups served closed
                        (cdr scan) nil prev n rev rm nil nil wire))))))
   ((eq phase :moderators)
    (cond ((not (consp mods)) '(:refused :read-scope))
          ((equal (car mods) login)
           (list :yield (fn-crs-state key login :closed nil read groups served closed scan nil prev n rev rm nil nil wire)))
          (t (list :yield (fn-crs-state key login :moderators nil read groups served closed scan (cdr mods) prev n rev rm nil nil wire)))))
   ((eq phase :accept)
    (let ((name (fn-cp-nth 0 groups)))
     (list :yield (fn-crs-state key login :groups nil read (fn-inj-cdr groups) served closed nil nil name
       (1+ n) (cons name rev) (fn-caac-list-cons (fn-scs-octets (len name)) rm) nil nil (+ wire 2 (len name))))))
   ((eq phase :reverse)
    (if (not (consp rev))
        (list :ready (fn-crs-state key login :ready nil read nil served closed nil nil prev n nil nil built bm wire))
      (list :yield (fn-crs-state key login :reverse nil read nil served closed nil nil prev n
         (cdr rev) (fn-cp-nth 2 rm) (cons (car rev) built)
         (fn-caac-list-cons (fn-cp-nth 1 rm) bm) wire))))
   (t '(:refused :scope-phase)))))

; No table/query walk here. The producer carries its exact definition child
; and canonical-size annotation into the eventual durable CPE constructor.
(defun fn-crs-finish (s current-key)
 (declare (xargs :guard t))
 (cond ((not (equal (fn-cp-nth 1 s) current-key)) '(:refused :scope-changed))
       ((not (eq (fn-cp-nth 3 s) :ready)) '(:refused :scope-incomplete))
       (t (list :definition (fn-cp-nth 15 s) (fn-cp-nth 16 s) (fn-cp-nth 12 s) current-key (fn-cp-nth 17 s)))))

(in-theory (disable fn-crs-key fn-crs-state fn-crs-begin fn-crs-namep fn-crs-tick fn-crs-finish))
