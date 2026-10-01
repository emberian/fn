; fn: the store's records as an abstract stobj over the history image (lane
; arena-store-6, 2026-09-28; history-columns' stage 3; coordinator decision:
; the owner's records become the logical value of an abstract stobj whose
; executable is the history image on the page store).  Prefix fn-hrs-.
;
; `fn-hrecs' holds a history H.  Its executable (`fn-hrecs$c') is the
; FNADTSN2 image of H's first N events on a NESTED page store
; (books/history-pages*.lisp: `fn-hp-x-at' reads a row, `fn-hp-x-append-step'
; appends one) and, after them, a SUFFIX array of the events appended since
; the image's last append.  H itself is a GHOST: the abstract value is
; (H . C), the logic carries H, the executable never builds it.  The
; correspondence is C itself; each export runs the concrete operation on C
; and says what it does to H (append adds EV, load sets EVENTS, the rest
; keep H).  What the exports MEAN is `fn-hrecs-faithful' (C holds H: H is
; the image's events then the suffix's, and every VERIFIED page of the
; nested store holds H's placed image), which every export keeps.
;
; Reads return need-verdicts (coordinator decision 2026-09-28, (6)): the
; exports are pure; a row whose page is not verified answers
; (:need-page P PHYS).  The ONE retry loop is `fn-hrecs-get' /
; `fn-hrecs-read': serve each need by one fill (`fn-hrecs-serve': the
; host's byte primitive `fn-pgs-fill-realize' at the address the table
; names for P, then the page store's digest check) and ask again.  A-PGS-
; HOST-IO (books/assumptions.lisp) enters there and nowhere else, with the
; relation `fn-hrecs-disk-faithful' (the page file holds the image's page
; for every page not yet verified) that the open establishes.
;
; KEYSTONES (each over the function the host calls)
;   fn-hrecs-at-is-nth       an :ok read is record SEQ of H (or (:refused
;                            :seq) past its end); any other verdict is a
;                            need-verdict for a record H has
;   fn-hrecs-read-is-nth     the read with its retry loop: keeps H, its
;                            faithfulness and the page file's relation; :ok
;                            answers record SEQ; never stops for fuel
;   fn-hrecs-get-fuel-enough each fill the loop makes verifies an open page
;   fn-hrecs-serve-keeps     one fill keeps all three (A-PGS-HOST-IO)
;   fn-hrecs-fill-keeps      a fill that writes the image's page keeps H
;                            faithful, whatever it answers
;   fn-hrecs-flush-keeps     moving the oldest suffix event into the image
;                            keeps H faithful, whatever it answers
;   fn-hrecs-append-appends, fn-hrecs-load-is-events, fn-hrecs-count-is-len
;
; Not here (milestone (c) of the lane): the open's adopt of a committed
; image (the ghost from the page file), the flush's retry loop over pages
; not yet verified (needs: the step changes the image only on pages it
; made ready), the commit.  Milestone (b): the Message-ID lookup and the
; relation to the store's `fn-sf-records'.
(in-package "ACL2")
(include-book "history-pages-import")
(include-book "history-pages-view")
(include-book "assumptions")
(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; A. The concrete: the image on a nested page store, its header, and the
; suffix of events appended since the image's last append.

(defstobj fn-hrecs$c
  (fn-hrc-pgs :type pgs-mem)
  (fn-hrc-oct :type fn-octets-pg)
  (fn-hrc-img :type (integer 0 1) :initially 0)
  (fn-hrc-salt :type (integer 0 *) :initially 0)
  (fn-hrc-nimg :type (integer 0 *) :initially 0)
  (fn-hrc-lens :type t :initially (0 0 0 0 0))
  (fn-hrc-starts :type t :initially (1 1 1 1 1))
  (fn-hrc-npages :type (integer 0 *) :initially 0)
  (fn-hrc-txid :type (integer 0 *) :initially 0)
  (fn-hrc-sfx :type (array t (0)) :initially nil :resizable t)
  (fn-hrc-lo :type (integer 0 *) :initially 0)
  (fn-hrc-hi :type (integer 0 *) :initially 0)
  :inline t)

(defun fn-hrc-wfp (fn-hrecs$c)
  ; the shape every export keeps: the suffix window inside its array, the
  ; header's lists of five naturals, no image rows without an image
  (declare (xargs :stobjs fn-hrecs$c))
  (and (<= (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c))
       (<= (fn-hrc-hi fn-hrecs$c) (fn-hrc-sfx-length fn-hrecs$c))
       (nat-listp (fn-hrc-lens fn-hrecs$c)) (equal (len (fn-hrc-lens fn-hrecs$c)) 5)
       (nat-listp (fn-hrc-starts fn-hrecs$c)) (equal (len (fn-hrc-starts fn-hrecs$c)) 5)
       (natp (fn-hrc-nimg fn-hrecs$c)) (natp (fn-hrc-lo fn-hrecs$c)) (natp (fn-hrc-hi fn-hrecs$c))
       (natp (fn-hrc-npages fn-hrecs$c)) (natp (fn-hrc-salt fn-hrecs$c)) (natp (fn-hrc-txid fn-hrecs$c))
       (or (equal (fn-hrc-img fn-hrecs$c) 0) (equal (fn-hrc-img fn-hrecs$c) 1))
       (implies (equal (fn-hrc-img fn-hrecs$c) 0) (equal (fn-hrc-nimg fn-hrecs$c) 0))))

; The suffix window [LO, HI) as a list, oldest first.
(defun fn-hrc-sfx-list (i hi fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (natp i) (natp hi) (<= hi (fn-hrc-sfx-length fn-hrecs$c)))
                  :measure (nfix (- (nfix hi) (nfix i)))))
  (if (mbe :logic (zp (- (nfix hi) (nfix i))) :exec (<= hi i))
      nil
    (cons (fn-hrc-sfxi i fn-hrecs$c) (fn-hrc-sfx-list (+ 1 (nfix i)) hi fn-hrecs$c))))

; The concrete's primitives closed from here on: reads over writes.

(deftheory fn-hrc-fields
  '(fn-hrc-img fn-hrc-salt fn-hrc-nimg fn-hrc-lens fn-hrc-starts fn-hrc-npages fn-hrc-txid
    fn-hrc-sfxi fn-hrc-sfx-length fn-hrc-lo fn-hrc-hi fn-hrc-sfx-list fn-hrc-pgs fn-hrc-oct))

; Reads over writes, so the stobj's primitives stay closed below.
(deftheory fn-hrc-updaters
  '(update-fn-hrc-img update-fn-hrc-salt update-fn-hrc-nimg update-fn-hrc-lens update-fn-hrc-starts
    update-fn-hrc-npages update-fn-hrc-txid update-fn-hrc-lo update-fn-hrc-hi update-fn-hrc-sfxi
    resize-fn-hrc-sfx update-fn-hrc-pgs update-fn-hrc-oct))

(defthm fn-hrc-row-img
  (and (equal (fn-hrc-img  (update-fn-hrc-img v c)) v)
       (equal (fn-hrc-salt  (update-fn-hrc-img v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-img v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-img v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-img v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-img v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-img v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-img v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-img v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-img v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-img v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-img v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-img v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-salt
  (and (equal (fn-hrc-img  (update-fn-hrc-salt v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-salt v c)) v)
       (equal (fn-hrc-nimg  (update-fn-hrc-salt v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-salt v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-salt v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-salt v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-salt v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-salt v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-salt v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-salt v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-salt v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-salt v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-salt v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-nimg
  (and (equal (fn-hrc-img  (update-fn-hrc-nimg v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-nimg v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-nimg v c)) v)
       (equal (fn-hrc-lens  (update-fn-hrc-nimg v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-nimg v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-nimg v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-nimg v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-nimg v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-nimg v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-nimg v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-nimg v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-nimg v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-nimg v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-lens
  (and (equal (fn-hrc-img  (update-fn-hrc-lens v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-lens v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-lens v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-lens v c)) v)
       (equal (fn-hrc-starts  (update-fn-hrc-lens v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-lens v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-lens v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-lens v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-lens v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-lens v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-lens v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-lens v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-lens v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-starts
  (and (equal (fn-hrc-img  (update-fn-hrc-starts v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-starts v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-starts v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-starts v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-starts v c)) v)
       (equal (fn-hrc-npages  (update-fn-hrc-starts v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-starts v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-starts v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-starts v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-starts v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-starts v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-starts v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-starts v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-npages
  (and (equal (fn-hrc-img  (update-fn-hrc-npages v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-npages v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-npages v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-npages v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-npages v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-npages v c)) v)
       (equal (fn-hrc-txid  (update-fn-hrc-npages v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-npages v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-npages v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-npages v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-npages v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-npages v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-npages v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-txid
  (and (equal (fn-hrc-img  (update-fn-hrc-txid v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-txid v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-txid v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-txid v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-txid v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-txid v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-txid v c)) v)
       (equal (fn-hrc-lo  (update-fn-hrc-txid v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-txid v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-txid v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-txid v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-txid v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-txid v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-lo
  (and (equal (fn-hrc-img  (update-fn-hrc-lo v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-lo v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-lo v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-lo v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-lo v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-lo v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-lo v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-lo v c)) v)
       (equal (fn-hrc-hi  (update-fn-hrc-lo v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-lo v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-lo v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-lo v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-lo v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-hi
  (and (equal (fn-hrc-img  (update-fn-hrc-hi v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-hi v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-hi v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-hi v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-hi v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-hi v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-hi v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-hi v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-hi v c)) v)
       (equal (fn-hrc-sfxi i  (update-fn-hrc-hi v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-hi v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-hi v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-hi v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-pgs
  (and (equal (fn-hrc-img  (update-fn-hrc-pgs v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-pgs v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-pgs v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-pgs v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-pgs v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-pgs v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-pgs v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-pgs v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-pgs v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-pgs v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-pgs v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-pgs v c)) v)
       (equal (fn-hrc-oct  (update-fn-hrc-pgs v c)) (fn-hrc-oct c)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-oct
  (and (equal (fn-hrc-img  (update-fn-hrc-oct v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-oct v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-oct v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-oct v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-oct v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-oct v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-oct v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-oct v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-oct v c)) (fn-hrc-hi c))
       (equal (fn-hrc-sfxi i  (update-fn-hrc-oct v c)) (fn-hrc-sfxi i c))
       (equal (fn-hrc-sfx-length  (update-fn-hrc-oct v c)) (fn-hrc-sfx-length c))
       (equal (fn-hrc-pgs  (update-fn-hrc-oct v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-oct v c)) v))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-sfxi
  (and (equal (fn-hrc-img  (update-fn-hrc-sfxi j v c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (update-fn-hrc-sfxi j v c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (update-fn-hrc-sfxi j v c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (update-fn-hrc-sfxi j v c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (update-fn-hrc-sfxi j v c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (update-fn-hrc-sfxi j v c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (update-fn-hrc-sfxi j v c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (update-fn-hrc-sfxi j v c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (update-fn-hrc-sfxi j v c)) (fn-hrc-hi c))
       (equal (fn-hrc-pgs  (update-fn-hrc-sfxi j v c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (update-fn-hrc-sfxi j v c)) (fn-hrc-oct c))
       (equal (fn-hrc-sfxi i (update-fn-hrc-sfxi j v c)) (if (equal (nfix i) (nfix j)) v (fn-hrc-sfxi i c)))
       (implies (< (nfix j) (fn-hrc-sfx-length c)) (equal (fn-hrc-sfx-length (update-fn-hrc-sfxi j v c)) (fn-hrc-sfx-length c))))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrc-row-resize
  (and (equal (fn-hrc-img  (resize-fn-hrc-sfx n c)) (fn-hrc-img c))
       (equal (fn-hrc-salt  (resize-fn-hrc-sfx n c)) (fn-hrc-salt c))
       (equal (fn-hrc-nimg  (resize-fn-hrc-sfx n c)) (fn-hrc-nimg c))
       (equal (fn-hrc-lens  (resize-fn-hrc-sfx n c)) (fn-hrc-lens c))
       (equal (fn-hrc-starts  (resize-fn-hrc-sfx n c)) (fn-hrc-starts c))
       (equal (fn-hrc-npages  (resize-fn-hrc-sfx n c)) (fn-hrc-npages c))
       (equal (fn-hrc-txid  (resize-fn-hrc-sfx n c)) (fn-hrc-txid c))
       (equal (fn-hrc-lo  (resize-fn-hrc-sfx n c)) (fn-hrc-lo c))
       (equal (fn-hrc-hi  (resize-fn-hrc-sfx n c)) (fn-hrc-hi c))
       (equal (fn-hrc-pgs  (resize-fn-hrc-sfx n c)) (fn-hrc-pgs c))
       (equal (fn-hrc-oct  (resize-fn-hrc-sfx n c)) (fn-hrc-oct c))
       (equal (fn-hrc-sfx-length (resize-fn-hrc-sfx n c)) (nfix n)))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(in-theory (disable fn-hrc-fields fn-hrc-updaters))

; -----------------------------------------------------------------------------
; B. The operations over the concrete.

(defun fn-hrc-count (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)))
  (+ (fn-hrc-nimg fn-hrecs$c) (- (fn-hrc-hi fn-hrecs$c) (fn-hrc-lo fn-hrecs$c))))

(defun fn-hrc-at (seq fn-hrecs$c)
  ; Record SEQ: (mv VERDICT RESULT).  Below the image's count, the image's
  ; row (`fn-hp-x-at': a need-verdict when a page it touches is not
  ; verified); else the suffix's element, or (:refused :seq) past the end.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp seq) (fn-hrc-wfp fn-hrecs$c))))
  (let ((n (fn-hrc-nimg fn-hrecs$c)))
    (if (< seq n)
        (let ((salt (fn-hrc-salt fn-hrecs$c))
              (lens (fn-hrc-lens fn-hrecs$c))
              (starts (fn-hrc-starts fn-hrecs$c)))
          (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                     (v r)
                     (fn-hp-x-at seq salt n lens starts pgs-mem)
                     (mv v r)))
      (let ((j (+ (fn-hrc-lo fn-hrecs$c) (- seq n))))
        (if (< j (fn-hrc-hi fn-hrecs$c))
            (mv :ok (list :ok (fn-hrc-sfxi j fn-hrecs$c)))
          (mv :ok (list :refused :seq)))))))

(defun fn-hrc-vlen (fn-hrecs$c)
  ; the nested page store's page count
  (declare (xargs :stobjs fn-hrecs$c))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))) (n) (pgs-v-length pgs-mem) n))

(defun fn-hrc-phys (p fn-hrecs$c)
  ; the physical address the table names for page P (what a fill reads)
  (declare (xargs :stobjs fn-hrecs$c :guard (natp p)))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))) (a) (first (pgs-x-get-entry 2 0 p pgs-mem)) a))

(defun fn-hrc-append (ev fn-hrecs$c)
  ; EV onto the suffix: O(1) amortized (the array doubles when full)
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory (disable fn-hrecs$cp)))))
  (let* ((hi (fn-hrc-hi fn-hrecs$c))
         (cap (fn-hrc-sfx-length fn-hrecs$c))
         (fn-hrecs$c (if (< hi cap) fn-hrecs$c
                       (resize-fn-hrc-sfx (max 16 (* 2 cap)) fn-hrecs$c)))
         (fn-hrecs$c (update-fn-hrc-sfxi hi ev fn-hrecs$c)))
    (update-fn-hrc-hi (+ 1 hi) fn-hrecs$c)))

(defthm fn-hrc-append-wfp0
  (implies (fn-hrc-wfp fn-hrecs$c) (fn-hrc-wfp (fn-hrc-append ev fn-hrecs$c))))

(defun fn-hrs-put (j ws pgs-mem)
  ; words J .. J+|WS|-1 := WS (a fill: no page is marked dirty)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp j) (fn-hp-u64-listp ws) (<= (+ j (len ws)) (pgs-w-length pgs-mem)))))
  (if (atom ws)
      pgs-mem
    (let ((pgs-mem (update-pgs-wi j (car ws) pgs-mem)))
      (fn-hrs-put (+ 1 j) (cdr ws) pgs-mem))))

(defun fn-hrs-fill-pgs (p words txid pgs-mem fn-octets-pg)
  ; The fill of image page P with WORDS, then its check against its table
  ; entry (`pgs-x-open-page' :eager): (mv VERDICT pgs-mem fn-octets-pg).
  ; :ok (P verified), a verified page untouched (:ok), or the page store's
  ; refusal ((:page-damaged P PHYS), (:need-table T), ...), or
  ; (:refused :fill-range) / (:refused :fill-words).  A page that does not
  ; verify keeps what was written and stays unverified.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :guard (and (natp p) (natp txid))))
  (cond ((not (and (< p (pgs-v-length pgs-mem)) (<= (* 2048 (+ 1 p)) (pgs-w-length pgs-mem))))
         (mv (list :refused :fill-range) pgs-mem fn-octets-pg))
        ((equal (pgs-vi p pgs-mem) 2) (mv :ok pgs-mem fn-octets-pg))
        ((not (and (fn-hp-u64-listp words) (equal (len words) 2048)))
         (mv (list :refused :fill-words) pgs-mem fn-octets-pg))
        (t (let ((pgs-mem (fn-hrs-put (* 2048 p) words pgs-mem)))
             (mv-let (v pgs-mem fn-octets-pg)
               (pgs-x-open-page p txid :eager pgs-mem fn-octets-pg)
               (mv (if v v :ok) pgs-mem fn-octets-pg))))))

(defun fn-hrc-fill (p words fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp p) (fn-hrc-wfp fn-hrecs$c))))
  (let ((txid (fn-hrc-txid fn-hrecs$c)))
    (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))
                (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
               (v pgs-mem fn-octets-pg)
               (fn-hrs-fill-pgs p words txid pgs-mem fn-octets-pg)
               (mv v fn-hrecs$c))))

; -----------------------------------------------------------------------------
; The frame fill (lane page-word-boundary, 2026-10-01; design stage 2): the
; same fill with the page's words put IN PLACE by the host (A-PGS-HOST-IO's
; frame form `fn-pgs-fill-frame', books/assumptions-pgs-host-io.lisp)
; instead of crossing the boundary as a list of 2048 words.  Each is `mbe':
; its :logic is the list form at the realizer's words, so it IS that term
; in the logic and every theorem over the list form is a theorem over it;
; its :exec is the in-place path; the guard proof is the bridge (the
; :fill-words refusal is unreachable there: the page's words are u64 words,
; fn-pgs-page-words-u64).  The list form stays for the theorems and the
; tests that take words as data.

; (the two bridges are used by name, never as rewrite rules: the proofs
; above and below reason about fn-hrs-put and fn-hp-u64-listp as they are)
(defthm fn-hp-u64-listp-is-fn-pgs-u64-listp
  (equal (fn-hp-u64-listp ws) (fn-pgs-u64-listp ws))
  :rule-classes nil)

(defthm fn-hrs-put-is-frame-put
  (equal (fn-hrs-put j ws pgs-mem) (fn-pgs-frame-put 0 j ws pgs-mem))
  :hints (("Goal" :induct (fn-hrs-put j ws pgs-mem) :in-theory (enable fn-pgs-frame-put)))
  :rule-classes nil)

(defun fn-hrs-frame-fill-pgs (file addr p txid pgs-mem fn-octets-pg)
  ; `fn-hrs-fill-pgs' at the realizer's words, the words put in place.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :guard (and (natp p) (natp txid))
                  :guard-hints (("Goal" :in-theory (e/d (fn-pgs-frame-len)
                                                        (pgs-x-open-page fn-hrs-put fn-pgs-frame-put
                                                         pgs-vi pgs-v-length pgs-w-length))
                                 :use ((:instance fn-pgs-page-words-shape)
                                       (:instance fn-pgs-page-words-u64)
                                       (:instance fn-hp-u64-listp-is-fn-pgs-u64-listp (ws (fn-pgs-page-words file addr)))
                                       (:instance fn-hrs-put-is-frame-put (j (* 2048 p)) (ws (fn-pgs-page-words file addr))))))))
  (mbe :logic (fn-hrs-fill-pgs p (fn-pgs-fill-realize file addr) txid pgs-mem fn-octets-pg)
       :exec (cond ((not (and (< p (pgs-v-length pgs-mem)) (<= (* 2048 (+ 1 p)) (pgs-w-length pgs-mem))))
                    (mv (list :refused :fill-range) pgs-mem fn-octets-pg))
                   ((equal (pgs-vi p pgs-mem) 2) (mv :ok pgs-mem fn-octets-pg))
                   (t (let ((pgs-mem (fn-pgs-fill-frame file addr 0 (* 2048 p) pgs-mem)))
                        (mv-let (v pgs-mem fn-octets-pg)
                          (pgs-x-open-page p txid :eager pgs-mem fn-octets-pg)
                          (mv (if v v :ok) pgs-mem fn-octets-pg)))))))

(defun fn-hrc-frame-fill (file addr p fn-hrecs$c)
  ; `fn-hrc-fill' at the realizer's words, the words put in place.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp p) (fn-hrc-wfp fn-hrecs$c))
                  :guard-hints (("Goal" :in-theory (e/d (fn-hrc-fill fn-hrs-frame-fill-pgs)
                                                        (fn-hrs-fill-pgs))))))
  (mbe :logic (fn-hrc-fill p (fn-pgs-fill-realize file addr) fn-hrecs$c)
       :exec (let ((txid (fn-hrc-txid fn-hrecs$c)))
               (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))
                           (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
                          (v pgs-mem fn-octets-pg)
                          (fn-hrs-frame-fill-pgs file addr p txid pgs-mem fn-octets-pg)
                          (mv v fn-hrecs$c)))))

(defun fn-hrs-pgs-empty (pgs-mem)
  (declare (xargs :stobjs pgs-mem))
  (let* ((pgs-mem (resize-pgs-w 0 pgs-mem)) (pgs-mem (resize-pgs-m 0 pgs-mem))
         (pgs-mem (resize-pgs-t 0 pgs-mem)) (pgs-mem (resize-pgs-d 0 pgs-mem))
         (pgs-mem (resize-pgs-v 0 pgs-mem)))
    (resize-pgs-tv 0 pgs-mem)))

(defun fn-hrc-load-events (events fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (and (true-listp events) (fn-hrc-wfp fn-hrecs$c))
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-append fn-hrc-wfp)))))
  (if (atom events)
      fn-hrecs$c
    (let ((fn-hrecs$c (fn-hrc-append (car events) fn-hrecs$c)))
      (fn-hrc-load-events (cdr events) fn-hrecs$c))))

(defun fn-hrc-reset (salt fn-hrecs$c)
  ; the empty history, no image (the nested page store emptied)
  (declare (xargs :stobjs fn-hrecs$c :guard (natp salt)))
  (let* ((fn-hrecs$c (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                                (pgs-mem)
                                (fn-hrs-pgs-empty pgs-mem)
                                fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-img 0 fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-nimg 0 fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-salt salt fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-lens (list 0 0 0 0 0) fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-starts (list 1 1 1 1 1) fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-npages 0 fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-txid 0 fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-lo 0 fn-hrecs$c)))
    (update-fn-hrc-hi 0 fn-hrecs$c)))

(defthm fn-hrc-reset-wfp
  (implies (natp salt) (fn-hrc-wfp (fn-hrc-reset salt fn-hrecs$c))))

(defun fn-hrc-load (events salt fn-hrecs$c)
  ; The history EVENTS, all in the suffix, no image (the first flush makes
  ; the image).  Work O(|EVENTS|).
  (declare (xargs :stobjs fn-hrecs$c :guard (and (true-listp events) (natp salt))
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-reset fn-hrc-wfp)))))
  (let ((fn-hrecs$c (fn-hrc-reset salt fn-hrecs$c)))
    (fn-hrc-load-events events fn-hrecs$c)))

(defun fn-hrc-adopt (salt n lens starts np txid fn-hrecs$c)
  ; The image the nested page store holds: its header answer (N LENS
  ; STARTS NP, `fn-hp-x-header'), SALT, and the record's TXID; the suffix
  ; empty.  O(1): no page is read.
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (natp salt) (natp n) (nat-listp lens) (equal (len lens) 5)
                              (nat-listp starts) (equal (len starts) 5) (natp np) (natp txid)
                              (fn-hrc-wfp fn-hrecs$c))))
  (let* ((fn-hrecs$c (update-fn-hrc-img 1 fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-salt salt fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-nimg n fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-lens lens fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-starts starts fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-npages np fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-txid txid fn-hrecs$c))
         (fn-hrecs$c (update-fn-hrc-lo 0 fn-hrecs$c)))
    (update-fn-hrc-hi 0 fn-hrecs$c)))

(defthm fn-hrs-append-step-types
  (implies (and (natp n) (nat-listp lens) (equal (len lens) 5) (nat-listp starts) (equal (len starts) 5) (natp np))
           (let ((a (fn-hp-x-append-step ev salt n lens starts np pgs-mem)))
             (and (natp (mv-nth 1 a)) (integerp (mv-nth 1 a)) (<= 0 (mv-nth 1 a))
                  (nat-listp (mv-nth 2 a)) (equal (len (mv-nth 2 a)) 5)
                  (nat-listp (mv-nth 3 a)) (equal (len (mv-nth 3 a)) 5)
                  (natp (mv-nth 4 a)) (integerp (mv-nth 4 a)) (<= 0 (mv-nth 4 a)))))
  :hints (("Goal" :use ((:instance fn-hp-x-append-loop-types (k 5)))
           :in-theory (disable fn-hp-x-append-loop-types fn-hp-x-append-loop))))

(defthm fn-hrs-x-init-types
  (let ((a (fn-hp-x-init pgs-mem)))
    (implies (equal (mv-nth 0 a) :ok)
             (and (equal (mv-nth 1 a) 0) (equal (mv-nth 2 a) '(0 0 0 0 0))
                  (equal (mv-nth 3 a) '(1 1 1 1 1)) (equal (mv-nth 4 a) 1))))
  :hints (("Goal" :in-theory (disable pgs-x-grow-image fn-hp-x-put))))

(defun fn-hrc-flush-init (fn-hrecs$c)
  ; the empty history's image on the (empty) nested page store
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory (disable fn-hp-x-init fn-hrecs$cp pgs-memp)))))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (v n lens starts np pgs-mem)
             (fn-hp-x-init pgs-mem)
             (if (eq v :ok)
                 (let* ((fn-hrecs$c (update-fn-hrc-img 1 fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-nimg n fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-lens lens fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-starts starts fn-hrecs$c))
                        (fn-hrecs$c (update-fn-hrc-npages np fn-hrecs$c)))
                   (mv :ok fn-hrecs$c))
               (mv v fn-hrecs$c))))

(defun fn-hrc-flush-step (fn-hrecs$c)
  ; the oldest suffix event into the image (`fn-hp-x-append-step')
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (fn-hrc-wfp fn-hrecs$c) (< (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
                  :guard-hints (("Goal" :in-theory (disable fn-hp-x-append-step)))))
  (let ((lo (fn-hrc-lo fn-hrecs$c))
        (ev (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c))
        (salt (fn-hrc-salt fn-hrecs$c))
        (n (fn-hrc-nimg fn-hrecs$c))
        (lens (fn-hrc-lens fn-hrecs$c))
        (starts (fn-hrc-starts fn-hrecs$c))
        (np (fn-hrc-npages fn-hrecs$c)))
    (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
               (v n2 lens2 starts2 np2 pgs-mem)
               (fn-hp-x-append-step ev salt n lens starts np pgs-mem)
               (let* ((fn-hrecs$c (update-fn-hrc-nimg n2 fn-hrecs$c))
                      (fn-hrecs$c (update-fn-hrc-lens lens2 fn-hrecs$c))
                      (fn-hrecs$c (update-fn-hrc-starts starts2 fn-hrecs$c))
                      (fn-hrecs$c (update-fn-hrc-npages np2 fn-hrecs$c))
                      (fn-hrecs$c (if (eq v :ok) (update-fn-hrc-lo (+ 1 lo) fn-hrecs$c) fn-hrecs$c)))
                 (mv v fn-hrecs$c)))))

(defthm fn-hrc-flush-init-frame
  (implies (fn-hrc-wfp fn-hrecs$c)
           (let ((c1 (mv-nth 1 (fn-hrc-flush-init fn-hrecs$c))))
             (and (fn-hrc-wfp c1)
                  (equal (fn-hrc-lo c1) (fn-hrc-lo fn-hrecs$c))
                  (equal (fn-hrc-hi c1) (fn-hrc-hi fn-hrecs$c))
                  (implies (equal (mv-nth 0 (fn-hrc-flush-init fn-hrecs$c)) :ok) (equal (fn-hrc-img c1) 1)))))
  :hints (("Goal" :in-theory (disable fn-hp-x-init))))

(defun fn-hrc-flush-one (fn-hrecs$c)
  ; The oldest suffix event into the image (the empty image first, when
  ; there is none): (mv VERDICT fn-hrecs$c).  :ok moves it; a need-verdict
  ; or refusal moves nothing (the placement a completed relocation
  ; answered is kept, as the step asks).  An empty suffix answers :ok.
  ; Work: the step's.
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-flush-init fn-hrc-flush-step fn-hrecs$cp
                                                            fn-hrc-lo fn-hrc-hi)))))
  (if (<= (fn-hrc-hi fn-hrecs$c) (fn-hrc-lo fn-hrecs$c))
      (mv :ok fn-hrecs$c)
    (mv-let (v0 fn-hrecs$c)
      (if (equal (fn-hrc-img fn-hrecs$c) 1) (mv :ok fn-hrecs$c) (fn-hrc-flush-init fn-hrecs$c))
      (if (not (eq v0 :ok))
          (mv v0 fn-hrecs$c)
        (fn-hrc-flush-step fn-hrecs$c)))))

; -----------------------------------------------------------------------------
; C. The concrete's primitives closed: reads over writes, types, the suffix
; window over the writes.

(defthm fn-hrs-sfx-list-len
  (equal (len (fn-hrc-sfx-list i hi c)) (nfix (- (nfix hi) (nfix i))))
  :hints (("Goal" :in-theory (enable fn-hrc-sfx-list))))

(local
 (defun fn-hrs-ind-ik (i k hi)
   (declare (xargs :measure (nfix (- (nfix hi) (nfix i)))))
   (if (or (zp (- (nfix hi) (nfix i))) (zp k)) (list i k hi) (fn-hrs-ind-ik (+ 1 (nfix i)) (1- k) hi))))

(defthm fn-hrs-sfx-list-nth
  (implies (and (natp i) (natp k) (< k (- (nfix hi) i)))
           (equal (nth k (fn-hrc-sfx-list i hi c)) (fn-hrc-sfxi (+ i k) c)))
  :hints (("Goal" :induct (fn-hrs-ind-ik i k hi) :in-theory (enable nth fn-hrc-sfx-list)
           :expand ((fn-hrc-sfx-list i hi c)))))

(local
 (defthm fn-hrs-nth-resize-list
   (implies (and (natp i) (< i (len l)) (< i (nfix n)))
            (equal (nth i (resize-list l n d)) (nth i l)))
   :hints (("Goal" :in-theory (enable nth resize-list) :induct (resize-list l n d) :expand ((nth i l))))))

(local
 (defthm fn-hrs-car-resize-list
   (implies (and (consp l) (posp n)) (equal (car (resize-list l n d)) (car l)))
   :hints (("Goal" :expand ((resize-list l n d))))))



(defthm fn-hrc-sfxp-is-true-listp
  (equal (fn-hrc-sfxp x) (true-listp x)))


(defthm fn-hrs-sfx-list-of-updates
  (and (equal (fn-hrc-sfx-list i hi (update-fn-hrc-img v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-salt v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-nimg v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-lens v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-starts v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-npages v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-txid v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-lo v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-hi v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-pgs v c)) (fn-hrc-sfx-list i hi c))
       (equal (fn-hrc-sfx-list i hi (update-fn-hrc-oct v c)) (fn-hrc-sfx-list i hi c)))
  :hints (("Goal" :induct (fn-hrc-sfx-list i hi c) :in-theory (enable fn-hrc-sfx-list))))

(defthm fn-hrs-sfx-list-of-update-above
  (implies (and (natp j) (<= (nfix hi) j))
           (equal (fn-hrc-sfx-list i hi (update-fn-hrc-sfxi j v c)) (fn-hrc-sfx-list i hi c)))
  :hints (("Goal" :induct (fn-hrc-sfx-list i hi c) :in-theory (enable fn-hrc-sfx-list))))

(defthm fn-hrs-sfx-list-of-resize
  (implies (and (<= (nfix hi) (fn-hrc-sfx-length c)) (<= (nfix hi) (nfix n)))
           (equal (fn-hrc-sfx-list i hi (resize-fn-hrc-sfx n c)) (fn-hrc-sfx-list i hi c)))
  :hints (("Goal" :induct (fn-hrc-sfx-list i hi c) :in-theory (enable fn-hrc-fields fn-hrc-updaters))))

(defthm fn-hrs-sfx-list-snoc
  (implies (and (natp lo) (natp hi) (<= lo hi) (< hi (fn-hrc-sfx-length c)))
           (equal (fn-hrc-sfx-list lo (+ 1 hi) (update-fn-hrc-sfxi hi ev c))
                  (append (fn-hrc-sfx-list lo hi c) (list ev))))
  :hints (("Goal" :induct (fn-hrc-sfx-list lo hi c) :in-theory (enable fn-hrc-sfx-list)
           :expand ((fn-hrc-sfx-list lo (+ 1 hi) (update-fn-hrc-sfxi hi ev c))))))


(defthm fn-hrc-append-wfp
  (implies (and (fn-hrc-wfp fn-hrecs$c))
           (fn-hrc-wfp (fn-hrc-append ev fn-hrecs$c))))

; -----------------------------------------------------------------------------
; D. The relation: the concrete holds the history H.
;
; `fn-hrs-rel' H C: H is the image's N events followed by the suffix
; window's.  `fn-hrs-img-ok' IMG C: with an image, IMG is what it holds --
; the header is IMG's, and every VERIFIED page of the nested page store
; holds IMG's placed image (`fn-hp-vhold' of `fn-hp-piw').  Pages not
; verified are unconstrained: a read that needs one answers a need-verdict,
; and the fill (section F) is where their words come from.

(defun-nx fn-hrs-img-ok (img fn-hrecs$c)
  (let* ((c fn-hrecs$c) (pgs (fn-hrc-pgs c)) (salt (fn-hrc-salt c)))
    (implies (equal (fn-hrc-img c) 1)
             (and (fn-hp-okp img salt)
                  (equal (fn-hrc-lens c) (fn-hp-lens img salt))
                  (adt-placement-ok (fn-hrc-starts c) (fn-hrc-lens c) (fn-hrc-npages c))
                  (fn-hp-vhold 0 (pgs-v-length pgs) pgs (fn-hp-piw img salt (fn-hrc-starts c) (fn-hrc-npages c)))))))

(defun-nx fn-hrs-rel (h fn-hrecs$c)
  (let ((c fn-hrecs$c))
    (and (true-listp h) (<= (fn-hrc-nimg c) (len h))
         (equal (nthcdr (fn-hrc-nimg c) h) (fn-hrc-sfx-list (fn-hrc-lo c) (fn-hrc-hi c) c))
         (fn-hrs-img-ok (take (fn-hrc-nimg c) h) c))))

(defthm fn-hrs-img-ok-of-updates
  (and (equal (fn-hrs-img-ok img (update-fn-hrc-nimg v c)) (fn-hrs-img-ok img c))
       (equal (fn-hrs-img-ok img (update-fn-hrc-txid v c)) (fn-hrs-img-ok img c))
       (equal (fn-hrs-img-ok img (update-fn-hrc-lo v c)) (fn-hrs-img-ok img c))
       (equal (fn-hrs-img-ok img (update-fn-hrc-hi v c)) (fn-hrs-img-ok img c))
       (equal (fn-hrs-img-ok img (update-fn-hrc-sfxi i v c)) (fn-hrs-img-ok img c))
       (equal (fn-hrs-img-ok img (resize-fn-hrc-sfx n c)) (fn-hrs-img-ok img c))
       (equal (fn-hrs-img-ok img (update-fn-hrc-oct v c)) (fn-hrs-img-ok img c)))
  :hints (("Goal" :in-theory (disable fn-hp-okp fn-hp-lens fn-hp-piw fn-hp-vhold adt-placement-ok))))

(in-theory (disable fn-hrs-img-ok))

(local
 (defthm fn-hrs-take-append
   (implies (and (natp n) (<= n (len h))) (equal (take n (append h x)) (take n h)))
   :hints (("Goal" :in-theory (enable take)))))
(local
 (defthm fn-hrs-nthcdr-append
   (implies (and (natp n) (<= n (len h))) (equal (nthcdr n (append h x)) (append (nthcdr n h) x)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-hrc-append-rel
  (implies (and (fn-hrc-wfp fn-hrecs$c) (fn-hrs-rel h fn-hrecs$c))
           (fn-hrs-rel (append h (list ev)) (fn-hrc-append ev fn-hrecs$c)))
  :hints (("Goal" :in-theory (disable take nthcdr))))


(local
 (defthm fn-hrs-nth-nthcdr
   (implies (and (natp n) (natp k)) (equal (nth k (nthcdr n h)) (nth (+ n k) h)))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))
(local
 (defthm fn-hrs-len-nthcdr
   (implies (natp n) (equal (len (nthcdr n h)) (nfix (- (len h) n))))))
(local
 (defthm fn-hrs-nth-take
   (implies (and (natp k) (< k (nfix n))) (equal (nth k (take n h)) (nth k h)))
   :hints (("Goal" :in-theory (enable nth take)))))
(local
 (defthm fn-hrs-len-take
   (implies (and (natp n) (<= n (len h))) (equal (len (take n h)) n))))

(defthm fn-hrs-at-image
  (implies (and (fn-hp-okp img salt) (equal n (len img)) (equal lens (fn-hp-lens img salt))
                (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
                (fn-hp-vhold 0 (pgs-v-length pgs) pgs (fn-hp-piw img salt starts np))
                (natp seq) (< seq n) (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs)) :ok))
           (equal (mv-nth 1 (fn-hp-x-at seq salt n lens starts pgs)) (list :ok (nth seq img))))
  :hints (("Goal" :use ((:instance fn-hp-x-at-is-nth-placed (h img) (pgs-mem pgs)))
           :in-theory (disable fn-hp-x-at-is-nth-placed fn-hp-x-at fn-hp-okp fn-hp-lens fn-hp-piw fn-hp-vhold
                               adt-placement-ok))))

(defthm fn-hrc-at-image-case
  (implies (and (fn-hrs-rel h fn-hrecs$c) (fn-hrc-wfp fn-hrecs$c) (natp seq)
                (< seq (fn-hrc-nimg fn-hrecs$c))
                (equal (mv-nth 0 (fn-hrc-at seq fn-hrecs$c)) :ok))
           (equal (mv-nth 1 (fn-hrc-at seq fn-hrecs$c)) (list :ok (nth seq h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrs-at-image
                            (img (take (fn-hrc-nimg fn-hrecs$c) h)) (salt (fn-hrc-salt fn-hrecs$c))
                            (n (fn-hrc-nimg fn-hrecs$c)) (lens (fn-hrc-lens fn-hrecs$c))
                            (starts (fn-hrc-starts fn-hrecs$c)) (np (fn-hrc-npages fn-hrecs$c))
                            (pgs (fn-hrc-pgs fn-hrecs$c))))
           :in-theory (e/d (fn-hrs-img-ok) (fn-hrs-at-image fn-hp-x-at fn-hp-okp fn-hp-lens fn-hp-piw fn-hp-vhold adt-placement-ok take nthcdr)))))

(defthm fn-hrc-at-suffix-case
  (implies (and (fn-hrs-rel h fn-hrecs$c) (fn-hrc-wfp fn-hrecs$c) (natp seq)
                (not (< seq (fn-hrc-nimg fn-hrecs$c))))
           (equal (fn-hrc-at seq fn-hrecs$c)
                  (mv :ok (if (< seq (len h)) (list :ok (nth seq h)) (list :refused :seq)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrs-sfx-list-nth (i (fn-hrc-lo fn-hrecs$c)) (hi (fn-hrc-hi fn-hrecs$c))
                            (c fn-hrecs$c) (k (- seq (fn-hrc-nimg fn-hrecs$c))))
                 (:instance fn-hrs-nth-nthcdr (n (fn-hrc-nimg fn-hrecs$c)) (k (- seq (fn-hrc-nimg fn-hrecs$c))))
                 (:instance fn-hrs-sfx-list-len (i (fn-hrc-lo fn-hrecs$c)) (hi (fn-hrc-hi fn-hrecs$c)) (c fn-hrecs$c))
                 (:instance fn-hrs-len-nthcdr (n (fn-hrc-nimg fn-hrecs$c))))
           :in-theory (disable fn-hrs-img-ok fn-hrs-sfx-list-nth fn-hrs-nth-nthcdr fn-hp-x-at fn-hrs-sfx-list-len fn-hrs-len-nthcdr
                               take nthcdr))))

; KEYSTONE (concrete): an :ok answer of the read is record SEQ of H, or
; (:refused :seq) past its end; any other verdict is a need-verdict.
(defthm fn-hrc-at-is-nth
  (implies (and (fn-hrs-rel h fn-hrecs$c) (fn-hrc-wfp fn-hrecs$c) (natp seq))
           (let ((res (fn-hrc-at seq fn-hrecs$c)))
             (and (implies (equal (mv-nth 0 res) :ok)
                           (equal (mv-nth 1 res) (if (< seq (len h)) (list :ok (nth seq h)) (list :refused :seq))))
                  (implies (not (equal (mv-nth 0 res) :ok))
                           (and (< seq (len h)) (fn-hp-need-verdictp (mv-nth 0 res)))))))
  :hints (("Goal" :do-not-induct t :cases ((< seq (fn-hrc-nimg fn-hrecs$c)))
           :use ((:instance fn-hp-x-at-verdict (salt (fn-hrc-salt fn-hrecs$c)) (n (fn-hrc-nimg fn-hrecs$c))
                            (lens (fn-hrc-lens fn-hrecs$c)) (starts (fn-hrc-starts fn-hrecs$c))
                            (pgs-mem (fn-hrc-pgs fn-hrecs$c))))
           :in-theory (disable fn-hrs-rel fn-hp-x-at fn-hp-need-verdictp fn-hp-x-at-verdict fn-hrc-wfp))
          ("Subgoal 1" :in-theory (e/d (fn-hrs-rel) (fn-hp-x-at fn-hp-need-verdictp fn-hp-x-at-verdict fn-hrc-wfp fn-hrs-img-ok take nthcdr
                                                     fn-hrc-at-suffix-case fn-hrc-at-image-case))
           :use ((:instance fn-hrc-at-image-case)
                 (:instance fn-hp-x-at-verdict (salt (fn-hrc-salt fn-hrecs$c)) (n (fn-hrc-nimg fn-hrecs$c))
                            (lens (fn-hrc-lens fn-hrecs$c)) (starts (fn-hrc-starts fn-hrecs$c))
                            (pgs-mem (fn-hrc-pgs fn-hrecs$c)))))))

(defthm fn-hrc-count-is-len
  (implies (and (fn-hrs-rel h fn-hrecs$c) (fn-hrc-wfp fn-hrecs$c))
           (equal (fn-hrc-count fn-hrecs$c) (len h)))
  :hints (("Goal" :in-theory (disable fn-hrs-img-ok fn-hrs-len-nthcdr fn-hrs-sfx-list-len take nthcdr)
           :use ((:instance fn-hrs-sfx-list-len (i (fn-hrc-lo fn-hrecs$c)) (hi (fn-hrc-hi fn-hrecs$c)) (c fn-hrecs$c))
                 (:instance fn-hrs-len-nthcdr (n (fn-hrc-nimg fn-hrecs$c)))))))

; -----------------------------------------------------------------------------
; E. The fill keeps the relation when it writes the image's page.

(defthm fn-hrs-put-words
  (implies (and (natp j) (true-listp ws) (<= (+ j (len ws)) (pgs-w-length pgs-mem)))
           (equal (nth *pgs-wi* (fn-hrs-put j ws pgs-mem))
                  (fn-hp-rep (nth *pgs-wi* pgs-mem) j ws)))
  :hints (("Goal" :induct (fn-hrs-put j ws pgs-mem) :in-theory (enable pgs-w-length))))

(defthm fn-hrs-put-rest
  (and (equal (nth *pgs-vi* (fn-hrs-put j ws pgs-mem)) (nth *pgs-vi* pgs-mem))
       (equal (nth *pgs-tvi* (fn-hrs-put j ws pgs-mem)) (nth *pgs-tvi* pgs-mem))
       (equal (nth *pgs-ti* (fn-hrs-put j ws pgs-mem)) (nth *pgs-ti* pgs-mem))
       (equal (pgs-v-length (fn-hrs-put j ws pgs-mem)) (pgs-v-length pgs-mem))
       (implies (and (natp j) (<= (+ j (len ws)) (pgs-w-length pgs-mem)))
                (equal (pgs-w-length (fn-hrs-put j ws pgs-mem)) (pgs-w-length pgs-mem))))
  :hints (("Goal" :induct (fn-hrs-put j ws pgs-mem) :in-theory (enable pgs-w-length pgs-v-length update-pgs-wi))))

; the page store's check changes one flag at most
(defthm fn-hrs-open-page-shape
  (let ((m2 (mv-nth 1 (pgs-x-open-page i txid mode pgs-mem fn-octets-pg))))
    (or (equal m2 pgs-mem)
        (equal m2 (update-pgs-vi i (if (pgs-entry-checked-p (pgs-x-get-entry 2 0 i pgs-mem) txid mode) 2 1) pgs-mem))))
  :rule-classes nil)

(defthm fn-hrs-vhold-set-flag
  (implies (and (fn-hp-vhold s np m iw) (natp p)
                (equal (take 2048 (nthcdr (* 2048 p) (nth *pgs-wi* m))) (take 2048 (nthcdr (* 2048 p) iw))))
           (fn-hp-vhold s np (update-pgs-vi p x m) iw))
  :hints (("Goal" :induct (fn-hp-vhold s np m iw) :in-theory (e/d (update-pgs-vi pgs-vi) (take nthcdr)))))

(local
 (defthm fn-hrs-append-take-nthcdr
   (implies (and (natp j) (<= j (len w)))
            (equal (append (take j w) (nthcdr j w)) w))
   :hints (("Goal" :in-theory (enable take nthcdr)))))

(local
 (defthm fn-hrs-nthcdr-nthcdr
   (implies (and (natp a) (natp b)) (equal (nthcdr a (nthcdr b l)) (nthcdr (+ a b) l)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-hrs-rep-own-block
  (implies (and (natp o) (natp n) (true-listp b) (<= (+ o n) (len b)))
           (equal (fn-hp-rep b o (take n (nthcdr o b))) b))
  :hints (("Goal" :in-theory (enable fn-hp-rep)
           :use ((:instance fn-hrs-append-take-nthcdr (j n) (w (nthcdr o b)))
                 (:instance fn-hrs-append-take-nthcdr (j o) (w b))))))

(defthm fn-hrs-rep-block
  (implies (and (natp o) (<= o (len b)) (true-listp x))
           (equal (take (len x) (nthcdr o (fn-hp-rep b o x))) x))
  :hints (("Goal" :in-theory (enable fn-hp-rep))))

(defthm fn-hrs-u64-take-long
  (implies (and (fn-hp-u64-listp (take n l)) (natp n)) (<= n (len l)))
  :hints (("Goal" :in-theory (enable take fn-hp-u64-listp)))
  :rule-classes nil)

(defthm fn-hrs-fill-pgs-unchanged
  (implies (not (and (< p (pgs-v-length pgs-mem)) (<= (* 2048 (+ 1 p)) (pgs-w-length pgs-mem))
                     (not (equal (pgs-vi p pgs-mem) 2)) (fn-hp-u64-listp words) (equal (len words) 2048)))
           (equal (mv-nth 1 (fn-hrs-fill-pgs p words txid pgs-mem fn-octets-pg)) pgs-mem))
  :hints (("Goal" :in-theory (disable fn-hrs-put pgs-x-open-page fn-hp-u64-listp))))

(defthm fn-hrs-fill-pgs-vhold-write
  (implies (and (natp p) (true-listp iw)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw)
                (< p (pgs-v-length pgs-mem)) (<= (* 2048 (+ 1 p)) (pgs-w-length pgs-mem))
                (not (equal (pgs-vi p pgs-mem) 2)) (fn-hp-u64-listp words) (equal (len words) 2048)
                (equal words (take 2048 (nthcdr (* 2048 p) iw))))
           (let ((m2 (mv-nth 1 (fn-hrs-fill-pgs p words txid pgs-mem fn-octets-pg))))
             (and (equal (pgs-v-length m2) (pgs-v-length pgs-mem))
                  (fn-hp-vhold 0 (pgs-v-length m2) m2 iw))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (pgs-w-length) (fn-hp-vhold fn-hp-rep take nthcdr pgs-x-open-page fn-hrs-put fn-hp-u64-listp
                               fn-hp-vhold-of-wreps fn-hrs-vhold-set-flag fn-hrs-rep-own-block fn-hrs-rep-block fn-hrs-put-words fn-hrs-put-rest))
           :use ((:instance fn-hrs-put-words (j (* 2048 p)) (ws words))
                 (:instance fn-hrs-put-rest (j (* 2048 p)) (ws words))
                 (:instance fn-hrs-open-page-shape (i p) (mode :eager)
                            (pgs-mem (fn-hrs-put (* 2048 p) words pgs-mem)))
                 (:instance fn-hrs-u64-take-long (n 2048) (l (nthcdr (* 2048 p) iw)))
                 (:instance fn-hp-vhold-of-wreps (p 0) (np (pgs-v-length pgs-mem)) (bs (list (cons (* 2048 p) words)))
                            (mem2 (fn-hrs-put (* 2048 p) words pgs-mem)))
                 (:instance fn-hrs-rep-own-block (o (* 2048 p)) (n 2048) (b iw))
                 (:instance fn-hrs-rep-block (o (* 2048 p)) (b (nth *pgs-wi* pgs-mem)) (x words))
                 (:instance fn-hrs-vhold-set-flag (s 0) (np (pgs-v-length pgs-mem))
                            (m (fn-hrs-put (* 2048 p) words pgs-mem)) (x 2))
                 (:instance fn-hrs-vhold-set-flag (s 0) (np (pgs-v-length pgs-mem))
                            (m (fn-hrs-put (* 2048 p) words pgs-mem)) (x 1))))))

(defthm fn-hrs-fill-pgs-vhold
  (implies (and (natp p) (true-listp iw)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw)
                (implies (and (< p (pgs-v-length pgs-mem)) (not (equal (pgs-vi p pgs-mem) 2)))
                         (equal words (take 2048 (nthcdr (* 2048 p) iw)))))
           (let ((m2 (mv-nth 1 (fn-hrs-fill-pgs p words txid pgs-mem fn-octets-pg))))
             (and (equal (pgs-v-length m2) (pgs-v-length pgs-mem))
                  (fn-hp-vhold 0 (pgs-v-length m2) m2 iw))))
  :hints (("Goal" :use ((:instance fn-hrs-fill-pgs-unchanged) (:instance fn-hrs-fill-pgs-vhold-write))
           :in-theory (union-theories '(not) (theory 'minimal-theory)))))

(defthm fn-hrs-true-listp-piw
  (true-listp (fn-hp-piw h salt starts np)))



(defun-nx fn-hrs-image-page (p h fn-hrecs$c)
  (let ((c fn-hrecs$c))
    (take 2048 (nthcdr (* 2048 p) (fn-hp-piw (take (fn-hrc-nimg c) h) (fn-hrc-salt c) (fn-hrc-starts c) (fn-hrc-npages c))))))

(defthm fn-hrc-fill-shape
  (equal (mv-nth 1 (fn-hrc-fill p words fn-hrecs$c))
         (let ((r (fn-hrs-fill-pgs p words (fn-hrc-txid fn-hrecs$c) (fn-hrc-pgs fn-hrecs$c) (fn-hrc-oct fn-hrecs$c))))
           (update-fn-hrc-oct (mv-nth 2 r) (update-fn-hrc-pgs (mv-nth 1 r) fn-hrecs$c))))
  :hints (("Goal" :in-theory (disable fn-hrs-fill-pgs))))

(defthm fn-hrc-fill-img-ok
  (implies (and (fn-hrs-img-ok img fn-hrecs$c) (natp p)
                (implies (and (equal (fn-hrc-img fn-hrecs$c) 1)
                              (< p (pgs-v-length (fn-hrc-pgs fn-hrecs$c)))
                              (not (equal (pgs-vi p (fn-hrc-pgs fn-hrecs$c)) 2)))
                         (equal words (take 2048 (nthcdr (* 2048 p) (fn-hp-piw img (fn-hrc-salt fn-hrecs$c) (fn-hrc-starts fn-hrecs$c) (fn-hrc-npages fn-hrecs$c)))))))
           (fn-hrs-img-ok img (mv-nth 1 (fn-hrc-fill p words fn-hrecs$c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrs-img-ok) (fn-hrc-fill fn-hrs-fill-pgs fn-hp-okp fn-hp-lens fn-hp-piw fn-hp-vhold adt-placement-ok take nthcdr
                                             fn-hrs-fill-pgs-vhold fn-hp-piw-caps-extend fn-hp-placement-mono))
           :use ((:instance fn-hrs-fill-pgs-vhold (txid (fn-hrc-txid fn-hrecs$c)) (pgs-mem (fn-hrc-pgs fn-hrecs$c))
                            (fn-octets-pg (fn-hrc-oct fn-hrecs$c))
                            (iw (fn-hp-piw img (fn-hrc-salt fn-hrecs$c) (fn-hrc-starts fn-hrecs$c) (fn-hrc-npages fn-hrecs$c))))))))

(defthm fn-hrc-fill-rel
  (implies (and (fn-hrc-wfp fn-hrecs$c) (fn-hrs-rel h fn-hrecs$c) (natp p)
                (implies (and (equal (fn-hrc-img fn-hrecs$c) 1)
                              (< p (pgs-v-length (fn-hrc-pgs fn-hrecs$c)))
                              (not (equal (pgs-vi p (fn-hrc-pgs fn-hrecs$c)) 2)))
                         (equal words (fn-hrs-image-page p h fn-hrecs$c))))
           (let ((c2 (mv-nth 1 (fn-hrc-fill p words fn-hrecs$c))))
             (and (fn-hrc-wfp c2) (fn-hrs-rel h c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hrc-fill fn-hrs-fill-pgs fn-hrs-img-ok fn-hrc-fill-img-ok take nthcdr fn-hp-piw)
           :use ((:instance fn-hrc-fill-img-ok (img (take (fn-hrc-nimg fn-hrecs$c) h)))))))

; -----------------------------------------------------------------------------
; F. The flush keeps the relation.
;
; `fn-hp-x-append-step-refines' says what a step's answer means but not,
; for an answer other than :ok, that the placement it leaves is valid: a
; relocation that completed before a need-verdict leaves STARTS2 NP2 with
; H's image.  The read's keystone (`fn-hp-x-at-is-nth-placed') needs the
; placement valid, so it is proved here over the loop: a relocation that
; answers :ok leaves a valid placement (`fn-hp-x-relocate-refines').

(defthm fn-hrs-loop-placement
  (implies (and (fn-hp-okp h salt) (fn-hp-starts-okp starts)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (adt-placement-ok starts (fn-hp-lens h salt) np)
                (not (equal (mv-nth 0 (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)) :ok)))
           (let ((res (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))
             (adt-placement-ok (mv-nth 3 res) (fn-hp-lens h salt) (mv-nth 4 res))))
  :hints (("Goal" :induct (fn-hp-x-append-loop k ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)
           :in-theory (set-difference-theories
                       (union-theories '(fn-hp-x-append-loop zp (:e zp) eq not fn-hp-mv-nth-cons natp (:e natp))
                                       (theory 'minimal-theory))
                       '(mv-nth)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-hp-x-append-grow-shape (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-x-append-grow-mem (lens (fn-hp-lens h salt)) (n (len h)))
                       (:instance fn-hp-x-relocate-not-ok-unchanged (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))))
                                  (c (caddr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))))
                       (:instance fn-hp-x-relocate-refines (lens (fn-hp-lens h salt)) (n (len h))
                                  (r (cadr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem))))
                                  (c (caddr (mv-nth 0 (fn-hp-x-append ev salt (len h) (fn-hp-lens h salt) starts np pgs-mem)))))
                       (:instance fn-hp-nat-listp-lens (h h))
                       (:instance fn-hp-len-lens (h h)))))))
(defthm fn-hrs-x-init-not-ok
  (implies (not (equal (mv-nth 0 (fn-hp-x-init pgs-mem)) :ok))
           (equal (mv-nth 5 (fn-hp-x-init pgs-mem)) pgs-mem))
  :hints (("Goal" :in-theory (disable pgs-x-grow-image fn-hp-x-put))))

(defthm fn-hrc-flush-init-shape
  (equal (fn-hrc-flush-init fn-hrecs$c)
         (let* ((r (fn-hp-x-init (fn-hrc-pgs fn-hrecs$c)))
                (c1 (update-fn-hrc-pgs (mv-nth 5 r) fn-hrecs$c)))
           (if (eq (mv-nth 0 r) :ok)
               (mv :ok (update-fn-hrc-npages (mv-nth 4 r) (update-fn-hrc-starts (mv-nth 3 r)
                         (update-fn-hrc-lens (mv-nth 2 r) (update-fn-hrc-nimg (mv-nth 1 r) (update-fn-hrc-img 1 c1))))))
             (mv (mv-nth 0 r) c1))))
  :hints (("Goal" :in-theory (disable fn-hp-x-init))))

(defthm fn-hrc-flush-init-rel
  (implies (and (fn-hrc-wfp fn-hrecs$c) (fn-hrs-rel h fn-hrecs$c) (equal (fn-hrc-img fn-hrecs$c) 0))
           (let ((r (fn-hrc-flush-init fn-hrecs$c)))
             (and (fn-hrc-wfp (mv-nth 1 r)) (fn-hrs-rel h (mv-nth 1 r))
                  (implies (equal (mv-nth 0 r) :ok) (equal (fn-hrc-img (mv-nth 1 r)) 1)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-init-refines (pgs-mem (fn-hrc-pgs fn-hrecs$c)) (salt (fn-hrc-salt fn-hrecs$c))))
           :in-theory (e/d (fn-hrs-img-ok) (fn-hrc-flush-init fn-hp-x-init fn-hp-x-init-refines fn-hp-okp fn-hp-lens fn-hp-piw fn-hp-vhold
                                            adt-placement-ok)))))


(defthm fn-hrc-flush-step-shape
  (equal (fn-hrc-flush-step fn-hrecs$c)
         (let* ((r (fn-hp-x-append-step (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c) (fn-hrc-salt fn-hrecs$c)
                                        (fn-hrc-nimg fn-hrecs$c) (fn-hrc-lens fn-hrecs$c) (fn-hrc-starts fn-hrecs$c)
                                        (fn-hrc-npages fn-hrecs$c) (fn-hrc-pgs fn-hrecs$c)))
                (c2 (update-fn-hrc-npages (mv-nth 4 r) (update-fn-hrc-starts (mv-nth 3 r)
                      (update-fn-hrc-lens (mv-nth 2 r) (update-fn-hrc-nimg (mv-nth 1 r)
                        (update-fn-hrc-pgs (mv-nth 5 r) fn-hrecs$c)))))))
           (mv (mv-nth 0 r) (if (eq (mv-nth 0 r) :ok) (update-fn-hrc-lo (+ 1 (fn-hrc-lo fn-hrecs$c)) c2) c2))))
  :hints (("Goal" :in-theory (disable fn-hp-x-append-step))))

(defthmd fn-hrs-take-plus-one
   (implies (and (natp n) (< n (len h)))
            (equal (take (+ 1 n) h) (append (take n h) (list (nth n h)))))
   :hints (("Goal" :in-theory (enable take nth))))

(local
 (defthm fn-hrs-sfx-list-open
   (implies (and (natp lo) (< lo (nfix hi)))
            (equal (fn-hrc-sfx-list lo hi c) (cons (fn-hrc-sfxi lo c) (fn-hrc-sfx-list (+ 1 lo) hi c))))
   :hints (("Goal" :in-theory (enable fn-hrc-sfx-list)))))

(defthm fn-hrs-step-facts
  (implies (and (fn-hp-okp img salt) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens img salt) np)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw img salt starts np)))
           (let ((res (fn-hp-x-append-step ev salt (len img) (fn-hp-lens img salt) starts np pgs-mem)))
             (and (fn-hp-starts-okp (mv-nth 3 res))
                  (implies (equal (mv-nth 0 res) :ok)
                           (and (fn-hp-okp (append img (list ev)) salt)
                                (equal (mv-nth 1 res) (+ 1 (len img)))
                                (equal (mv-nth 2 res) (fn-hp-lens (append img (list ev)) salt))
                                (adt-placement-ok (mv-nth 3 res) (mv-nth 2 res) (mv-nth 4 res))
                                (fn-hp-vhold 0 (pgs-v-length (mv-nth 5 res)) (mv-nth 5 res)
                                             (fn-hp-piw (append img (list ev)) salt (mv-nth 3 res) (mv-nth 4 res)))))
                  (implies (not (equal (mv-nth 0 res) :ok))
                           (and (equal (mv-nth 1 res) (len img)) (equal (mv-nth 2 res) (fn-hp-lens img salt))
                                (adt-placement-ok (mv-nth 3 res) (fn-hp-lens img salt) (mv-nth 4 res))
                                (fn-hp-vhold 0 (pgs-v-length (mv-nth 5 res)) (mv-nth 5 res)
                                             (fn-hp-piw img salt (mv-nth 3 res) (mv-nth 4 res))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-append-step-refines (h img) (n (len img)) (lens (fn-hp-lens img salt)))
                 (:instance fn-hrs-loop-placement (h img) (k 5)))
           :in-theory (union-theories '(fn-hp-x-append-step fn-hp-len-append1) (theory 'minimal-theory)))))

(local (defthm fn-hrs-nthcdr-0 (equal (nthcdr 0 x) x)))

(defthm fn-hrs-sfx-head
  (implies (and (fn-hrc-wfp fn-hrecs$c) (fn-hrs-rel h fn-hrecs$c) (< (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
           (and (< (fn-hrc-nimg fn-hrecs$c) (len h))
                (equal (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c) (nth (fn-hrc-nimg fn-hrecs$c) h))
                (equal (nthcdr (+ 1 (fn-hrc-nimg fn-hrecs$c)) h)
                       (fn-hrc-sfx-list (+ 1 (fn-hrc-lo fn-hrecs$c)) (fn-hrc-hi fn-hrecs$c) fn-hrecs$c))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrs-sfx-list-open (lo (fn-hrc-lo fn-hrecs$c)) (hi (fn-hrc-hi fn-hrecs$c)) (c fn-hrecs$c))
                 (:instance fn-hrs-nth-nthcdr (n (fn-hrc-nimg fn-hrecs$c)) (k 0))
                 (:instance fn-hrs-len-nthcdr (n (fn-hrc-nimg fn-hrecs$c)))
                 (:instance fn-hrs-sfx-list-len (i (fn-hrc-lo fn-hrecs$c)) (hi (fn-hrc-hi fn-hrecs$c)) (c fn-hrecs$c))
                 (:instance adt-cdr-nthcdr (j (fn-hrc-nimg fn-hrecs$c)) (r h))
                 (:instance adt-car-nthcdr (j (fn-hrc-nimg fn-hrecs$c)) (r h)))
           :in-theory (e/d (fn-hrs-rel) (fn-hrs-sfx-list-open fn-hrs-nth-nthcdr fn-hrs-len-nthcdr fn-hrs-img-ok fn-hrs-sfx-list-len
                                         adt-cdr-nthcdr adt-car-nthcdr take nthcdr fn-cp-id-length-bound)))))

(defthm fn-hrc-flush-step-rel
  (implies (and (fn-hrc-wfp fn-hrecs$c) (fn-hrs-rel h fn-hrecs$c) (equal (fn-hrc-img fn-hrecs$c) 1)
                (< (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
           (let ((c2 (mv-nth 1 (fn-hrc-flush-step fn-hrecs$c))))
             (and (fn-hrc-wfp c2) (fn-hrs-rel h c2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrs-step-facts (img (take (fn-hrc-nimg fn-hrecs$c) h))
                            (ev (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c)) (salt (fn-hrc-salt fn-hrecs$c))
                            (starts (fn-hrc-starts fn-hrecs$c))
                            (np (fn-hrc-npages fn-hrecs$c)) (pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                 (:instance fn-hrs-append-step-types
                            (ev (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c)) (salt (fn-hrc-salt fn-hrecs$c))
                            (n (fn-hrc-nimg fn-hrecs$c)) (lens (fn-hrc-lens fn-hrecs$c)) (starts (fn-hrc-starts fn-hrecs$c))
                            (np (fn-hrc-npages fn-hrecs$c)) (pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                 (:instance fn-hrs-sfx-head)
                 (:instance fn-hrs-take-plus-one (n (fn-hrc-nimg fn-hrecs$c))))
           :in-theory (union-theories
                       '(fn-hrs-rel fn-hrs-img-ok fn-hrc-wfp fn-hrc-flush-step-shape fn-hp-starts-okp
                         fn-hrc-row-img fn-hrc-row-salt fn-hrc-row-nimg fn-hrc-row-lens fn-hrc-row-starts fn-hrc-row-npages
                         fn-hrc-row-txid fn-hrc-row-lo fn-hrc-row-hi fn-hrc-row-pgs fn-hrs-sfx-list-of-updates fn-hrs-len-take
                         fn-hp-mv-nth-cons zp (:e zp) natp (:e natp) eq not fix (:t len) (:t take) (:t nthcdr))
                       (theory 'minimal-theory)))))
(defthm fn-hrc-wfp-img-cases
  (implies (fn-hrc-wfp fn-hrecs$c)
           (or (equal (fn-hrc-img fn-hrecs$c) 0) (equal (fn-hrc-img fn-hrecs$c) 1)))
  :rule-classes nil)

; KEYSTONE (concrete): the flush keeps the history: whatever it answers,
; the concrete it leaves holds the same H.
(defthm fn-hrc-flush-one-rel
  (implies (and (fn-hrc-wfp fn-hrecs$c) (fn-hrs-rel h fn-hrecs$c))
           (let ((c2 (mv-nth 1 (fn-hrc-flush-one fn-hrecs$c))))
             (and (fn-hrc-wfp c2) (fn-hrs-rel h c2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrc-flush-init-rel)
                 (:instance fn-hrc-flush-init-frame)
                 (:instance fn-hrc-flush-step-rel (fn-hrecs$c (mv-nth 1 (fn-hrc-flush-init fn-hrecs$c))))
                 (:instance fn-hrc-flush-step-rel) (:instance fn-hrc-wfp-img-cases))
           :in-theory (union-theories (quote (fn-hrc-flush-one fn-hp-mv-nth-cons zp (:e zp) eq not)) (theory (quote minimal-theory))))))
(local
 (defun-nx fn-hrs-load-ind (events h c)
   (if (atom events)
       (list h c)
     (fn-hrs-load-ind (cdr events) (append h (list (car events))) (fn-hrc-append (car events) c)))))

(defthm fn-hrs-rel-true-listp
  (implies (fn-hrs-rel h c) (true-listp h))
  :rule-classes :forward-chaining)

(defthm fn-hrc-load-events-rel
  (implies (and (fn-hrc-wfp fn-hrecs$c) (fn-hrs-rel h fn-hrecs$c))
           (let ((c2 (fn-hrc-load-events events fn-hrecs$c)))
             (and (fn-hrc-wfp c2) (fn-hrs-rel (append h (true-list-fix events)) c2))))
  :hints (("Goal" :induct (fn-hrs-load-ind events h fn-hrecs$c)
           :in-theory (disable fn-hrs-rel fn-hrc-append fn-hrc-wfp))
          ("Subgoal *1/2" :use ((:instance fn-hrc-append-rel (ev (car events)))
                                (:instance fn-hrc-append-wfp0 (ev (car events)))))))

(local (defthm fn-hrs-sfx-list-empty (equal (fn-hrc-sfx-list i i c) nil) :hints (("Goal" :in-theory (enable fn-hrc-sfx-list)))))

(defthm fn-hrc-reset-rel
  (fn-hrs-rel nil (fn-hrc-reset salt fn-hrecs$c))
  :hints (("Goal" :in-theory (enable fn-hrs-img-ok))))

; KEYSTONE (concrete): the load holds EVENTS.
(defthm fn-hrc-load-rel
  (implies (and (true-listp events) (natp salt))
           (let ((c2 (fn-hrc-load events salt fn-hrecs$c)))
             (and (fn-hrc-wfp c2) (fn-hrs-rel events c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hrc-load-events-rel fn-hrc-load-events fn-hrc-reset fn-hrs-rel fn-hrc-wfp fn-hrc-reset-rel
                               fn-hrc-reset-wfp)
           :use ((:instance fn-hrc-load-events-rel (h nil) (fn-hrecs$c (fn-hrc-reset salt fn-hrecs$c)))
                 (:instance fn-hrc-reset-rel) (:instance fn-hrc-reset-wfp)))))


(defthm fn-hrc-fill-wfp
  (implies (fn-hrc-wfp fn-hrecs$c) (fn-hrc-wfp (mv-nth 1 (fn-hrc-fill p words fn-hrecs$c))))
  :hints (("Goal" :in-theory (disable fn-hrc-fill fn-hrs-fill-pgs))))

(defthm fn-hrc-flush-step-wfp
  (implies (and (fn-hrc-wfp fn-hrecs$c) (< (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)) (equal (fn-hrc-img fn-hrecs$c) 1))
           (fn-hrc-wfp (mv-nth 1 (fn-hrc-flush-step fn-hrecs$c))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrs-append-step-types
                            (ev (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c)) (salt (fn-hrc-salt fn-hrecs$c))
                            (n (fn-hrc-nimg fn-hrecs$c)) (lens (fn-hrc-lens fn-hrecs$c)) (starts (fn-hrc-starts fn-hrecs$c))
                            (np (fn-hrc-npages fn-hrecs$c)) (pgs-mem (fn-hrc-pgs fn-hrecs$c))))
           :in-theory (union-theories
                       '(fn-hrc-wfp fn-hrc-flush-step-shape
                         fn-hrc-row-img fn-hrc-row-salt fn-hrc-row-nimg fn-hrc-row-lens fn-hrc-row-starts fn-hrc-row-npages
                         fn-hrc-row-txid fn-hrc-row-lo fn-hrc-row-hi fn-hrc-row-pgs
                         fn-hp-mv-nth-cons zp (:e zp) natp (:e natp) eq not fix)
                       (theory 'minimal-theory)))))

(defthm fn-hrc-flush-one-wfp
  (implies (fn-hrc-wfp fn-hrecs$c) (fn-hrc-wfp (mv-nth 1 (fn-hrc-flush-one fn-hrecs$c))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrc-flush-init-frame)
                 (:instance fn-hrc-flush-step-wfp (fn-hrecs$c (mv-nth 1 (fn-hrc-flush-init fn-hrecs$c))))
                 (:instance fn-hrc-flush-step-wfp) (:instance fn-hrc-wfp-img-cases))
           :in-theory (union-theories '(fn-hrc-flush-one fn-hp-mv-nth-cons zp (:e zp) eq not) (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; G. The abstract stobj.
;
; The abstract value is (H . C): H, the history, is a GHOST -- the logic
; carries it, the executable never computes it -- and C is the concrete.
; The correspondence is C itself; each export's logic runs the concrete
; operation on C and says what it does to H (append adds EV, load sets
; EVENTS, the others keep it).  What the exports MEAN is the relation
; (`fn-hrecs-faithful': C holds H), which every export keeps (section H).

(defun fn-hrs$ap (a)
  (declare (xargs :guard t))
  (and (consp a) (true-listp (car a))
       (non-exec (fn-hrc-wfp (cdr a)))))

(defun create-fn-hrs$a ()
  (declare (xargs :guard t))
  (cons nil (non-exec (create-fn-hrecs$c))))

(defun-nx fn-hrs$corr (fn-hrecs$c a)
  (equal fn-hrecs$c (cdr a)))

(defun fn-hrs$a-count (a)
  (declare (xargs :guard (fn-hrs$ap a)))
  (non-exec (fn-hrc-count (cdr a))))

(defun fn-hrs$a-at (seq a)
  (declare (xargs :guard (and (natp seq) (fn-hrs$ap a))))
  (let ((r (non-exec (fn-hrc-at seq (cdr a)))))
    (mv (mv-nth 0 r) (mv-nth 1 r))))

(defun fn-hrs$a-vlen (a)
  (declare (xargs :guard (fn-hrs$ap a)))
  (non-exec (fn-hrc-vlen (cdr a))))

(defun fn-hrs$a-phys (p a)
  (declare (xargs :guard (and (natp p) (fn-hrs$ap a))))
  (non-exec (fn-hrc-phys p (cdr a))))

(defun fn-hrs$a-append (ev a)
  (declare (xargs :guard (fn-hrs$ap a)))
  (cons (append (car a) (list ev)) (non-exec (fn-hrc-append ev (cdr a)))))

(defun fn-hrs$a-fill (p words a)
  (declare (xargs :guard (and (natp p) (fn-hrs$ap a))))
  (let ((r (non-exec (fn-hrc-fill p words (cdr a)))))
    (mv (mv-nth 0 r) (cons (car a) (mv-nth 1 r)))))

(defun fn-hrs$a-frame-fill (file addr p a)
  ; the fill at the realizer's words (fn-hrc-frame-fill's logic, by its mbe)
  (declare (xargs :guard (and (natp p) (fn-hrs$ap a))))
  (fn-hrs$a-fill p (fn-pgs-fill-realize file addr) a))

(defun fn-hrs$a-load (events salt a)
  (declare (xargs :guard (and (true-listp events) (natp salt) (fn-hrs$ap a))))
  (cons events (non-exec (fn-hrc-load events salt (cdr a)))))

(defun fn-hrs$a-flush (a)
  (declare (xargs :guard (fn-hrs$ap a)))
  (let ((r (non-exec (fn-hrc-flush-one (cdr a)))))
    (mv (mv-nth 0 r) (cons (car a) (mv-nth 1 r)))))

(defthm create-fn-hrecs{correspondence}
  (fn-hrs$corr (create-fn-hrecs$c) (create-fn-hrs$a))
  :rule-classes nil)

(defthm create-fn-hrecs{preserved}
  (fn-hrs$ap (create-fn-hrs$a))
  :hints (("Goal" :in-theory (enable fn-hrc-fields)))
  :rule-classes nil)

(defthm fn-hrecs-count{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (fn-hrs$ap fn-hrecs))
           (equal (fn-hrc-count fn-hrecs$c) (fn-hrs$a-count fn-hrecs)))
  :rule-classes nil)

(defthm fn-hrecs-count{guard-thm}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (fn-hrs$ap fn-hrecs))
           (fn-hrc-wfp fn-hrecs$c))
  :rule-classes nil)

(defthm fn-hrecs-at{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (natp seq) (fn-hrs$ap fn-hrecs))
           (let ((lhs (fn-hrc-at seq fn-hrecs$c)) (rhs (fn-hrs$a-at seq fn-hrecs)))
             (and (equal (mv-nth 0 lhs) (mv-nth 0 rhs)) (equal (mv-nth 1 lhs) (mv-nth 1 rhs)))))
  :hints (("Goal" :in-theory (disable fn-hrc-at)))
  :rule-classes nil)

(defthm fn-hrecs-at{guard-thm}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (natp seq) (fn-hrs$ap fn-hrecs))
           (and (natp seq) (fn-hrc-wfp fn-hrecs$c)))
  :rule-classes nil)

(defthm fn-hrecs-vlen{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (fn-hrs$ap fn-hrecs))
           (equal (fn-hrc-vlen fn-hrecs$c) (fn-hrs$a-vlen fn-hrecs)))
  :rule-classes nil)

(defthm fn-hrecs-phys{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (natp p) (fn-hrs$ap fn-hrecs))
           (equal (fn-hrc-phys p fn-hrecs$c) (fn-hrs$a-phys p fn-hrecs)))
  :rule-classes nil)

(defthm fn-hrecs-phys{guard-thm}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (natp p) (fn-hrs$ap fn-hrecs))
           (natp p))
  :rule-classes nil)

(defthm fn-hrecs-append{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (fn-hrs$ap fn-hrecs))
           (fn-hrs$corr (fn-hrc-append ev fn-hrecs$c) (fn-hrs$a-append ev fn-hrecs)))
  :hints (("Goal" :in-theory (disable fn-hrc-append)))
  :rule-classes nil)

(defthm fn-hrecs-append{guard-thm}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (fn-hrs$ap fn-hrecs))
           (fn-hrc-wfp fn-hrecs$c))
  :rule-classes nil)

(defthm fn-hrecs-append{preserved}
  (implies (fn-hrs$ap fn-hrecs)
           (fn-hrs$ap (fn-hrs$a-append ev fn-hrecs)))
  :hints (("Goal" :in-theory (disable fn-hrc-append fn-hrc-wfp)))
  :rule-classes nil)

(defthm fn-hrecs-fill{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (natp p) (fn-hrs$ap fn-hrecs))
           (let ((lhs (fn-hrc-fill p words fn-hrecs$c)) (rhs (fn-hrs$a-fill p words fn-hrecs)))
             (and (equal (mv-nth 0 lhs) (mv-nth 0 rhs)) (fn-hrs$corr (mv-nth 1 lhs) (mv-nth 1 rhs)))))
  :hints (("Goal" :in-theory (disable fn-hrc-fill fn-hrc-fill-shape fn-hrs-fill-pgs)))
  :rule-classes nil)

(defthm fn-hrecs-fill{guard-thm}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (natp p) (fn-hrs$ap fn-hrecs))
           (and (natp p) (fn-hrc-wfp fn-hrecs$c)))
  :rule-classes nil)

(defthm fn-hrecs-fill{preserved}
  (implies (and (natp p) (fn-hrs$ap fn-hrecs))
           (fn-hrs$ap (mv-nth 1 (fn-hrs$a-fill p words fn-hrecs))))
  :hints (("Goal" :in-theory (disable fn-hrc-fill fn-hrc-wfp fn-hrc-fill-shape)))
  :rule-classes nil)

; The frame fill's three: the list fill's at the realizer's words (both
; sides are that term by definition).
(defthm fn-hrecs-frame-fill{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (natp p) (fn-hrs$ap fn-hrecs))
           (let ((lhs (fn-hrc-frame-fill file addr p fn-hrecs$c))
                 (rhs (fn-hrs$a-frame-fill file addr p fn-hrecs)))
             (and (equal (mv-nth 0 lhs) (mv-nth 0 rhs)) (fn-hrs$corr (mv-nth 1 lhs) (mv-nth 1 rhs)))))
  :hints (("Goal" :use ((:instance fn-hrecs-fill{correspondence} (words (fn-pgs-fill-realize file addr))))
           :in-theory (e/d (fn-hrc-frame-fill fn-hrs$a-frame-fill)
                           (fn-hrc-fill fn-hrc-fill-shape fn-hrs-fill-pgs fn-hrs$a-fill))))
  :rule-classes nil)

(defthm fn-hrecs-frame-fill{guard-thm}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (natp p) (fn-hrs$ap fn-hrecs))
           (and (natp p) (fn-hrc-wfp fn-hrecs$c)))
  :rule-classes nil)

(defthm fn-hrecs-frame-fill{preserved}
  (implies (and (natp p) (fn-hrs$ap fn-hrecs))
           (fn-hrs$ap (mv-nth 1 (fn-hrs$a-frame-fill file addr p fn-hrecs))))
  :hints (("Goal" :use ((:instance fn-hrecs-fill{preserved} (words (fn-pgs-fill-realize file addr))))
           :in-theory (e/d (fn-hrs$a-frame-fill) (fn-hrs$a-fill fn-hrc-fill fn-hrc-wfp fn-hrc-fill-shape))))
  :rule-classes nil)

(defthm fn-hrecs-load{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (true-listp events) (natp salt) (fn-hrs$ap fn-hrecs))
           (fn-hrs$corr (fn-hrc-load events salt fn-hrecs$c) (fn-hrs$a-load events salt fn-hrecs)))
  :hints (("Goal" :in-theory (disable fn-hrc-load)))
  :rule-classes nil)

(defthm fn-hrecs-load{guard-thm}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (true-listp events) (natp salt) (fn-hrs$ap fn-hrecs))
           (and (true-listp events) (natp salt)))
  :rule-classes nil)

(defthm fn-hrecs-load{preserved}
  (implies (and (true-listp events) (natp salt) (fn-hrs$ap fn-hrecs))
           (fn-hrs$ap (fn-hrs$a-load events salt fn-hrecs)))
  :hints (("Goal" :use ((:instance fn-hrc-load-rel (fn-hrecs$c (cdr fn-hrecs))))
           :in-theory (disable fn-hrc-load fn-hrc-wfp fn-hrc-load-rel)))
  :rule-classes nil)

(defthm fn-hrecs-flush{correspondence}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (fn-hrs$ap fn-hrecs))
           (let ((lhs (fn-hrc-flush-one fn-hrecs$c)) (rhs (fn-hrs$a-flush fn-hrecs)))
             (and (equal (mv-nth 0 lhs) (mv-nth 0 rhs)) (fn-hrs$corr (mv-nth 1 lhs) (mv-nth 1 rhs)))))
  :hints (("Goal" :in-theory (disable fn-hrc-flush-one fn-hrc-flush-init fn-hrc-flush-step fn-hrc-flush-init-shape
                                      fn-hrc-flush-step-shape)))
  :rule-classes nil)

(defthm fn-hrecs-flush{guard-thm}
  (implies (and (fn-hrs$corr fn-hrecs$c fn-hrecs) (fn-hrs$ap fn-hrecs))
           (fn-hrc-wfp fn-hrecs$c))
  :rule-classes nil)

(defthm fn-hrecs-flush{preserved}
  (implies (fn-hrs$ap fn-hrecs)
           (fn-hrs$ap (mv-nth 1 (fn-hrs$a-flush fn-hrecs))))
  :hints (("Goal" :in-theory (disable fn-hrc-flush-one fn-hrc-wfp)))
  :rule-classes nil)

(defabsstobj fn-hrecs
  :foundation fn-hrecs$c
  :recognizer (fn-hrecs-p :logic fn-hrs$ap :exec fn-hrecs$cp)
  :creator (create-fn-hrecs :logic create-fn-hrs$a :exec create-fn-hrecs$c)
  :corr-fn fn-hrs$corr
  :exports ((fn-hrecs-count :logic fn-hrs$a-count :exec fn-hrc-count)
            (fn-hrecs-at :logic fn-hrs$a-at :exec fn-hrc-at)
            (fn-hrecs-vlen :logic fn-hrs$a-vlen :exec fn-hrc-vlen)
            (fn-hrecs-phys :logic fn-hrs$a-phys :exec fn-hrc-phys)
            (fn-hrecs-append :logic fn-hrs$a-append :exec fn-hrc-append :protect t)
            (fn-hrecs-fill :logic fn-hrs$a-fill :exec fn-hrc-fill :protect t)
            (fn-hrecs-frame-fill :logic fn-hrs$a-frame-fill :exec fn-hrc-frame-fill :protect t)
            (fn-hrecs-load :logic fn-hrs$a-load :exec fn-hrc-load :protect t)
            (fn-hrecs-flush :logic fn-hrs$a-flush :exec fn-hrc-flush-one :protect t)))


; -----------------------------------------------------------------------------
; H. What the exports mean.  `fn-hrecs-list': the history (the ghost);
; `fn-hrecs-faithful': the concrete holds it.  Every export keeps
; faithfulness (the fill: when it writes the image's page), and the read
; answers record SEQ of the history.

(defun-nx fn-hrecs-list (st) (car st))

(defun-nx fn-hrecs-faithful (st) (fn-hrs-rel (car st) (cdr st)))

; KEYSTONE: the read the host calls answers the history's record SEQ, or
; (:refused :seq) past its end; any other verdict is a need-verdict for a
; record the history has.
(defthm fn-hrecs-at-is-nth
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st) (natp seq))
           (let ((res (fn-hrecs-at seq st)) (h (fn-hrecs-list st)))
             (and (implies (equal (mv-nth 0 res) :ok)
                           (equal (mv-nth 1 res) (if (< seq (len h)) (list :ok (nth seq h)) (list :refused :seq))))
                  (implies (not (equal (mv-nth 0 res) :ok))
                           (and (< seq (len h)) (fn-hp-need-verdictp (mv-nth 0 res)))))))
  :hints (("Goal" :use ((:instance fn-hrc-at-is-nth (h (car st)) (fn-hrecs$c (cdr st))))
           :in-theory (disable fn-hrc-at-is-nth fn-hrc-at fn-hrs-rel fn-hrc-wfp))))

(defthm fn-hrecs-count-is-len
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st))
           (equal (fn-hrecs-count st) (len (fn-hrecs-list st))))
  :hints (("Goal" :use ((:instance fn-hrc-count-is-len (h (car st)) (fn-hrecs$c (cdr st))))
           :in-theory (disable fn-hrc-count-is-len fn-hrc-count fn-hrs-rel fn-hrc-wfp))))

(defthm fn-hrecs-append-appends
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st))
           (let ((st2 (fn-hrecs-append ev st)))
             (and (equal (fn-hrecs-list st2) (append (fn-hrecs-list st) (list ev)))
                  (fn-hrecs-faithful st2))))
  :hints (("Goal" :use ((:instance fn-hrc-append-rel (h (car st)) (fn-hrecs$c (cdr st))))
           :in-theory (disable fn-hrc-append-rel fn-hrc-append fn-hrs-rel fn-hrc-wfp))))

(defthm fn-hrecs-load-is-events
  (implies (and (true-listp events) (natp salt))
           (let ((st2 (fn-hrecs-load events salt st)))
             (and (equal (fn-hrecs-list st2) events) (fn-hrecs-faithful st2))))
  :hints (("Goal" :use ((:instance fn-hrc-load-rel (fn-hrecs$c (cdr st))))
           :in-theory (disable fn-hrc-load-rel fn-hrc-load fn-hrs-rel fn-hrc-wfp))))

; KEYSTONE: the flush keeps the history and its faithfulness, whatever it
; answers.
(defthm fn-hrecs-flush-keeps
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st))
           (let ((st2 (mv-nth 1 (fn-hrecs-flush st))))
             (and (equal (fn-hrecs-list st2) (fn-hrecs-list st)) (fn-hrecs-faithful st2))))
  :hints (("Goal" :use ((:instance fn-hrc-flush-one-rel (h (car st)) (fn-hrecs$c (cdr st))))
           :in-theory (disable fn-hrc-flush-one-rel fn-hrc-flush-one fn-hrs-rel fn-hrc-wfp))))

; The image page P of the history ST holds (what a fill must write).
(defun-nx fn-hrecs-image-page (p st) (fn-hrs-image-page p (car st) (cdr st)))

(defun-nx fn-hrecs-has-image (st) (equal (fn-hrc-img (cdr st)) 1))

; page P is one the image's reads may ask to fill: in the nested store, not verified
(defun-nx fn-hrecs-page-open (p st)
  (and (< p (pgs-v-length (fn-hrc-pgs (cdr st)))) (not (equal (pgs-vi p (fn-hrc-pgs (cdr st))) 2))))

; KEYSTONE: a fill keeps the history and, when it writes the image's page
; (or there is no image), its faithfulness -- whatever it answers.
(defthm fn-hrecs-fill-keeps
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st) (natp p)
                (implies (and (fn-hrecs-has-image st) (fn-hrecs-page-open p st))
                         (equal words (fn-hrecs-image-page p st))))
           (let ((st2 (mv-nth 1 (fn-hrecs-fill p words st))))
             (and (equal (fn-hrecs-list st2) (fn-hrecs-list st)) (fn-hrecs-faithful st2))))
  :hints (("Goal" :use ((:instance fn-hrc-fill-rel (h (car st)) (fn-hrecs$c (cdr st))))
           :in-theory (disable fn-hrc-fill-rel fn-hrc-fill fn-hrs-rel fn-hrc-wfp fn-hrs-image-page fn-hrc-fill-shape))))


; -----------------------------------------------------------------------------
; I. The need-verdicts name pages that are open.

(defun-nx fn-hrs-need-ok (v m)
  ; a (:need-page P ...) verdict names a page P of M that is not verified
  (implies (and (consp v) (equal (car v) :need-page))
           (and (natp (cadr v)) (< (cadr v) (pgs-v-length m)) (not (equal (pgs-vi (cadr v) m) 2)))))

(defthm fn-hrs-need-ok-of-atom
  (implies (not (consp v)) (fn-hrs-need-ok v m)))

(defthm fn-hrs-need-ok-ready
  (implies (natp p) (fn-hrs-need-ok (fn-hp-x-ready p pgs-mem) pgs-mem)))

(defthm fn-hrs-need-ok-ready-range
  (implies (natp p) (fn-hrs-need-ok (fn-hp-x-ready-range p hi pgs-mem) pgs-mem))
  :hints (("Goal" :induct (fn-hp-x-ready-range p hi pgs-mem) :in-theory (disable fn-hp-x-ready fn-hrs-need-ok))))

(defthm fn-hrs-need-ok-cell
  (implies (and (natp r) (natp seq) (nat-listp starts))
           (fn-hrs-need-ok (car (fn-hp-x-cell r seq starts pgs-mem)) pgs-mem))
  :hints (("Goal" :in-theory (disable fn-hp-x-ready fn-hrs-need-ok floor))))

(defthm fn-hrs-need-ok-pool
  (implies (natp lo) (fn-hrs-need-ok (fn-hp-x-pool-ready lo k pgs-mem) pgs-mem))
  :hints (("Goal" :in-theory (disable fn-hp-x-ready-range fn-hrs-need-ok))))

(defthm fn-hrs-natp-pool-lo
  (natp (fn-hp-pool-lo off starts))
  :rule-classes :type-prescription)

(defthm fn-hrs-need-ok-at
  (implies (and (natp seq) (nat-listp starts))
           (fn-hrs-need-ok (car (fn-hp-x-at seq salt n lens starts pgs-mem)) pgs-mem))
  :hints (("Goal" :in-theory (union-theories '(fn-hp-x-at fn-hrs-need-ok-cell fn-hrs-need-ok-pool fn-hrs-need-ok-of-atom
                                                fn-hrs-natp-pool-lo car-cons cdr-cons natp (:e natp) eq not
                                                mv-nth (:e zp) zp (:t fn-hp-pool-lo))
                                              (theory 'minimal-theory)))))

(defthm fn-hrecs-at-need-page
  (implies (and (fn-hrecs-p st) (natp seq)
                (consp (car (fn-hrecs-at seq st))) (equal (car (car (fn-hrecs-at seq st))) :need-page))
           (and (natp (cadr (car (fn-hrecs-at seq st))))
                (fn-hrecs-page-open (cadr (car (fn-hrecs-at seq st))) st)))
  :hints (("Goal" :use ((:instance fn-hrs-need-ok-at (salt (fn-hrc-salt (cdr st))) (n (fn-hrc-nimg (cdr st)))
                                   (lens (fn-hrc-lens (cdr st))) (starts (fn-hrc-starts (cdr st)))
                                   (pgs-mem (fn-hrc-pgs (cdr st)))))
           :in-theory (disable fn-hrs-need-ok-at fn-hp-x-at))))


; -----------------------------------------------------------------------------
; J. The fill's frame: page P's flag only (to verified, or not at all), the
; table and every other page's flag unchanged.

(defthm fn-hrs-put-frame
  (and (equal (pgs-v-length (fn-hrs-put j ws pgs-mem)) (pgs-v-length pgs-mem))
       (equal (pgs-tv-length (fn-hrs-put j ws pgs-mem)) (pgs-tv-length pgs-mem))
       (equal (pgs-vi q (fn-hrs-put j ws pgs-mem)) (pgs-vi q pgs-mem))
       (equal (pgs-tvi q (fn-hrs-put j ws pgs-mem)) (pgs-tvi q pgs-mem))
       (equal (nth *pgs-ti* (fn-hrs-put j ws pgs-mem)) (nth *pgs-ti* pgs-mem)))
  :hints (("Goal" :induct (fn-hrs-put j ws pgs-mem)
           :in-theory (enable pgs-v-length pgs-tv-length pgs-vi pgs-tvi update-pgs-wi))))

(defthm fn-hrs-entry-of-ti
  (implies (equal (nth *pgs-ti* m2) (nth *pgs-ti* m))
           (equal (pgs-x-get-entry 2 b q m2) (pgs-x-get-entry 2 b q m)))
  :hints (("Goal" :in-theory (enable pgs-x-get-entry pgs-x-word pgs-x-len pgs-x-dig4 pgs-ti pgs-t-length)))
  :rule-classes nil)

(defthm fn-hrs-vi-of-update-vi
  (and (equal (pgs-vi q (update-pgs-vi p x m)) (if (equal (nfix q) (nfix p)) x (pgs-vi q m)))
       (implies (< (nfix p) (pgs-v-length m)) (equal (pgs-v-length (update-pgs-vi p x m)) (pgs-v-length m)))
       (equal (pgs-tv-length (update-pgs-vi p x m)) (pgs-tv-length m))
       (equal (nth *pgs-ti* (update-pgs-vi p x m)) (nth *pgs-ti* m)))
  :hints (("Goal" :in-theory (enable pgs-vi pgs-v-length pgs-tv-length update-pgs-vi))))

(defthm fn-hrs-fill-pgs-frame
  (implies (natp p)
           (let ((m2 (mv-nth 1 (fn-hrs-fill-pgs p words txid pgs-mem fn-octets-pg))))
             (and (equal (pgs-v-length m2) (pgs-v-length pgs-mem))
                  (equal (nth *pgs-ti* m2) (nth *pgs-ti* pgs-mem))
                  (implies (not (equal (nfix q) p)) (equal (pgs-vi q m2) (pgs-vi q pgs-mem)))
                  (implies (not (equal (pgs-vi p m2) (pgs-vi p pgs-mem))) (equal (pgs-vi p m2) 2))
                  (implies (and (equal (mv-nth 0 (fn-hrs-fill-pgs p words txid pgs-mem fn-octets-pg)) :ok)
                                (< p (pgs-v-length pgs-mem)))
                           (equal (pgs-vi p m2) 2)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-hrs-put pgs-x-page-digest pgs-x-get-entry pgs-vi pgs-v-length pgs-tv-length pgs-tvi)
           :expand ((pgs-x-open-page p txid :eager (fn-hrs-put (* 2048 p) words pgs-mem) fn-octets-pg)))))


; -----------------------------------------------------------------------------
; K. The one retry loop.
;
; A read that answers (:need-page P PHYS) is served by one fill of page P:
; its words come from the page file through the host's byte primitive,
; `fn-pgs-fill-realize' (A-PGS-HOST-IO, books/assumptions.lisp: it answers
; the words the page file holds at the address), at the address the
; table names for P (`fn-hrecs-phys'), then the read is asked again.  The
; fill keeps the history's faithfulness when the page file holds the
; image's page at that address for every page the image has not verified:
; `fn-hrecs-disk-faithful', the relation between the page file and the
; history that the open establishes (the committed record's pages are the
; image's; milestone (c)) and that no fill changes.

(defun-nx fn-hrs-disk-ok (file p n st)
  (declare (xargs :measure (nfix (- (nfix n) (nfix p)))
                  :hints (("Goal" :in-theory (disable fn-hrecs-page-open fn-hrecs-image-page pgs-x-get-entry)))))
  (if (zp (- (nfix n) (nfix p)))
      t
    (and (implies (fn-hrecs-page-open (nfix p) st)
                  (equal (fn-pgs-page-words file (first (pgs-x-get-entry 2 0 (nfix p) (fn-hrc-pgs (cdr st)))))
                         (fn-hrecs-image-page (nfix p) st)))
         (fn-hrs-disk-ok file (+ 1 (nfix p)) n st))))

(defun-nx fn-hrecs-disk-faithful (file st)
  (implies (fn-hrecs-has-image st)
           (fn-hrs-disk-ok file 0 (pgs-v-length (fn-hrc-pgs (cdr st))) st)))

(defthm fn-hrs-disk-ok-page
  (implies (and (fn-hrs-disk-ok file p n st) (natp p) (natp q) (<= p q) (< q (nfix n)) (fn-hrecs-page-open q st))
           (equal (fn-pgs-page-words file (first (pgs-x-get-entry 2 0 q (fn-hrc-pgs (cdr st)))))
                  (fn-hrecs-image-page q st)))
  :hints (("Goal" :induct (fn-hrs-disk-ok file p n st) :in-theory (disable fn-hrecs-page-open fn-hrecs-image-page))))

(defun fn-hrecs-serve (p file fn-hrecs)
  ; One fill: page P from the page FILE at the address its table entry
  ; names, then the page store's check.  (mv VERDICT fn-hrecs).
  ; In the logic the list form; what runs is the frame fill (the words put
  ; in place by the host), the same term by fn-hrecs-frame-fill's definition.
  (declare (xargs :stobjs fn-hrecs :guard (natp p)
                  :guard-hints (("Goal" :in-theory (enable fn-hrecs-frame-fill fn-hrs$a-frame-fill fn-hrecs-fill)))))
  (mbe :logic (let ((words (fn-pgs-fill-realize file (fn-hrecs-phys p fn-hrecs))))
                (fn-hrecs-fill p words fn-hrecs))
       :exec (fn-hrecs-frame-fill file (fn-hrecs-phys p fn-hrecs) p fn-hrecs)))


(defthm fn-hrs-fill-st-pgs
  (equal (fn-hrc-pgs (cdr (mv-nth 1 (fn-hrecs-fill p words st))))
         (mv-nth 1 (fn-hrs-fill-pgs p words (fn-hrc-txid (cdr st)) (fn-hrc-pgs (cdr st)) (fn-hrc-oct (cdr st)))))
  :hints (("Goal" :in-theory (disable fn-hrs-fill-pgs))))

(defthm fn-hrs-fill-st-fields
  (let ((c2 (cdr (mv-nth 1 (fn-hrecs-fill p words st)))))
    (and (equal (car (mv-nth 1 (fn-hrecs-fill p words st))) (car st))
         (equal (fn-hrc-img c2) (fn-hrc-img (cdr st)))
         (equal (fn-hrc-nimg c2) (fn-hrc-nimg (cdr st)))
         (equal (fn-hrc-salt c2) (fn-hrc-salt (cdr st)))
         (equal (fn-hrc-starts c2) (fn-hrc-starts (cdr st)))
         (equal (fn-hrc-npages c2) (fn-hrc-npages (cdr st)))))
  :hints (("Goal" :in-theory (disable fn-hrs-fill-pgs))))

(defthm fn-hrs-image-page-after-fill
  (equal (fn-hrecs-image-page q (mv-nth 1 (fn-hrecs-fill p words st))) (fn-hrecs-image-page q st))
  :hints (("Goal" :in-theory (disable fn-hrecs-fill take nthcdr fn-hp-piw))))

(defthm fn-hrs-entry-after-fill
  (implies (natp p)
           (equal (pgs-x-get-entry 2 0 q (fn-hrc-pgs (cdr (mv-nth 1 (fn-hrecs-fill p words st)))))
                  (pgs-x-get-entry 2 0 q (fn-hrc-pgs (cdr st)))))
  :hints (("Goal" :use ((:instance fn-hrs-entry-of-ti (b 0)
                                   (m2 (mv-nth 1 (fn-hrs-fill-pgs p words (fn-hrc-txid (cdr st)) (fn-hrc-pgs (cdr st)) (fn-hrc-oct (cdr st)))))
                                   (m (fn-hrc-pgs (cdr st)))))
           :in-theory (disable fn-hrecs-fill fn-hrs-fill-pgs pgs-x-get-entry))))

(defthm fn-hrs-open-after-fill
  (implies (and (natp p) (natp q))
           (equal (fn-hrecs-page-open q (mv-nth 1 (fn-hrecs-fill p words st)))
                  (and (fn-hrecs-page-open q st)
                       (not (equal (pgs-vi q (fn-hrc-pgs (cdr (mv-nth 1 (fn-hrecs-fill p words st))))) 2)))))
  :hints (("Goal" :cases ((equal q p))
           :use ((:instance fn-hrs-fill-pgs-frame (txid (fn-hrc-txid (cdr st))) (pgs-mem (fn-hrc-pgs (cdr st)))
                            (fn-octets-pg (fn-hrc-oct (cdr st)))))
           :in-theory (disable fn-hrecs-fill fn-hrs-fill-pgs fn-hrs-fill-pgs-frame pgs-vi))))


(defthm fn-hrs-disk-ok-after-fill
  (implies (and (fn-hrs-disk-ok file q n st) (natp p))
           (fn-hrs-disk-ok file q n (mv-nth 1 (fn-hrecs-fill p words st))))
  :hints (("Goal" :induct (fn-hrs-disk-ok file q n st)
           :in-theory (union-theories '(fn-hrs-disk-ok fn-hrs-open-after-fill fn-hrs-image-page-after-fill fn-hrs-entry-after-fill
                                         nfix natp (:t nfix) zp (:e zp) (:e natp) not)
                                      (theory 'minimal-theory)))))

(defthm fn-hrs-vlen-after-fill
  (implies (natp p)
           (equal (pgs-v-length (fn-hrc-pgs (cdr (mv-nth 1 (fn-hrecs-fill p words st)))))
                  (pgs-v-length (fn-hrc-pgs (cdr st)))))
  :hints (("Goal" :use ((:instance fn-hrs-fill-pgs-frame (txid (fn-hrc-txid (cdr st))) (pgs-mem (fn-hrc-pgs (cdr st)))
                                   (fn-octets-pg (fn-hrc-oct (cdr st))) (q 0)))
           :in-theory (disable fn-hrecs-fill fn-hrs-fill-pgs fn-hrs-fill-pgs-frame))))

(defthm fn-hrecs-p-of-exports
  (implies (fn-hrecs-p st)
           (and (implies (natp p) (fn-hrecs-p (mv-nth 1 (fn-hrecs-fill p words st))))
                (fn-hrecs-p (fn-hrecs-append ev st))
                (fn-hrecs-p (mv-nth 1 (fn-hrecs-flush st)))
                (implies (and (true-listp events) (natp salt)) (fn-hrecs-p (fn-hrecs-load events salt st)))))
  :hints (("Goal" :use ((:instance fn-hrecs-fill{preserved} (fn-hrecs st))
                        (:instance fn-hrecs-append{preserved} (fn-hrecs st))
                        (:instance fn-hrecs-flush{preserved} (fn-hrecs st))
                        (:instance fn-hrecs-load{preserved} (fn-hrecs st)))
           :in-theory (disable fn-hrs$ap fn-hrs$a-fill fn-hrs$a-append fn-hrs$a-flush fn-hrs$a-load))))

; KEYSTONE (the fill the loop makes): over a page file that holds the
; image's pages the history has not verified, one fill keeps the history,
; its faithfulness and the page file's relation to it -- whatever it
; answers.  A-PGS-HOST-IO is used here and nowhere else.
(defthm fn-hrecs-serve-keeps
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st) (fn-hrecs-disk-faithful file st) (natp p))
           (let ((st2 (mv-nth 1 (fn-hrecs-serve p file st))))
             (and (fn-hrecs-p st2)
                  (equal (fn-hrecs-list st2) (fn-hrecs-list st))
                  (fn-hrecs-faithful st2)
                  (fn-hrecs-disk-faithful file st2))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrecs-fill-keeps (words (fn-pgs-fill-realize file (fn-hrecs-phys p st))))
                 (:instance fn-hrs-disk-ok-page (p 0) (q p) (n (pgs-v-length (fn-hrc-pgs (cdr st)))))
                 (:instance fn-hrs-disk-ok-after-fill (q 0) (n (pgs-v-length (fn-hrc-pgs (cdr st))))
                            (words (fn-pgs-fill-realize file (fn-hrecs-phys p st)))))
           :in-theory (e/d (fn-hrecs-has-image)
                           (fn-hrecs-fill-keeps fn-hrs-disk-ok-page fn-hrs-disk-ok-after-fill fn-hrecs-fill
                            fn-hrecs-faithful fn-hrecs-list fn-hrecs-image-page fn-hrs-disk-ok pgs-x-get-entry
                            fn-hrecs-p fn-hrs$a-fill fn-hrc-fill fn-hrs-fill-pgs fn-hrc-wfp fn-hrc-fill-shape
                            fn-hrs-fill-st-pgs)))))


(defun fn-hrecs-get (seq file fuel fn-hrecs)
  ; Record SEQ as the host calls it: (mv VERDICT RESULT fn-hrecs).  Ask the
  ; read; serve each (:need-page P ...) by one fill and ask again.  VERDICT
  ; :ok and RESULT the read's answer; otherwise VERDICT is what stopped it:
  ; a fill the page store refused (a recovery event), a need the loop does
  ; not serve ((:need-table T PHYS) or :out-of-range: the open loads every
  ; table, section L), or (:refused :fuel).  FUEL: the nested store's page
  ; count plus one suffices (`fn-hrecs-get-fuel-enough').  Work: one read
  ; per fill, at most one fill per page the record touches.
  (declare (xargs :stobjs fn-hrecs :guard (and (natp seq) (natp fuel)) :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-hrecs-at fn-hrecs-serve fn-hrecs-p)))
                  :guard-hints (("Goal" :in-theory (disable fn-hrecs-at fn-hrecs-serve)))))
  (mv-let (v r) (fn-hrecs-at seq fn-hrecs)
    (cond ((eq v :ok) (mv :ok r fn-hrecs))
          ((not (and (consp v) (eq (car v) :need-page) (consp (cdr v)) (natp (cadr v)))) (mv v nil fn-hrecs))
          ((zp fuel) (mv (list :refused :fuel) nil fn-hrecs))
          (t (mv-let (fv fn-hrecs) (fn-hrecs-serve (cadr v) file fn-hrecs)
               (if (eq fv :ok)
                   (fn-hrecs-get seq file (1- fuel) fn-hrecs)
                 (mv fv nil fn-hrecs)))))))

; KEYSTONE (the loop): over a page file that holds the image's unverified
; pages, the loop keeps the history, its faithfulness and the page file's
; relation, and an :ok answer is the history's record SEQ (or (:refused
; :seq) past its end).
(defthm fn-hrecs-get-is-nth
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st) (fn-hrecs-disk-faithful file st) (natp seq))
           (let* ((res (fn-hrecs-get seq file fuel st)) (st2 (mv-nth 2 res)) (h (fn-hrecs-list st)))
             (and (fn-hrecs-p st2)
                  (equal (fn-hrecs-list st2) h)
                  (fn-hrecs-faithful st2)
                  (fn-hrecs-disk-faithful file st2)
                  (implies (equal (mv-nth 0 res) :ok)
                           (equal (mv-nth 1 res) (if (< seq (len h)) (list :ok (nth seq h)) (list :refused :seq)))))))
  :hints (("Goal" :induct (fn-hrecs-get seq file fuel st)
           :in-theory (disable fn-hrecs-serve fn-hrecs-at fn-hrecs-faithful fn-hrecs-disk-faithful fn-hrecs-list fn-hrecs-p))
          ("Subgoal *1/2" :use ((:instance fn-hrecs-serve-keeps (p (cadr (mv-nth 0 (fn-hrecs-at seq st)))))
                                (:instance fn-hrecs-at-is-nth)))
          ("Subgoal *1/1" :use ((:instance fn-hrecs-at-is-nth)))))


; Progress: each fill the loop makes verifies a page that was open, so the
; loop never runs out of fuel when the fuel covers the open pages.

(defun-nx fn-hrs-open-count (q n st)
  (declare (xargs :measure (nfix (- (nfix n) (nfix q)))))
  (if (zp (- (nfix n) (nfix q)))
      0
    (+ (if (fn-hrecs-page-open (nfix q) st) 1 0) (fn-hrs-open-count (+ 1 (nfix q)) n st))))

(defthm fn-hrs-open-count-pos
  (implies (and (fn-hrecs-page-open p st) (natp p) (natp q) (<= q p) (< p (nfix n)))
           (< 0 (fn-hrs-open-count q n st)))
  :hints (("Goal" :induct (fn-hrs-open-count q n st) :in-theory (disable fn-hrecs-page-open)))
  :rule-classes :linear)

(defthm fn-hrs-serve-ok-verifies
  (implies (and (natp p) (fn-hrecs-page-open p st) (equal (mv-nth 0 (fn-hrecs-serve p file st)) :ok))
           (not (fn-hrecs-page-open p (mv-nth 1 (fn-hrecs-serve p file st)))))
  :hints (("Goal" :use ((:instance fn-hrs-fill-pgs-frame (words (fn-pgs-fill-realize file (fn-hrecs-phys p st)))
                                   (txid (fn-hrc-txid (cdr st))) (pgs-mem (fn-hrc-pgs (cdr st)))
                                   (fn-octets-pg (fn-hrc-oct (cdr st))) (q p)))
           :in-theory (disable fn-hrs-fill-pgs fn-hrs-fill-pgs-frame pgs-vi pgs-v-length))))

(defthm fn-hrs-open-other-after-fill
  (implies (and (natp p) (natp q) (not (equal q p)))
           (equal (fn-hrecs-page-open q (mv-nth 1 (fn-hrecs-fill p words st))) (fn-hrecs-page-open q st)))
  :hints (("Goal" :use ((:instance fn-hrs-fill-pgs-frame (txid (fn-hrc-txid (cdr st))) (pgs-mem (fn-hrc-pgs (cdr st)))
                                   (fn-octets-pg (fn-hrc-oct (cdr st)))))
           :in-theory (e/d (fn-hrecs-page-open) (fn-hrs-fill-pgs fn-hrs-fill-pgs-frame pgs-vi pgs-v-length fn-hrecs-fill
                                                 fn-hrs-open-after-fill)))))

(defthm fn-hrs-open-count-above-fill
  (implies (and (natp p) (natp q) (< p q))
           (equal (fn-hrs-open-count q n (mv-nth 1 (fn-hrecs-fill p words st))) (fn-hrs-open-count q n st)))
  :hints (("Goal" :induct (fn-hrs-open-count q n st)
           :in-theory (disable fn-hrecs-page-open fn-hrecs-fill fn-hrs-open-after-fill))))

(defthm fn-hrs-open-count-after-serve
  (implies (and (natp p) (fn-hrecs-page-open p st) (equal (mv-nth 0 (fn-hrecs-serve p file st)) :ok)
                (natp q) (<= q p) (< p (nfix n)))
           (equal (fn-hrs-open-count q n (mv-nth 1 (fn-hrecs-serve p file st)))
                  (+ -1 (fn-hrs-open-count q n st))))
  :hints (("Goal" :induct (fn-hrs-open-count q n st)
           :in-theory (disable fn-hrecs-page-open fn-hrecs-fill fn-hrs-open-after-fill fn-hrs-serve-ok-verifies))
          ("Subgoal *1/2" :cases ((equal q p))
           :use ((:instance fn-hrs-serve-ok-verifies)
                 (:instance fn-hrs-open-count-above-fill (q (+ 1 p)) (words (fn-pgs-fill-realize file (fn-hrecs-phys p st))))))))


(defthm fn-hrs-vlen-after-serve
  (implies (natp p)
           (equal (pgs-v-length (fn-hrc-pgs (cdr (mv-nth 1 (fn-hrecs-serve p file st)))))
                  (pgs-v-length (fn-hrc-pgs (cdr st)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hrecs-serve fn-hrs-vlen-after-fill) (theory 'minimal-theory)))))

(defthm fn-hrs-get-need-count
  (implies (and (fn-hrecs-p st) (natp seq)
                (consp (car (fn-hrecs-at seq st))) (equal (car (car (fn-hrecs-at seq st))) :need-page))
           (< 0 (fn-hrs-open-count 0 (pgs-v-length (fn-hrc-pgs (cdr st))) st)))
  :hints (("Goal" :use ((:instance fn-hrecs-at-need-page)
                        (:instance fn-hrs-open-count-pos (p (cadr (car (fn-hrecs-at seq st)))) (q 0)
                                   (n (pgs-v-length (fn-hrc-pgs (cdr st))))))
           :in-theory (e/d (fn-hrecs-page-open) (fn-hrecs-at-need-page fn-hrs-open-count-pos fn-hrecs-at fn-hrs-open-count))))
  :rule-classes :linear)

(defthm fn-hrs-get-step-count
  (implies (and (fn-hrecs-p st) (natp seq)
                (consp (car (fn-hrecs-at seq st))) (equal (car (car (fn-hrecs-at seq st))) :need-page)
                (natp (cadr (car (fn-hrecs-at seq st))))
                (equal (car (fn-hrecs-serve (cadr (car (fn-hrecs-at seq st))) file st)) :ok))
           (equal (fn-hrs-open-count 0 (pgs-v-length (fn-hrc-pgs (cdr st)))
                                     (mv-nth 1 (fn-hrecs-serve (cadr (car (fn-hrecs-at seq st))) file st)))
                  (+ -1 (fn-hrs-open-count 0 (pgs-v-length (fn-hrc-pgs (cdr st))) st))))
  :hints (("Goal" :use ((:instance fn-hrecs-at-need-page)
                        (:instance fn-hrs-open-count-after-serve (p (cadr (car (fn-hrecs-at seq st)))) (q 0)
                                   (n (pgs-v-length (fn-hrc-pgs (cdr st)))))
                        (:instance fn-hrs-vlen-after-serve (p (cadr (car (fn-hrecs-at seq st))))))
           :in-theory (union-theories '(fn-hrecs-page-open natp nfix (:e natp) mv-nth zp (:e zp) (:t pgs-v-length)) (theory 'minimal-theory)))))

(defthm fn-hrs-serve-not-fuel
  (not (equal (car (fn-hrecs-serve p file st)) '(:refused :fuel)))
  :hints (("Goal" :in-theory (disable fn-hrs-put pgs-x-page-digest pgs-x-get-entry))))

(defthm fn-hrs-at-not-fuel
  (not (equal (car (fn-hrecs-at seq st)) '(:refused :fuel)))
  :hints (("Goal" :use ((:instance fn-hp-x-at-verdict (salt (fn-hrc-salt (cdr st))) (n (fn-hrc-nimg (cdr st)))
                                   (lens (fn-hrc-lens (cdr st))) (starts (fn-hrc-starts (cdr st)))
                                   (pgs-mem (fn-hrc-pgs (cdr st)))))
           :in-theory (disable fn-hp-x-at-verdict fn-hp-x-at))))

; PROGRESS: with fuel covering the pages not yet verified, the loop never
; stops for fuel: it answers :ok, or what the page store refused, or a
; need it does not serve.
(defthm fn-hrecs-get-fuel-enough
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st) (fn-hrecs-disk-faithful file st) (natp seq)
                (<= (fn-hrs-open-count 0 (pgs-v-length (fn-hrc-pgs (cdr st))) st) (nfix fuel)))
           (not (equal (mv-nth 0 (fn-hrecs-get seq file fuel st)) (list :refused :fuel))))
  :hints (("Goal" :induct (fn-hrecs-get seq file fuel st)
           :in-theory (disable fn-hrecs-serve fn-hrecs-at fn-hrecs-faithful fn-hrecs-disk-faithful fn-hrecs-p
                               fn-hrecs-page-open fn-hrs-open-count))))


(defthm fn-hrs-open-count-bound
  (<= (fn-hrs-open-count q n st) (nfix (- (nfix n) (nfix q))))
  :hints (("Goal" :induct (fn-hrs-open-count q n st) :in-theory (disable fn-hrecs-page-open)))
  :rule-classes :linear)

(defun fn-hrecs-read (seq file fn-hrecs)
  ; Record SEQ, the one read the host and the store's readers call:
  ; `fn-hrecs-get' with fuel the nested store's page count.
  (declare (xargs :stobjs fn-hrecs :guard (natp seq)))
  (fn-hrecs-get seq file (fn-hrecs-vlen fn-hrecs) fn-hrecs))

; KEYSTONE (the read the host calls): over a page file that holds the
; image's unverified pages, it keeps the history, its faithfulness and the
; page file's relation; an :ok answer is record SEQ of the history (or
; (:refused :seq) past its end); it never stops for fuel.
(defthm fn-hrecs-read-is-nth
  (implies (and (fn-hrecs-p st) (fn-hrecs-faithful st) (fn-hrecs-disk-faithful file st) (natp seq))
           (let* ((res (fn-hrecs-read seq file st)) (st2 (mv-nth 2 res)) (h (fn-hrecs-list st)))
             (and (fn-hrecs-p st2)
                  (equal (fn-hrecs-list st2) h)
                  (fn-hrecs-faithful st2)
                  (fn-hrecs-disk-faithful file st2)
                  (implies (equal (mv-nth 0 res) :ok)
                           (equal (mv-nth 1 res) (if (< seq (len h)) (list :ok (nth seq h)) (list :refused :seq))))
                  (not (equal (mv-nth 0 res) (list :refused :fuel))))))
  :hints (("Goal" :use ((:instance fn-hrecs-get-is-nth (fuel (fn-hrecs-vlen st)))
                        (:instance fn-hrecs-get-fuel-enough (fuel (fn-hrecs-vlen st)))
                        (:instance fn-hrs-open-count-bound (q 0) (n (pgs-v-length (fn-hrc-pgs (cdr st))))))
           :in-theory (disable fn-hrecs-get-is-nth fn-hrecs-get-fuel-enough fn-hrs-open-count-bound fn-hrecs-get
                               fn-hrecs-p fn-hrecs-faithful fn-hrecs-disk-faithful fn-hrecs-list fn-hrs-open-count))))
