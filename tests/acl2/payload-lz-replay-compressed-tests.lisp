; Event-fold teeth for PRF-326 through the COMPRESSED branch.
; tests/acl2/payload-lz-replay-tests.lisp exercises the fold with no
; dictionaries, so only the plain extent branch runs.  Here the record is the
; real 750-octet article, Z its frame sealed against the 2,749-octet
; dictionary (tests/acl2/payload-lz-record-tests.lisp), and DICTS holds that
; dictionary, so fn-lzr-extent-of answers an extent and fn-lzr-cat-intern-lz
; seals a compressed extent.
(in-package "ACL2")
(include-book "payload-lz-record-tests")
(include-book "teeth-ground-lemma")
(include-book "must-fail-checked")

; The place: Z at a one-record entry at 4096 of file 3.
(defconst *plc-ps* (list (cons 3 *plr-pos*)))

; The compressed branch is the one taken: the fixture has an extent, the same
; record with no dictionaries has none, and the event is the compressed seal.
(assert-event
 (and (fn-lzr-extentp *plr-e*)
      (equal (fn-lzr-extent-of 3 *plr-pos* *plr-z1* (fn-record-payload *plr-w*) *plr-dicts*) *plr-e*)))

(defthm plc-takes-the-compressed-branch
  (and (equal (fn-lzr-intern-event *plr-w* *plr-z1* (cdr (car *plc-ps*)) 3 *plr-dicts* nil 0 fn-arena)
              (fn-lzr-cat-intern-lz *plr-w* *plr-e* *plz-dict* nil 0 fn-arena))
       (null (fn-lzr-extent-of 3 *plr-pos* *plr-z1* (fn-record-payload *plr-w*) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lzr-intern-event)
                                  (fn-lzr-cat-intern-lz fn-lzr-extent-of fn-arx-intern-event
                                   fn-record-p fn-lzr-extentp)))))

; Positive witness of fn-lzr-intern-events-refines at the compressed frame:
; the faithful read (fn-durable-octets is the constrained file) is the
; hypothesis, the extent exists, and the fold equals the resident fold.
(defthm plc-events-witness
  (implies (fn-arx-faithful-p (list *plr-z1*) *plc-ps*)
           (and *plr-e*
                (equal (fn-lzr-intern-events (list *plr-w*) (list *plr-z1*) *plc-ps* *plr-dicts* nil 0 nil)
                       (fn-intern-events (list *plr-w*) nil 0 nil))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-lzr-intern-events-refines
                                   (ws (list *plr-w*)) (zs (list *plr-z1*)) (ps *plc-ps*)
                                   (dicts *plr-dicts*) (keyring nil) (generation 0) (arena-value nil)))
           :in-theory (disable fn-lzr-intern-events fn-intern-events
                               fn-lzr-intern-events-refines fn-arx-faithful-p))))

; Mutation: a fold that seals the compressed payload but drops the returned
; row is refuted (the resident fold returns the row).
(defthm plc-dropped-row-is-refuted
  (implies (fn-arx-faithful-p (list *plr-z1*) *plc-ps*)
           (not (equal (mv-nth 0 (fn-lzr-intern-events (list *plr-w*) (list *plr-z1*) *plc-ps*
                                                        *plr-dicts* nil 0 nil))
                       nil)))
  :rule-classes nil
  :hints (("Goal" :use (plc-events-witness)
           :in-theory (e/d (fn-intern-events fn-intern-event)
                           (fn-lzr-intern-events fn-arx-faithful-p fn-record-p
                            fn-lzr-cat-intern-lz)))))

; Hypothesis removal: without the faithful read the durable octets are
; unconstrained and the equation is not provable.
(must-fail-checked
 (defthm plc-events-no-faithful
   (equal (fn-lzr-intern-events (list *plr-w*) (list *plr-z1*) *plc-ps* *plr-dicts* nil 0 nil)
          (fn-intern-events (list *plr-w*) nil 0 nil))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-lzr-intern-events fn-intern-events)))))
