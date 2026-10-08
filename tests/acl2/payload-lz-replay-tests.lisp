; Event-fold teeth for PRF-326.  The LZ fold accepts plain placed records
; too: this fixture exercises its fallback through the verified plain
; extent branch.  It does not assert compression or physical disk contents.
(in-package "ACL2")
(include-book "../../books/payload-lz-replay")
(include-book "payload-extent-tests")

(defthm plrt-uses-plain-extent
  (not (fn-lzr-extent-of 3 *pxt-teeth-position* (pxt-teeth-r)
                         (fn-durable-octets 3 42 1) nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lzr-extent-of) (fn-lzr-parse)))))

(defconst *plrt-events-claim*
  '(((faithful (fn-arx-faithful-p zs ps)))
    (equal (fn-lzr-intern-events ws zs ps dicts keyring generation arena-value)
           (fn-intern-events ws keyring generation arena-value))))

(teeth-ground-lemma plrt-events-positive *plrt-events-claim*
  ((ws (list (pxt-teeth-w))) (zs (list (pxt-teeth-r)))
   (ps (list (cons 3 *pxt-teeth-position*)))
   (dicts nil) (keyring nil) (generation 0) (arena-value nil))
  :hints (("Goal" :in-theory (disable fn-lzr-intern-events fn-intern-events))))

(teeth-ground-lemma plrt-events-dropped-row *plrt-events-claim*
  ((ws (list (pxt-teeth-w))) (zs (list (pxt-teeth-r)))
   (ps (list (cons 3 *pxt-teeth-position*)))
   (dicts nil) (keyring nil) (generation 0) (arena-value nil))
  :mutation (:conclusion
             (equal (mv-nth 0 (fn-lzr-intern-events ws zs ps dicts keyring generation arena-value)) nil))
  :hints (("Goal" :use (pxt-teeth-placed
                       (:instance pxt-one-event-has-row (w (pxt-teeth-w)) (fn-arena nil)))
           :in-theory (disable fn-lzr-intern-events fn-intern-events fn-record-p
                               fn-arx-extent-of))))

(defteeth fn-lzr-intern-events-refines
  :claim (((faithful (fn-arx-faithful-p zs ps)))
          (equal (fn-lzr-intern-events ws zs ps dicts keyring generation arena-value)
                 (fn-intern-events ws keyring generation arena-value)))
  :subject fn-lzr-intern-events
  :witness ((ws (list (pxt-teeth-w))) (zs (list (pxt-teeth-r)))
            (ps (list (cons 3 *pxt-teeth-position*)))
            (dicts nil) (keyring nil) (generation 0) (arena-value nil))
  :witness-lemma plrt-events-positive
  :breaks ((faithful (:assumption fn-durable-octets)))
  :mutations ((dropped-row
               (:conclusion
                (equal (mv-nth 0 (fn-lzr-intern-events ws zs ps dicts keyring generation arena-value)) nil))
               ((ws (list (pxt-teeth-w))) (zs (list (pxt-teeth-r)))
                (ps (list (cons 3 *pxt-teeth-position*)))
                (dicts nil) (keyring nil) (generation 0) (arena-value nil))
               :fault "the LZ replay fold seals the payload but drops the returned row"
               :lemma plrt-events-dropped-row)))
