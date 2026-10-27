; Semantic retained-copy agreement follows actual append and recycle effects.
(in-package "ACL2")
(include-book "lb-log-payload-agreement")

(defthm fn-lb-log-entries-payload-agreep-of-append
 (equal (fn-lb-log-entries-payload-agreep sequence handle payload (append a b))
        (and (fn-lb-log-entries-payload-agreep sequence handle payload a)
             (fn-lb-log-entries-payload-agreep sequence handle payload b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero)
  '(len fn-lb-log-entries-payload-agreep binary-append)))))

(defthm fn-lb-log-entries-payload-agreep-gives-lookup-payload
 (implies (and (fn-lb-log-entries-payload-agreep sequence handle payload entries)
               (fn-lb-log-model-row-entry-in sequence handle entries))
  (equal (nth 6 (fn-lb-log-model-row-entry-in sequence handle entries)) payload))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-entries-payload-agreep fn-lb-log-model-row-entry-in)))))

(defthm fn-lb-log-row-copies-agreep-gives-lookup-payload
 (implies (and (fn-lb-log-row-copies-agreep row payload log)
               (fn-lb-log-model-row-entry row log))
  (equal (fn-lb-log-payload row log) payload))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry row log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-row-copies-agreep fn-lb-log-model-row-entry fn-lb-log-payload
     fn-lb-log-entries-payload-agreep-gives-lookup-payload)))))

(defthm fn-lb-log-row-copies-agreep-of-recycle
 (implies (fn-lb-log-row-copies-agreep row payload log)
  (fn-lb-log-row-copies-agreep row payload (fn-lb-log-model-recycle target log)))
 :hints (("Goal" :induct (fn-lb-log-model-recycle target log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-row-copies-agreep fn-lb-log-model-recycle)))))

(defthm fn-lb-log-payload-after-recycle-from-agreement
 (implies (and (fn-lb-log-row-copies-agreep row (fn-lb-log-payload row log) log)
               (fn-lb-log-model-row-entry row (fn-lb-log-model-recycle target log)))
  (equal (fn-lb-log-payload row (fn-lb-log-model-recycle target log))
         (fn-lb-log-payload row log)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-log-row-copies-agreep-of-recycle (payload (fn-lb-log-payload row log)))
        (:instance fn-lb-log-row-copies-agreep-gives-lookup-payload
         (payload (fn-lb-log-payload row log)) (log (fn-lb-log-model-recycle target log))))
  :in-theory (theory 'ground-zero))))

(local (defthm fn-lbpa-entries-of-appended-segment
 (equal (fn-lb-log-entries-payload-agreep sequence handle expected
          (caddr (fn-lb-log-model-append-to-segment row payload segment)))
  (and (fn-lb-log-entries-payload-agreep sequence handle expected (caddr segment))
       (implies (and (equal sequence (fn-record-sequence row))
                     (equal handle (fn-record-payload row)))
                (equal payload expected))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-append-to-segment fn-lb-log-entries-payload-agreep-of-append
     fn-lb-log-entries-payload-agreep nth))))))

(defthm fn-lb-log-row-copies-agreep-of-append
 (equal (fn-lb-log-row-copies-agreep old expected
          (fn-lb-log-model-append row payload target log))
  (and (fn-lb-log-row-copies-agreep old expected log)
       (implies (and (equal (fn-record-sequence old) (fn-record-sequence row))
                     (equal (fn-record-payload old) (fn-record-payload row)))
                (equal payload expected))))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-append fn-lb-log-row-copies-agreep
     fn-lbpa-entries-of-appended-segment fn-lb-log-entries-payload-agreep)))))

(defthm fn-lb-log-entries-agree-when-key-absent
 (implies (and (natp handle)
               (not (fn-lb-log-model-row-entry-in sequence handle entries)))
  (fn-lb-log-entries-payload-agreep sequence handle payload entries))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry-in fn-lb-log-entries-payload-agreep natp nth)))))

(defthm fn-lb-log-copies-agree-when-key-absent
 (implies (and (natp (fn-record-payload row))
               (not (fn-lb-log-model-row-entry row log)))
  (fn-lb-log-row-copies-agreep row payload log))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry row log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry fn-lb-log-row-copies-agreep
     fn-lb-log-entries-agree-when-key-absent)))))

(defthm fn-lb-log-row-copies-agree-of-fresh-append
 (implies (and (natp (fn-record-payload row))
               (not (fn-lb-log-model-row-entry row log)))
  (fn-lb-log-row-copies-agreep row payload (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-log-row-copies-agreep-of-append fn-lb-log-copies-agree-when-key-absent)))))

(defthm fn-lb-log-row-copies-agree-of-distinct-append
 (implies (and (fn-lb-log-row-copies-agreep old expected log)
               (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
                   (not (equal (fn-record-payload old) (fn-record-payload row)))))
  (fn-lb-log-row-copies-agreep old expected (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-log-row-copies-agreep-of-append)))))

(local (defthm fn-lbpa-row-entry-key-congruence
 (implies (and (equal (fn-record-sequence old) (fn-record-sequence row))
               (equal (fn-record-payload old) (fn-record-payload row)))
  (equal (fn-lb-log-model-row-entry old log) (fn-lb-log-model-row-entry row log)))
 :hints (("Goal" :induct (len log) :in-theory (union-theories (theory 'ground-zero)
  '(len fn-lb-log-model-row-entry))))))

(defthm fn-lb-log-row-copies-agree-of-fresh-append-old
 (implies (and (fn-lb-log-row-copies-agreep old expected log)
               (fn-lb-log-model-row-entry old log)
               (not (fn-lb-log-model-row-entry row log)))
  (fn-lb-log-row-copies-agreep old expected (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbpa-row-entry-key-congruence)
        (:instance fn-lb-log-row-copies-agreep-of-append))
  :in-theory (theory 'ground-zero))))
