; Appending actual octets preserves old committed ranges and verification.
(in-package "ACL2")
(include-book "log-verified-map")

(local (defthm fn-lba-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(len binary-append))))))

(local (defthm fn-lba-take-append-prefix
 (implies (and (natp n) (<= n (len bytes))) (equal (take n (append bytes tail)) (take n bytes)))
 :hints (("Goal" :induct (take n bytes) :in-theory (union-theories (theory 'ground-zero) '(take len natp zp binary-append))))))

(local (defthm fn-lba-nthcdr-append-prefix
 (implies (and (natp off) (<= off (len bytes)))
 (equal (nthcdr off (append bytes tail)) (append (nthcdr off bytes) tail)))
 :hints (("Goal" :induct (nthcdr off bytes) :in-theory (union-theories (theory 'ground-zero) '(nthcdr len natp zp binary-append))))))

(local (defthm fn-lba-len-nthcdr-bounded
 (implies (and (natp off) (<= off (len bytes))) (equal (len (nthcdr off bytes)) (- (len bytes) off)))
 :hints (("Goal" :induct (nthcdr off bytes) :in-theory (union-theories (theory 'ground-zero) '(nthcdr len natp zp))))))

(local (defthm fn-lba-range-slice-append-prefix
 (implies (and (natp off) (natp count) (<= (+ off count) (len bytes)))
 (equal (take count (nthcdr off (append bytes tail))) (take count (nthcdr off bytes))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lba-nthcdr-append-prefix)
       (:instance fn-lba-take-append-prefix (n count) (bytes (nthcdr off bytes)))
       (:instance fn-lba-len-nthcdr-bounded))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lba-atom-not-authenticated
 (implies (atom octets) (not (fn-arx-entry-ok octets elen)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-arx-entry-ok len nfix))))))

(local (defthm fn-lba-authenticated-range-entry-present
 (implies (fn-arx-entry-ok (fn-lb-entry-octets seg off log) (fn-lb-entry-protected-len seg off log))
 (and (fn-lb-log-model-range-entry off (caddr (fn-lb-log-model-segment seg log)))
      (not (equal (fn-lb-entry-octets seg off log) :bad))))
 :hints (("Goal" :do-not-induct t
 :cases ((fn-lb-log-model-range-entry off (caddr (fn-lb-log-model-segment seg log))))
 :use ((:instance fn-lba-atom-not-authenticated (octets nil) (elen (fn-lb-entry-protected-len seg off log)))
       (:instance fn-lba-atom-not-authenticated (octets :bad) (elen (fn-lb-entry-protected-len seg off log))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-entry-octets))))))

(local (defthm fn-lba-old-range-entry-survives
 (implies (fn-lb-log-model-range-entry off entries)
 (equal (fn-lb-log-model-range-entry off (append entries tail)) (fn-lb-log-model-range-entry off entries)))
 :hints (("Goal" :induct (fn-lb-log-model-range-entry off entries)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-range-entry binary-append))))))

(local (defthm fn-lba-old-range-domain-survives
 (implies (fn-lb-log-model-range-in-entries off count entries)
 (fn-lb-log-model-range-in-entries off count (append entries tail)))
 :hints (("Goal" :induct (fn-lb-log-model-range-in-entries off count entries)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-range-in-entries binary-append))))))

(local (defthm fn-lba-segment-append-preserves-id
 (equal (car (fn-lb-log-model-append-to-segment row payload segment)) (car segment))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment))))))

(local (defthm fn-lba-segment-append-length-increases
 (<= (len (cadr segment)) (len (cadr (fn-lb-log-model-append-to-segment row payload segment))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment fn-lba-len-append))))))

(local (defthm fn-lba-segment-append-preserves-old-slice
 (implies (and (natp off) (natp count) (<= (+ off count) (len (cadr segment))))
 (equal (take count (nthcdr off (cadr (fn-lb-log-model-append-to-segment row payload segment))))
        (take count (nthcdr off (cadr segment)))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment fn-lba-range-slice-append-prefix))))))

(local (defthm fn-lba-segment-append-preserves-old-directory
 (and (implies (fn-lb-log-model-range-entry off (caddr segment))
       (equal (fn-lb-log-model-range-entry off (caddr (fn-lb-log-model-append-to-segment row payload segment)))
              (fn-lb-log-model-range-entry off (caddr segment))))
      (implies (fn-lb-log-model-range-in-entries off count (caddr segment))
       (fn-lb-log-model-range-in-entries off count (caddr (fn-lb-log-model-append-to-segment row payload segment)))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment fn-lba-old-range-entry-survives fn-lba-old-range-domain-survives))))))

(local (defthm fn-lba-segment-append-is-consp
 (consp (fn-lb-log-model-append-to-segment row payload segment))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment))))))

(local (defthm fn-lba-existing-segment-id
 (implies (fn-lb-log-model-segment seg log) (equal (car (fn-lb-log-model-segment seg log)) seg))
 :hints (("Goal" :induct (fn-lb-log-model-segment seg log) :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-segment))))))

(local (defthm fn-lba-existing-segment-after-append
 (implies (fn-lb-log-model-segment seg log)
 (equal (fn-lb-log-model-segment seg (fn-lb-log-model-append row payload target log))
 (if (equal seg target) (fn-lb-log-model-append-to-segment row payload (fn-lb-log-model-segment seg log)) (fn-lb-log-model-segment seg log))))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append fn-lb-log-model-segment fn-lba-segment-append-preserves-id))))))

(local (defthm fn-lba-range-entry-nil
 (equal (fn-lb-log-model-range-entry off nil) nil)
 :hints (("Goal" :in-theory '(fn-lb-log-model-range-entry)))))

(local (defthm fn-lba-existing-range-entry-after-append
 (implies (fn-lb-log-model-range-entry off (caddr (fn-lb-log-model-segment seg log)))
 (equal (fn-lb-log-model-range-entry off (caddr (fn-lb-log-model-segment seg (fn-lb-log-model-append row payload target log))))
        (fn-lb-log-model-range-entry off (caddr (fn-lb-log-model-segment seg log)))))
 :hints (("Goal" :do-not-induct t :cases ((fn-lb-log-model-segment seg log) (equal seg target))
 :use ((:instance fn-lba-existing-segment-after-append)
       (:instance fn-lba-segment-append-preserves-old-directory (segment (fn-lb-log-model-segment seg log))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lba-range-entry-nil))))))

(local (defthm fn-lba-valid-read-facts
 (implies (not (equal (fn-lb-log-model-read-range seg off count log) :bad))
 (and (fn-lb-log-model-segment seg log) (natp off) (natp count)
      (<= (+ off count) (len (cadr (fn-lb-log-model-segment seg log))))
      (fn-lb-log-model-range-in-entries off count (caddr (fn-lb-log-model-segment seg log)))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-read-range))))))

(defthm fn-lb-log-append-preserves-existing-range
 (implies (not (equal (fn-lb-log-model-read-range seg off count log) :bad))
 (equal (fn-lb-log-model-read-range seg off count (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-read-range seg off count log)))
 :hints (("Goal" :do-not-induct t :cases ((equal seg target))
 :use ((:instance fn-lba-valid-read-facts)
       (:instance fn-lba-existing-segment-after-append)
       (:instance fn-lba-segment-append-is-consp (segment (fn-lb-log-model-segment seg log)))
       (:instance fn-lba-segment-append-length-increases (segment (fn-lb-log-model-segment seg log)))
       (:instance fn-lba-segment-append-preserves-old-directory (segment (fn-lb-log-model-segment seg log)))
       (:instance fn-lba-segment-append-preserves-old-slice (segment (fn-lb-log-model-segment seg log))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-read-range)))))

(local (defthm fn-lba-authenticated-entry-unchanged-by-append
 (implies (fn-arx-entry-ok (fn-lb-entry-octets seg off log) (fn-lb-entry-protected-len seg off log))
 (and (equal (fn-lb-entry-octets seg off (fn-lb-log-model-append row payload target log)) (fn-lb-entry-octets seg off log))
      (equal (fn-lb-entry-protected-len seg off (fn-lb-log-model-append row payload target log)) (fn-lb-entry-protected-len seg off log))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lba-authenticated-range-entry-present)
       (:instance fn-lba-existing-range-entry-after-append)
       (:instance fn-lb-log-append-preserves-existing-range
        (off (nth 1 (fn-lb-log-model-range-entry off (caddr (fn-lb-log-model-segment seg log)))))
        (count (+ (nfix (nth 2 (fn-lb-log-model-range-entry off (caddr (fn-lb-log-model-segment seg log))))) 32))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-entry-octets fn-lb-entry-protected-len))))))

(defthm fn-lb-log-append-preserves-verified-entry
 (implies (fn-arx-entry-ok (fn-lb-entry-octets seg off log) (fn-lb-entry-protected-len seg off log))
 (fn-arx-entry-ok (fn-lb-entry-octets seg off (fn-lb-log-model-append row payload target log))
                  (fn-lb-entry-protected-len seg off (fn-lb-log-model-append row payload target log))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lba-authenticated-entry-unchanged-by-append)) :in-theory (theory 'ground-zero))))

(local (defthm fn-lba-verified-entries-of-append
 (implies (fn-lb-verified-entries-invp bits log)
 (fn-lb-verified-entries-invp bits (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :induct (fn-lb-verified-entries-invp bits log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-verified-entries-invp fn-lb-log-append-preserves-verified-entry))))))

(defthm fn-lb-verified-invp-of-append
 (implies (fn-lb-verified-invp log fn-lb-vmap)
 (fn-lb-verified-invp (fn-lb-log-model-append row payload target log) fn-lb-vmap))
 :hints (("Goal" :use ((:instance fn-lba-verified-entries-of-append (bits (nth 0 fn-lb-vmap))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-verified-invp)))))
