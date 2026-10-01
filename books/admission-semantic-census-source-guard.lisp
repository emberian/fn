; The actual source constructor used by registered census BEGIN.
(in-package "ACL2")
(include-book "snapshot-source-cursor")
(defthm fn-owner-census-source-begin-establishes-scalar-guard
 (implies (natp count)
          (fn-osrc-guardp (fn-osrc-begin field count epoch lease)))
 :hints (("Goal" :in-theory (enable fn-osrc-guardp fn-osrc-begin fn-osrc-at))))
(defthm fn-owner-census-source-begin-retains-captured-source
 (and (equal (fn-osrc-at 1 (fn-osrc-begin field count epoch lease)) field)
      (equal (fn-osrc-at 9 (fn-osrc-begin field count epoch lease)) epoch)
      (equal (fn-osrc-at 10 (fn-osrc-begin field count epoch lease)) lease))
 :hints (("Goal" :in-theory (enable fn-osrc-begin fn-osrc-at))))
