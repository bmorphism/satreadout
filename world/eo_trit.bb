#!/usr/bin/env bb
;; world://<OLC> EO change → ternary discrimination trits (the Earth "device").
;; Reads OlmoEarth embeddings in the zig-syrup binary format emitted by
;; sentinel2_olmoearth.py:  [u32 N][u16 D][f32 D*N][f64 lat,lon *N]  (LE)
;; Per-tile cosine change → saturating readout f_A → keep/maybe/discard trit.
;; This is the EO instance of the SatReadout readout: the scout's own
;; "worth keeping?" decision (earth_stack line 29) = GF(3) trit-0 maybe-band.
;; The stream of these trits calibrates Â in EO-embedding units (satfit).
(import [java.nio ByteBuffer ByteOrder] [java.nio.file Files Paths])

(defn read-bin [path]
  (let [bb (doto (ByteBuffer/wrap (Files/readAllBytes (Paths/get path (into-array String []))))
             (.order ByteOrder/LITTLE_ENDIAN))
        n (.getInt bb) d (bit-and (int (.getShort bb)) 0xffff)
        emb (vec (for [_ (range n)] (vec (repeatedly d #(.getFloat bb)))))
        coords (vec (for [_ (range n)] [(.getDouble bb) (.getDouble bb)]))]
    {:n n :d d :emb emb :coords coords}))

(defn write-bin [path n d emb coords]
  (let [cap (+ 4 2 (* 4 n d) (* 16 n))
        bb (doto (ByteBuffer/allocate cap) (.order ByteOrder/LITTLE_ENDIAN))]
    (.putInt bb n) (.putShort bb (short d))
    (doseq [v emb e v] (.putFloat bb (float e)))
    (doseq [c coords x c] (.putDouble bb (double x)))
    (Files/write (Paths/get path (into-array String [])) (.array bb)
                 (into-array java.nio.file.OpenOption []))))

(defn cosdist [a b]
  (let [dot (reduce + (map * a b))
        na (Math/sqrt (reduce + (map * a a))) nb (Math/sqrt (reduce + (map * b b)))]
    (- 1.0 (/ dot (+ (* na nb) 1e-12)))))

(def A 0.45)
(defn f [d] (* A (- 1.0 (Math/exp (/ (- d) A)))))
(defn logistic [x] (/ 1.0 (+ 1.0 (Math/exp (- x)))))
(def CUT {:a 0.10 :b 0.22 :s 60.0})
(defn trit [ds] (let [{:keys [a b s]} CUT
                      ps (logistic (* (- s) (- ds a))) pd (logistic (* s (- ds b)))
                      pm (max 1e-12 (- (logistic (* s (- ds a))) pd))]
                  (cond (and (>= ps pm) (>= ps pd)) -1 (>= pd pm) 1 :else 0)))

;; deterministic synthetic embeddings (sm64) to validate the format end-to-end
(def MIX1 (Long/parseUnsignedLong "BF58476D1CE4E5B9" 16))
(def MIX2 (Long/parseUnsignedLong "94D049BB133111EB" 16))
(def GOLD (Long/parseUnsignedLong "9E3779B97F4A7C15" 16))
(defn sm64 [s] (let [z (unchecked-add s GOLD)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) MIX1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) MIX2)]
    (bit-xor z (unsigned-bit-shift-right z 31))))
(defn vd [seed d] (mapv #(- (/ (Long/remainderUnsigned (sm64 (bit-xor seed %)) 100000) 100000.0) 0.5) (range d)))

(defn diff-readout [a b]
  ;; a,b = read-bin maps; per-tile change → f_A → trit
  (let [n (min (:n a) (:n b))]
    (for [i (range n)]
      (let [raw (cosdist (nth (:emb a) i) (nth (:emb b) i))]
        {:tile i :raw raw :f (f raw) :trit (trit (f raw))}))))

(let [arg (first *command-line-args*)]
  (if (= arg "diff")
    ;; diff two real .bin files: eo_trit.bb diff q1.bin q2.bin
    (let [[_ pa pb] *command-line-args*
          rows (diff-readout (read-bin pa) (read-bin pb))
          h (frequencies (map :trit rows))]
      (println (format "EO change over %d tiles: KEEP(+1)=%d MAYBE(0)=%d DISCARD(-1)=%d"
                       (count rows) (get h 1 0) (get h 0 0) (get h -1 0)))
      (doseq [r (take 5 (sort-by :raw > rows))]
        (println (format "  tile %2d raw=%.4f f=%.4f trit=%d" (:tile r) (:raw r) (:f r) (:trit r)))))
    ;; selftest: synth two windows, round-trip the EXACT format, run readout
    (let [d 192 n 16
          q1 (mapv #(vd (+ 1000 %) d) (range n))
          ;; q2: tiles 0-11 seasonal drift; 12-13 partial; 14-15 full flip
          q2 (mapv (fn [i] (let [base (nth q1 i)]
                             (cond (< i 12) (mapv #(+ %1 (* 0.05 %2)) base (vd (+ 5000 i) d))
                                   (< i 14) (mapv #(+ %1 (* 0.9 %2)) base (vd (+ 5000 i) d))
                                   :else (vd (+ 9000 i) d)))) (range n))
          coords (vec (repeat n [37.7301238 -122.4049352]))
          pa "/Volumes/Build/dietrich-offload/eo/_selftest_q1.bin"
          pb "/Volumes/Build/dietrich-offload/eo/_selftest_q2.bin"]
      (write-bin pa n d q1 coords) (write-bin pb n d q2 coords)
      (let [ra (read-bin pa) rb (read-bin pb)
            rt-ok (and (= (:n ra) n) (= (:d ra) d)
                       (< (Math/abs (- (ffirst (:emb ra)) (ffirst q1))) 1e-6))
            rows (diff-readout ra rb) h (frequencies (map :trit rows))]
        (println (format "format round-trip ok? %s  (N=%d D=%d)" rt-ok (:n ra) (:d ra)))
        (println (format "trits: KEEP(+1)=%d MAYBE(0)=%d DISCARD(-1)=%d  (planted 2/2/12)"
                         (get h 1 0) (get h 0 0) (get h -1 0)))
        (let [ok (and rt-ok (= 2 (get h 1 0)) (>= (get h -1 0) 10))]
          (println (if ok "Σ selftest GREEN — adapter ready for real OlmoEarth .bin" "RED — inspect"))
          (flush) (System/exit (if ok 0 1)))))))
