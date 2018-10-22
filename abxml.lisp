(in-package #:3b-dex)

;; https://android.googlesource.com/platform/frameworks/base/+/master/tools/aapt2/format/binary/
(defparameter *string-pool* nil)
(defparameter *xml-tree* nil)
(defparameter *type-spec* nil)
(defparameter *table-package-types* nil)
(defparameter *table-package-keys* nil)
(defparameter *sdk-version* 0)

(defmethod read-chunk-with-type (type hsize bsize stream)
  ;; hsize is header size - any already parsed octets
  ;; bsize is size of body
  (error "unknown type ~x" type)
  (file-position stream (+ (file-position stream) (+ hsize bsize)))
  (list type))

(defmethod read-chunk-with-type ((type (eql #x0000)) hsize bsize stream)
  (file-position stream (+ (file-position stream) (+ hsize bsize)))
  (list :null hsize bsize))

(defmethod read-chunk-with-type ((type (eql #x0001)) hsize bsize stream)
  (labels ((read-flags (stream)
             (let ((a (read-u32 stream))
                   (f nil))
               (when (logbitp 0 a) (push :sorted f))
               (when (logbitp 8 a) (push :utf8 f))
               f))
           (read-length16 ()
             ;; not sure if we can have more than (* 2 (expt 2 15))
             ;; characters or not?
             (let ((l (read-u16 stream)))
               (if (logbitp 15 l)
                   (dpb l (byte 15 16) (read-u16 stream))
                   l))
             #++(loop for i = (read-u16 stream)
                   sum (ldb (byte 15 0) i)
                   while (logbitp 15 i)))
           #++(read-length8 ()
             (error "don't know how to read utf8 string length")
             ;; not sure if this should only use 2 octets like 16bit
             ;; version does, or read multiple octets in some form...
             (loop for i = (read-u8 stream)
                   sum (ldb (byte 7 0) i)
                   while (logbitp 7 i)))
           (read-string16 ()
             (let* ((l (read-length16))
                    (octets (make-array (* l 2)
                                        :element-type '(unsigned-byte 8))))
               (read-sequence octets stream)
               (read-u16 stream) ;; zero termination
               (or (babel:octets-to-string octets :encoding :utf-16le
                                                  :errorp nil))))
           (read-string8 ()
             (error "utf8 not done yet")))
    (let ((string-count (read-u32 stream))
          (style-count (read-u32 stream))
          (flags (read-flags stream))
          (string-offset (read-u32 stream))
          (style-offset (read-u32 stream))
          (bstart (file-position stream))
          (strings))
      (file-position stream (+ (file-position stream) (* string-count 4)))
      (setf strings
            (loop repeat string-count
                  collect (if (member :utf8 flags)
                              (read-string8)
                              (read-string16))))
      (when (plusp style-count)
        (error "can't parse styled strings in string-pool yet"))
      (file-position stream (+ bstart bsize))
      (unless *string-pool*
        (setf *string-pool* strings))
      (list :string-pool :string strings :styles nil
                         :hsize hsize :bsize bsize))))

(defmethod read-chunk-with-type ((type (eql #x0002)) hsize bsize stream)
  #++(file-position stream (+ (file-position stream) (+ hsize bsize)))
  #++(list :table hsize bsize)
  (let ((package-count (read-u32 stream)))
    (declare (ignore package-count))
    (list* :table
           (loop for o = 0 then (+ o s)
                 for (c s) = (multiple-value-list
                              (%read-chunk stream :max-length (- bsize o)))
                 when c collect c
                   while (< (+ o s) bsize)))))

(defmethod read-chunk-with-type ((type (eql #x0003)) hsize bsize stream)
  #++(list :xml hsize bsize)
  (list* :xml (loop for o = 0 then (+ o s)
                    for (c s) = (multiple-value-list
                                 (%read-chunk stream :max-length (- bsize o)))
                    when c collect c
                      while (< (+ o s) bsize))))

(defun read-string-pool (s)
  (let ((a (read-u32 s)))
    (when (and (>= a 0) (/= a #.(1- (expt 2 32))))
      (if *string-pool* (elt *string-pool* a) a))))

(defun expand-restable-ref (i)
  (list :resource :package (ldb (byte 8 24) i)
                  :type (ldb (byte 8 16) i)
                  :entry (ldb (byte 16 0) i)))

(defun read-restable-ref (s)
  (expand-restable-ref (read-u32 s)))

(defun read-res-value (s)
  (let* ((size (read-u16 s))
         (r0 (read-u8 s))
         (tt (read-u8 s))
         (data (read-u32 s)))
    (declare (ignore size r0))
    (ecase tt
      (0 nil)
      (1 #++(list :resource data)
         (expand-restable-ref data))
      #++ (2 .. attribute resource identifier?)
      (3
       (when (and (not (minusp data)) (/= data #.(1- (expt 2 32))))
         (if (< data (length *string-pool*))
             (elt *string-pool* data)
             (list :string data))))
      (4 (ieee-floats:decode-float32 data))
      (5 (ecase data ;; possibly should store these as (:dimension :foo)?
           (0 :dimension :pixels)
           (1 :device-independent-pixels)
           (2 :scaled-device-independent-pixels)
           (3 :points)
           (4 :inches)
           (5 :mm)))
      (6 (ecase data
           (0 :unit-fraction)
           (1 :unit-fraction-parent)))
      (#x10 data) ;; 10 is dec, 11 is hex?
      (#x11 data) ;; 10 is dec, 11 is hex?
      (#x12 (ecase data
              (0 nil)
              (1 t) ; not sure if "true" is 1 or -1 or either?
              (#.(1- (expt 2 32)) t)))
      (#x1c (list :rgba8
                (ldb (byte 8 16) data)
                (ldb (byte 8 8) data)
                (ldb (byte 8 0) data)
                (ldb (byte 8 24) data)))
      (#x1d (list :rgb8
                (ldb (byte 8 16) data)
                (ldb (byte 8 8) data)
                (ldb (byte 8 0) data)))
      (#x1e (list :rgba4
                (ldb (byte 4 8) data)
                (ldb (byte 4 4) data)
                (ldb (byte 4 0) data)
                (ldb (byte 4 12) data)))
      (#x1f (list :rgb4
                (ldb (byte 4 8) data)
                (ldb (byte 4 4) data)
                (ldb (byte 4 0) data)))

      #++(t
       (list :encoded-data :type tt :data data)))))

(defmacro xml-start (name (stream) &body body)
  (declare (ignore name))
  (let ((line (gensym))
        (comment (gensym))
        (node (gensym)))
    `(let* ((,line (read-u32 ,stream))
            (,comment (read-string-pool ,stream))
            (,node (progn ,@body)))
       (when ,line
         (push (list :line ,line) (cadr ,node)))
       (when ,comment
         (push (list :comment ,comment) (cadr ,node)))
       (push ,node *xml-tree*)
       nil)))


(defmacro xml-end (name (stream) &body body)
  (declare (ignore name))
  (let ((attr (gensym))
        (line (gensym))
        (comment (gensym))
        (n (gensym)))
    `(let* ((,line (read-u32 ,stream))
            (,comment (read-string-pool ,stream))
            (,attr (progn ,@body))
            (,n (pop *xml-tree*)))
       ;; fixme: verify attr matches?
       (declare (ignore ,attr))
       #++(format t "n = ~s~%" ,n)
       #++(format t "tree = ~s~%" ,*xml-tree*)
       (if (assoc :line (cadr ,n))
           (setf (cadr (assoc :line (cadr ,n)))
                 (list (cadr (assoc :line (cadr ,n))) ,line))
           (push (list :line ,line) (cadr ,n)))
       (when ,comment
         (if (assoc :comment (cadr ,n))
             (setf (cadr (assoc :comment (cadr ,n)))
                   (list (cadr (assoc :comment (cadr ,n))) ,comment))
             (push (list :comment (list nil ,comment)) (cadr ,n))))
       (setf (cddr ,n)
             (reverse (caddr ,n)))
       (if *xml-tree*
           (progn (push ,n (caddar *xml-tree*)) nil)
           ,n))))

(defmethod read-chunk-with-type ((type (eql #x0100)) hsize bsize stream)
  (xml-start :xml-first-chunk/start-namespace (stream)
    (list :namespace (list (list :label (read-string-pool stream))
                           (list :uri (read-string-pool stream)))
          nil)))

(defmethod read-chunk-with-type ((type (eql #x0101)) hsize bsize stream)
  (xml-end :xml-end-namespace (stream)
    (list (read-string-pool stream) (read-string-pool stream))))

(defmethod read-chunk-with-type ((type (eql #x0102)) hsize bsize stream)
  (xml-start :xml-start-element (stream)
    (let* ((ns (read-string-pool stream))
           (name (read-string-pool stream))
           (attribute-offset (read-u16 stream))
           (attribute-size (read-u16 stream))
           (attribute-count (read-u16 stream))
           (id (read-u16 stream))
           (class (read-u16 stream))
           (style (read-u16 stream))
           (attributes nil))
      (assert (= attribute-offset 20))
      (assert (= attribute-size 20))
      (loop for i below attribute-count
            for ns = (read-string-pool stream)
            for name = (read-string-pool stream)
            for value-string = (read-string-pool stream)
            for value = (read-res-value stream)
            for ns-name = (if ns
                              (cons name ns)
                              name)
            do (push #++(list :ns (read-string-pool stream)
                           :name (read-string-pool stream)
                           :value-string (read-string-pool stream)
                           :value (read-res-value stream))
                     (if value-string
                         (list ns-name value :value-string value-string)
                         (list ns-name value))
                     attributes))
      (setf attributes (reverse attributes))
      (let ((orig attributes))
        (declare (ignorable orig))
        (when (< 0 id)
          ;; id = (elt orig id)
          (error "handle :id?"))
        (when (< 0 class)
          ;; id = (elt orig class)
          (error "handle :class?"))
        (when (< 0 style)
          ;; id = (elt orig style)
          (error "handle :style?")))
      (list (if ns (cons name ns) name)
            attributes
            nil))))

(defmethod read-chunk-with-type ((type (eql #x0103)) hsize bsize stream)
  #++(file-position stream (+ (file-position stream) (+ hsize bsize)))
  #++(list :xml-end-element hsize bsize)
  (xml-end :xml-end-element (stream)
    (list :ns (read-string-pool stream)
          :name (read-string-pool stream))))

(defmethod read-chunk-with-type ((type (eql #x0104)) hsize bsize stream)
  (file-position stream (+ (file-position stream) (+ hsize bsize)))
  (list :xml-cdata-element hsize bsize))

(defmethod read-chunk-with-type ((type (eql #x017f)) hsize bsize stream)
  (file-position stream (+ (file-position stream) (+ hsize bsize)))
  (list :xml-last-chunk hsize bsize))

(defmethod read-chunk-with-type ((type (eql #x0180)) hsize bsize stream)
  #++(file-position stream (+ (file-position stream) (+ hsize bsize)))
  #++(list :xml-resource-map hsize bsize)
  (list :xml-resource-map (loop for i below (/ bsize 4)
                                collect (read-u32 stream))))

(defmethod read-chunk-with-type ((type (eql #x017f)) hsize bsize stream)
  (file-position stream (+ (file-position stream) (+ hsize bsize)))
  (list :xml-last-chunk hsize bsize))


(defun get-string-from-table (table id)
  (let ((strings (getf (cdr table) :string)))
    (if (and strings
             (<= 0 id (length strings)))
        (elt strings id)
        id)))

(defmethod read-chunk-with-type ((type (eql #x0200)) hsize bsize stream)
  #++(file-position stream (+ (file-position stream) (+ hsize bsize)))
  #++(list :table-package hsize bsize)
  (let* ((id (read-u32 stream))
         (%name (read-ub8-vector 256 stream))
         (%name-end (search #(0 0) %name))
         (name (babel:octets-to-string %name
                                       :encoding :utf-16le
                                       :end (1+ %name-end)))
         (types-offset (read-u32 stream))
         (last-public-type (read-u32 stream))
         (keys-offset (read-u32 stream))
         (last-public-key (read-u32 stream))
         (start (file-position stream))
         (*table-package-types* (%read-chunk stream :max-length bsize))
         (*table-package-keys* (%read-chunk stream :max-length bsize))
         (*type-spec* nil))
    (declare (ignorable types-offset last-public-type
                        keys-offset last-public-key))
    (assert (plusp id) () "don't know how to handle table-package chunk that overrides another package (id=0)")
    (list* :table-package
           (list :id id :name name
                 :types *table-package-types* :keys *table-package-keys*)
           (loop with start-typespecs = (- (file-position stream) start)
                 for o = 0 then (+ o s)
                 for (c s) = (multiple-value-list
                              (%read-chunk stream :max-length (- bsize o)))
                 when c collect c
                   while (< (+ o s) (- bsize start-typespecs))))))

(defvar *config-enums*
  (flet ((e (&rest kv)
           (let ((fields nil))
             (setf
              kv
              (loop
                for (k v) on kv by #'cddr
                when (consp v)
                  do (push
                      (list k
                            (car v)
                            (alexandria:plist-hash-table (cdr v))
                            (alexandria:plist-hash-table (reverse (cdr v))))
                      fields)
                else
                  collect k and collect v))
             (list (alexandria:plist-hash-table kv)
                   (alexandria:plist-hash-table (reverse kv))
                   fields))))
    (alexandria:plist-hash-table
     (list :color-mode (e :hdr '(#xc
                                 :undefined 0
                                 :lowdr 4
                                 :highdr 8)
                          :undefined 0
                          :wide-gamut '(#x3
                                        :undefined 0
                                        :nowidecg 1
                                        :widecg 2))
           :density-dpi (e :undefined 0)
           :hard-keyboard-hidden (e :undefined 0
                                    :no 1
                                    :yes 2)
           :keyboard-hidden (e :undefined 0
                               :no 1
                               :yes 2)
           :keyboard (e :undefined 0
                        :nokeys 1
                        :qwerty 2
                        :12key 3)
           :navigation-hidden (e :undefined 0
                                 :no 1
                                 :yes 2)
           :navigation (e :undefined 0
                          :nonav 1
                          :dpad 2
                          :trackball 3
                          :wheel 4)
           :orientation (e :undefined 0
                           :portrait 1
                           :landscape 2
                           :square 3
                           :layoutdir '(#xc
                                        :undefined 0
                                        :ltr #x40
                                        :rtl #x80))
           :screen-layout (e :long '(#x30
                                     :undefined 0
                                     :no #x10
                                     :yes #x20)
                             :round '(#x300
                                      :undefined 0
                                      :no #x100
                                      :yes #x200)
                             :size '(#xf
                                     :undefined 0
                                     :small #x1
                                     :normal #x2
                                     :large #x3
                                     :xlarge 4))
           :touchscreen (e :finger 3
                           :notouch 1
                           :stylus 2
                           :undefined 0)
           :mode (e :night '(#x30
                             :undefined 0
                             :no #x10
                             :yes #x20)
                    :type '(#xf
                            :undefined 0
                            :normal 1
                            :desk 2
                            :car 3
                            :television 4
                            :appliance 5
                            :watch 6
                            :headset 7))))))


(defun decode-enum (v enum)
  (if (zerop v)
      nil
      (let ((tmp v))
        (destructuring-bind (w r fields) (gethash enum *config-enums*)
          (declare (ignore w))
          (let ((ff (when fields
                      (loop for (k mask nil kv) in fields
                            for masked = (logand mask tmp)
                            do (setf tmp (logand tmp (lognot mask)))
                            collect (list k (gethash masked kv))))))
            (list* (gethash tmp r) ff))))))

(defun read-config-enum/8 (s enum)
  (decode-enum (read-u8 s) enum))

(defun read-config-enum/16 (s enum)
  (decode-enum (read-u16 s) enum))

(defun encode-enum (v enum)
  (cond
    ((numberp v)
     v)
    ((null v)
     0)
    ((symbolp v)
     (gethash v (first (gethash enum *config-enums*))))
    (t
     (let ((tmp 0))
       (destructuring-bind (w r fields) (gethash enum *config-enums*)
         (declare (ignore r))
         (loop for x in v
               when (symbolp x)
                 do (setf tmp (logior tmp (gethash x w)))
               else
                 do (setf tmp (logior tmp
                                      (gethash (second x)
                                               (third
                                                (assoc (first x) fields))))))
         tmp)))))

(defun write-config-enum/8 (v s enum)
  (write-byte (encode-enum v enum) s))

(defun write-config-enum/16 (v s enum)
  (write-u16 (encode-enum v enum) s))


(defun read-table-type-config (s)
  (flet ((cc ()
           (let ((c (read-u16 s)))
             (when (plusp c)
               (coerce (list (code-char (ldb (byte 8 8) c))
                             (code-char (ldb (byte 8 0) c)))
                       'string)))))
    (let ((start (file-position s))
          (size (read-u32 s)))
      (prog1
          (loop
            for (k v)
              on (list :imsi-mcc (read-u16 s)
                       :imsi-mnc (read-u16 s)
                       :locale-lang (cc)
                       :locale-country (cc)
                       :screen-type-orientation
                       (read-config-enum/8 s :orientation)
                       :screen-type-touchscreen
                       (read-config-enum/8 s :touchscreen)
                       :screen-type-density (read-u16 s) ;; todo: decode enum
                       :input-keyboard (read-config-enum/8 s :keyboard)
                       :input-navigation (read-config-enum/8 s :navigation)
                       :input-flags (prog1 (read-u8 s) ;; todo: decode enum
                                      (read-u8 s))     ;; 0 padding
                       :screen-width (read-u16 s)
                       :screen-height (read-u16 s)
                       :sdk-version (prog1 (read-u16 s) ;; version
                                      (read-u16 s)) ; minor version == 0
                       :screen-config-layout (read-config-enum/8 s :screen-layout)
                       :screen-config-ui-mode (read-config-enum/8 s :mode)
                       :screen-config-smallest-screen-width-dp (read-u16 s)
                       :screen-width-dp (read-u16 s)
                       :screen-height-dp (read-u16 s))
            by #'cddr
            when (and v (not (zerop v))) collect k and collect v)
        (assert (= (file-position s) (+ size start)))))))


(defun read-table-type-entry (s)
  (let ((start (file-position s))
        (size (read-u16 s))
        (bflags (read-u16 s)) ;; bit 0=complex,bit 1=public
        (key (read-u32 s)) ;; index into 'packages'
        (flags ()))
    (when (logbitp 0 bflags)
      (push :complex flags))
    (when (logbitp 1 bflags)
      (push :public flags))
    (when (logbitp 2 bflags)
      (push :weak flags))

    (if (member :complex flags)
        ;; body is an array of restable-map
        (let* ((parent (read-restable-ref s))
               (count (read-u32 s))
               (map (loop for i below count
                          collect (list :name (read-restable-ref s)
                                        :value (read-res-value s)))))
          (list :entry :flags flags :key (get-string-from-table
                                          *table-package-keys* key)
                       :parent parent :values map))
        ;; body is single res-value
        (let ((v (read-res-value s)))
          (list :entry :flags flags
                       :key (get-string-from-table *table-package-keys* key)
                       :value v)))))

(defmethod read-chunk-with-type ((type (eql #x0201)) hsize bsize stream)
  #++(file-position stream (+ (file-position stream) (+ hsize bsize)))
  #++(list :table-type hsize bsize)
  (let* ((id (read-u8 stream))
         (r0 (read-u8 stream))
         (r1 (read-u16 stream))
         (count (read-u32 stream))
         (offset (read-u32 stream))
         (config (read-table-type-config stream))
         (entry-offsets (read-ub32-vector count stream)))
    (declare (ignore r0 r1 offset entry-offsets))
    (assert *type-spec*)
    ;; fixme: look up by ID instead of just pushing into most recent?
    (push
     (list* :table-type
            (list :id (get-string-from-table *table-package-types* (1- id)))
            (list :config config)
            (loop for i below count
                  collect (read-table-type-entry stream)))
     (cddr *type-spec*))
    nil))

(defmethod read-chunk-with-type ((type (eql #x0202)) hsize bsize stream)
  #++(file-position stream (+ (file-position stream) (+ hsize bsize)))
  #++(list :table-type-spec hsize bsize)
  (let* ((id (read-u8 stream))
         (r0 (read-u8 stream))
         (r1 (read-u16 stream))
         (count (read-u32 stream))
         ;; todo :decode bit flags
         (values (read-ub32-vector count stream)))
    (declare (ignore r0 r1))
    (when *type-spec*
      (setf (cddr *type-spec*)
            (reverse (cddr *type-spec*))))
    (setf *type-spec*
          (list :table-spec
                (list
                 :id (get-string-from-table *table-package-types* (1- id))
                 :values values)))))

(defun %read-chunk (seekable-stream &key (max-length (file-length seekable-stream)))
  (let* (#++(start (file-position seekable-stream))
         (type (read-u16 seekable-stream))
         (hsize (read-u16 seekable-stream))
         (size (read-u32 seekable-stream)))
    (assert (<= size max-length))
    (values (read-chunk-with-type type (- hsize 8) (- size hsize) seekable-stream)
            size)))

(defun read-chunk (seekable-stream &key (max-length (file-length seekable-stream)))
  (let ((*string-pool* nil)
        (*xml-tree* nil))
    (%read-chunk seekable-stream :max-length max-length)))

