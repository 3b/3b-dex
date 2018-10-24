(in-package #:3b-dex)

(defclass dex-class-method/w (dex-class-method)
  ((method-index :accessor method-index)
   (code-off :accessor code-off)))

(defun header-size (version)
  (assert (= 35 version))
  ;; == #x70
  (+ 8  ;; magic
     4  ;; checksum
     20 ;; hash
     (* 20 4)))

(defun simplified-signature (sig)
  (assert (char= #\( (char sig 0)))
  (loop with skip = nil
        for i from 1 below (length sig)
        for c = (char sig i)
        until (char= c #\))
        unless (or skip (char= c #\[))
          collect c into args
        when (char= c #\L)
          do (setf skip t)
        when (char= c #\;)
          do (setf skip nil)
        finally (incf i)
                (when (char= (char sig i) #\[)
                  (incf i))
                (return (list (format nil "~a~{~a~}" (char sig i)
                                      (reverse args))
                              (format nil "~a" (char sig i))))))

(defun write-u16 (x stream)
  (write-byte (ldb (byte 8 0) x) stream)
  (write-byte (ldb (byte 8 8) x) stream))

(defun write-u32 (x stream)
  (write-byte (ldb (byte 8 0) x) stream)
  (write-byte (ldb (byte 8 8) x) stream)
  (write-byte (ldb (byte 8 16) x) stream)
  (write-byte (ldb (byte 8 24) x) stream))

(defun write-uleb128 (x stream)
  ;; *leb128 are always 32bit in .dex
  (assert (<= (integer-length x) 32))
  (assert (not (minusp x)))
  (loop for p = (ldb (byte 7 0) x)
        do (setf x (ash x -7))
           (when (plusp x)
             (setf (ldb (byte 1 7) p) 1))
           (write-byte p stream)
        while (plusp x)))

#++
(loop repeat 1000000
      for i = (random (expt 2 32))
      for e = (flex:with-output-to-sequence (s)
                (write-uleb128 i s))
      for d = (flex:with-input-from-sequence (s e)
                (read-uleb128 s))
      do (assert (= d i)))

(defun write-header (version header stream)
  ;; todo: handle alignment
  (assert (zerop (mod (file-position stream) 4)))
  (write-sequence (dex-magic version) stream)
  (loop for k in `(:checksum :signature :file-size :header-size
                   :endian :link-size :link-off :map-off
                   :strings-size :strings-off
                   :types-size :types-off :prototypes-size :prototypes-off
                   :fields-size :fields-off :methods-size :methods-off
                   :classes-size :classes-off :data-size :data-off)
        for v = (getf header k)
        do (case k
             (:signature
              (if v
                  (assert (= 20 (length v)))
                  (setf v (make-array 20 :initial-element 0))))
             (:header-size
              (if v
                  (assert (= v (header-size version)))
                  (setf v (header-size version)))))
           (if (vectorp v)
               (write-sequence v stream)
               (write-u32 (or v 0) stream))))

;; no duplicates in any tables unless otherwise specified
;; strings must be sorted by utf16 code points
;; types, sorted by string ID index
;; prototypes, sorted by return-type type-id, then args type-ids
;; fields, sorted by defining type id, then name id, then value type id
;; methods, sorted by defining type id, name id, prototype id
;; classes, sorted with supertypes before subtypes
;; call-sites, sorted by offsets
;; method handles, unsorted, may contain dupes
;; data, ?
;; link data, ?

(defun extract-values-for-instruction (op &rest args)
  (let ((types (getf (gethash op *opcodes*) :types)))
    (loop for arg in args
          for i from 0
          for type = (nth i types)
          when (member type '(:string :type :array :class :method :field))
            collect type and collect arg)))

(defun extract-dex-tables (dex)
  (let ((strings (make-hash-table :test 'equal))
        (types  (make-hash-table :test 'equal))
        (methods (make-hash-table :test 'equal))
        ;; intern arglists as lists so we can intern prototypes with
        ;; equal since it compares vectors by identity
        (arglists (make-hash-table :test 'equal))
        (prototypes (make-hash-table :test 'equal))
        (fields (make-hash-table :test 'equal))
        (classes (make-hash-table :test 'equal))
        (field-index (make-hash-table :test 'equal)))
    (labels ((s (s)
               (when s
                 (or (gethash s strings)
                     (setf (gethash s strings) s))))
             (t (s)
               (when s
                 (or (gethash s types)
                     (setf (gethash s types) (s s)))))
             (al (a1)
               (unless a1
                 (setf a1 #()))
               (let ((a (map 'list #'t a1)))
                 (or (gethash a arglists)
                     (setf (gethash a arglists) (coerce a 'vector)))))
             (p (st rt args)
               (let ((p (list (s st) (t rt) (al args))))
                 (or (gethash p prototypes)
                     (setf (gethash p prototypes) p))))
             (m (type p n m)
               (let ((mm (list (t type)
                               (s n)
                               (apply #'p p)
                               m)))
                 (or (gethash mm methods)
                     (setf (gethash mm methods) mm))))
             (field* (ff)
               (or (gethash ff fields)
                   (setf (gethash ff fields) ff)))
             (c (code)
               (when code
                 (loop for i in (instructions code)
                       for v = (apply #'extract-values-for-instruction i)
                       when v
                         do (when (getf v :proto)
                              (apply #'p (getf v :proto)))
                            (when (getf v :method)
                              (apply #'m (getf v :method)))
                            (when (getf v :array)
                              (assert
                               (member (car i) '(:new-array :fill-array)))
                              (t (getf v :array)))
                            (when (getf v :field)
                              (let* ((vf (getf v :field))
                                     (ff (gethash vf field-index))
                                     (c (gethash (first vf) classes)))
                                (cond
                                  (ff
                                   (apply #'field ff))
                                  (c
                                   (field* (list c
                                                 (s (second vf))
                                                 (t (third vf))
                                                 nil)))
                                  (t
                                   (field* (list (t (first vf))
                                                 (s (second vf))
                                                 (t (third vf)) nil))))))
                            (when (getf v :class)
                              (t (getf v :class)))
                            (when (getf v :type)
                              (t (getf v :type)))
                            (s (getf v :string)))))
             (field (class f)
               ;; todo: annotations
               (let ((ff (list class
                               (s (name f))
                               (t (field-type f))
                               f)))
                 (field* ff)))
             (method (class m)
               ;; todo: annotations and parameter-annotations
               (let* ((short-type
                        (simplified-signature
                         (format nil "(~{~a~})~a"
                                 (coerce (parameters m) 'list)
                                 (return-type m))))
                      (p (p (first short-type) (return-type m)
                            (parameters m))))
                 (c (code m))
                 (m (type-name class) p (name m) m))))
      (loop for class across (classes dex)
            do (setf (gethash (type-name class) classes) class)
               (when (static-fields class)
                 (loop for f across (static-fields class)
                       do (setf (gethash (list (type-name class) (name f))
                                         field-index)
                                (list class f))))
               (when (instance-fields class)
                 (loop for f across (instance-fields class)
                       do (setf (gethash (list (type-name class) (name f))
                                         field-index)
                                (list class f)))))
      (loop for class across (classes dex)
            do (t (type-name class))
               (t (superclass class))
               (map nil #'t (interfaces class))
               (when (static-fields class)
                 (loop for f across (static-fields class)
                       do (field class f)))
               (when (instance-fields class)
                 (loop for f across (instance-fields class)
                       do (field class f)))
               (when (direct-methods class)
                 (loop for m across (direct-methods class)
                       do (method class m)))
               (when (virtual-methods class)
                 (loop for m across (virtual-methods class)
                       do (method class m)))))
    (list strings types methods prototypes fields)))

(defvar *id-sizes* '(:strings-size (4 4)
                     :types-size (4 4)
                     :prototypes-size (4 #x0c)
                     :fields-size (4 8)
                     :methods-size (4 8)
                     :classes-size (4 #x20)
                     :map-off (4 #x0c)
                     :type-list (4 0)))


(defvar *data-offset*)
(defvar *table-offset*)
(defvar *map-offset*)
(defvar *stream*)

(defun align-data (align)
  (when (zerop align) (setf align 1))
  (assert (<= *data-offset* (* align (ceiling *data-offset* align))))
  (setf *data-offset* (* align (ceiling *data-offset* align))))

(defun write-map (item count offset)
  (file-position *stream* *map-offset*)
  (write-u16 (getf *map-items* item) *stream*)
  (write-u16 0 *stream*)
  (write-u32 count *stream*)
  (write-u32 offset *stream*)
  (setf *map-offset* (file-position *stream*)))

(defun write-table-16 (d)
  (file-position *stream* *table-offset*)
  (incf *table-offset* 2)
  (write-u16 d *stream*))

(defun write-table-32 (d)
  (file-position *stream* *table-offset*)
  (incf *table-offset* 4)
  (write-u32 d *stream*))

(defmacro with-data ((&key align) &body body)
  `(progn
     ,@(when align `((align-data ,align)))
     (file-position *stream* *data-offset*)
     ,@body
     (setf *data-offset* (file-position *stream*))))

(defun sort-types-and-strings (types strings)
  (let ((sstrings (sort (alexandria:hash-table-keys strings) 'string<)))
    (loop for s in sstrings
          for i from 0
          do (setf (gethash s strings) i)))
  (let ((stypes (sort (alexandria:hash-table-keys types) '<
                      :key (lambda (a) (gethash a strings)))))
    (loop for s in stypes
          for i from 0
          do (setf (gethash s types) i))))

(defun lexical< (a b)
  (loop for i = (pop a)
        for j = (pop b)
        if (not j) ;; B is shorter or lists are equal
          return nil
        if (or (not i) (< i j)) ;; a is < or shorter
          return t
        if (< j i) ;; b is <
          return nil))


(defun make-type-list-< (types)
  (assert (not (gethash nil types)))
  (lambda (a b)
    (lexical< (map 'list (lambda (x) (gethash x types)) a)
              (map 'list (lambda (x) (gethash x types)) b))))

(defun write-type-list (h types)
  ;; not sure if these need sorted?
  (let ((type-lists (sort (alexandria:hash-table-keys h)
                          (make-type-list-< types))))
    (align-data 4)
    (write-map :type-list (hash-table-count h) *data-offset*)
    (loop for s in type-lists
          for i from 0
          do ;; type_list_item
             (with-data (:align 4)
               (setf (gethash s h) *data-offset*)
               (write-u32 (length s) *stream*)
               (loop for i across s
                     do (write-u16 (gethash i types) *stream*))))))

(defun write-strings (h)
  ;; fixme: should be sorted by encoded utf16 instead
  (let ((strings (sort (alexandria:hash-table-keys h) 'string<)))
    (write-map :string-data-item (hash-table-count h) *data-offset*)
    (loop for s in strings
          do (write-table-32 *data-offset*)
             ;; string_data_item
             (with-data ()
               (write-uleb128
                (/ (babel:string-size-in-octets s :encoding :utf-16)
                   2)
                *stream*)

               ;; fixme: use 'modified' utf8
               (write-sequence (babel:string-to-octets s :encoding :utf-8)
                               *stream*)
               (write-byte 0 *stream*)))))

(defun write-types (h strings)
  (let ((types (sort (alexandria:hash-table-keys h) '<
                     :key (lambda (a) (gethash a strings)))))
    (loop for s in types
          ;; type_id_item
          do (write-table-32 (gethash s strings)))))

(defun write-prototypes (h type-list strings types)
  (let ((prototypes (sort (alexandria:hash-table-keys h)
                          (make-type-list-< types)
                          :key (lambda (a)
                                 (list* (second a)
                                        (coerce (third a) 'list))))))
    (loop for s in prototypes
          for i from 0
          do (setf (gethash s h) i)
             ;; prototype_id_item
             (write-table-32 (gethash (first s) strings))
             (write-table-32 (gethash (second s) types))
             (if (third s)
                 (write-table-32 (gethash (third s) type-list))
                 (write-table-32 0)))))

(defun write-fields (h strings types)
  (let ((fields (sort (alexandria:hash-table-keys h) 'lexical<
                      :key (lambda (a)
                             (list (gethash (if (stringp (first a))
                                                (first a)
                                                (type-name (first a)))
                                            types)
                                   (gethash (second a) strings)
                                   (gethash (third a) types))))))
    (loop for s in fields
          for i from 0
          ;; field_id_item
          do (setf (gethash s h) i)
             (write-table-16 (gethash (if (stringp (first s))
                                          (first s)
                                          (type-name (first s)))
                                      types))
             (write-table-16 (gethash (third s) types))
             (write-table-32 (gethash (second s) strings)))))


(defun write-methods (h strings types prototypes fields)
  (let* ((methods (sort (alexandria:hash-table-keys h) 'lexical<
                        :key (lambda (a)
                               (list (gethash (first a) types)
                                     (gethash (second a) strings)
                                     (gethash (third a) types)))))
         (*strings* strings)
         (*methods* (alexandria:plist-hash-table
                     (loop for m in methods
                           for i from 0
                           collect (list (first m)
                                         (third m)
                                         (second m)
                                         (fourth m))
                           collect i)
                     :test 'equalp))
         (*fields* (alexandria:plist-hash-table
                    (loop for (c n type) being the hash-keys of fields
                            using (hash-value v)
                          collect (list (if (stringp c) c (type-name c))
                                        n type)
                          collect v)
                    :test 'equalp))
         (*types* types))
    (write-map :code-item (loop for s in methods
                                count (and (fourth s) (code (fourth s))))
               *data-offset*)
    (loop for s in methods
          for i from 0
          ;; method_id_item
          do (when (fourth s)
               (change-class (fourth s) 'dex-class-method/w)
               (setf (method-index (fourth s)) i))
             (write-table-16 (gethash (first s) types))
             (write-table-16 (gethash (third s) prototypes))
             (write-table-32 (gethash (second s) strings))
             (let ((code (and (fourth s) (code (fourth s)))))
               (setf (gethash s h) (if code *data-offset* 0))
               (align-data 4)
               (when (fourth s)
                 (setf (code-off (fourth s))
                       (if code *data-offset* 0)))
               (when code
                 (with-data (:align 4)
                   (when (tries code) (break "code ~s" code))
                   (write-u16 (registers code) *stream*)
                   (write-u16 (or (ins code) 0) *stream*)
                   (write-u16 (or (outs code) 0) *stream*)
                   (write-u16 (or (tries code) 0) *stream*)
                   (write-u32 0 *stream*) ;; todo: debug info
                   (let ((bytecode (assemble (instructions code))))
                     (write-u32 (length bytecode) *stream*)
                     (loop for i across bytecode
                           do (write-byte (ldb (byte 8 0) i) *stream*)
                              (write-byte (ldb (byte 8 8) i) *stream*)))))))))

(defun sort-classes (c)
  (let ((s nil)
        (done (make-hash-table))
        (index (make-hash-table :test 'equal)))
    (loop for i across c
          do (setf (gethash (type-name i) index) i)
          do (setf (gethash i index) i))
    ;; do we also need to sort outer classes before inner?
    (labels ((r (c)
               (setf c (gethash c index))
               (when (and c (not (gethash c done)))
                 (r (superclass c))
                 (map nil #'r (interfaces c))
                 (push c s)
                 (setf (gethash c done) t))))
      (map nil #'r c))
    (reverse s)))

(defvar *encoded-value-types*
  (alexandria:plist-hash-table '("Z" #x1f  ;; boolean
                                 "V" :void ;; probably not valid here
                                 "B" #x0   ;; signed byte
                                 "S" #x2   ;; signed short
                                 "C" #x3   ;; 'char' = unsigned short
                                 "I" #x4   ;; signed 32-bit int
                                 "J" #x6   ;; signed 64-bit long
                                 "F" #x10  ;; single-float
                                 "D" #x11  ;; double-float
                                 ;;"L" :? ;; class
                                 ;;"[..." #x1c ;; array of type ...
                                 :null #x1e)
                               :test 'equal))

(defun write-encoded-value (.type value)
  (let* ((type (if value
                   (gethash .type *encoded-value-types*)
                   (gethash :null *encoded-value-types*)))
         (arg (typecase value
                (integer
                 (1- (ceiling (integer-length value) 8)))
                (single-float
                 (setf value (encode-float32 value))
                 (1- (- 4
                        (loop for i below 4
                              while (zerop (ldb (byte 8 (* i 8)) value))
                              count 1))))
                (double-float
                 (setf value (encode-float64 value))
                 (1- (- 8
                        (loop for i below 8
                              while (zerop (ldb (byte 8 (* i 8)) value))
                              count 1))))
                ((member t nil)
                 0)
                (character
                 (let ((cc (babel:string-to-octets (string value)
                                                   :encoding :utf-16)))
                   (assert (= 1 (length cc)))
                   (aref cc 0)))
                (t 0))))
    (format t "write value ~s/~s ~s = ~2,'0x~%" .type value
            arg type)
    (when (eql type #x1f)
      (setf arg (if value 1 0)))
    (write-byte (dpb arg (byte 3 5) type) *stream*)

    (flet ((w (x)
             (loop for i below (1+ arg)
                   do (write-byte (ldb (byte 8 (* i 8)) x) *stream*))))
      ;; todo: range check ARG
      (case type
        (#x00 ;; signed byte arg should be 0
         (write-byte value *stream*))
        (#x02 ;; signed (16 bit) short
         (w value))
        (#x03 ;; (unsigned 16-bit) char
         (w value))
        (#x04 ;; signed (32 bit) int
         (w value))
        (#x06 ;; signed (64bit) long
         (w value))
        (#x10 ;; float32
         (w (ash value (* -8 value))))
        (#x11 ;; float64
         (w (ash value (* -8 value))))
        (#x15 ;; method type
         (error "todo: encoded value: method type"))
        (#x #x16 ;; method handle
         (error "todo: encoded value: method handle"))
        (#x17 ;; string
         (w value))
        (#x18 ;; type
         (w value))
        (#x19 ;; field
         (w value))
        (#x1a ;; method
         (w value))
        (#x1b ;; enum
         (w value))
        (#x1c ;; array
         (error "todo: write encoded array"))
        (#x1d ;; annotation
         (error "todo: annotation"))
        (#x1e ;; null
         nil)
        (#x1f ;; boolean
         nil)
        (t (error "invalid encoded_value? type = #x~2,'0x, arg = ~d" type arg))))))

(defun write-encoded-array (a)
  (write-uleb128 (length a) *stream*)
  (loop for (type value) in a
        do (write-encoded-value type value)))


(defun write-classes (a type-list strings types fields)
  (let ((classes (sort-classes a)))
    (align-data 1)
    (let ((encoded-array-items (make-hash-table)))
      (loop for c in classes
            for inits = (when (static-fields c)
                          (loop for s across (static-fields c)
                                when (slot-boundp s 'value)
                                  collect (list (field-type s) (value s))))
            when inits
              ;; todo: set defaults if only some are initialized?
              do (assert (= (length inits) (length (static-fields c))))
                 (setf (gethash c encoded-array-items)
                       inits))
      (write-map :encoded-array-item (hash-table-count encoded-array-items)
                 *data-offset*)
      (when (plusp (hash-table-count encoded-array-items))
        (with-data (:align 1)
          (loop for c in classes
                for i = (gethash c encoded-array-items)
                when i
                  do (setf (gethash c encoded-array-items)
                           (file-position *stream*))
                     (write-encoded-array i))))
      (write-map :class-data-item (length a) *data-offset*)
      (loop for c in classes
            ;; class_def_item
            do (write-table-32 (gethash (type-name c) types))
               (write-table-32 (encode-flags (flags c) *class-flags*))
               (write-table-32 (gethash (superclass c) types +no-index+))
               (write-table-32 (gethash (interfaces c) type-list 0))
               (write-table-32 (gethash (source-file c) strings +no-index+))
               (when (annotations c)
                 #++
                 (loop for a across (annotations c)
                       do (format t "skipping class annotation ~s:~% ~s~%"
                                  (annotation-type a)
                                  (alexandria:hash-table-plist
                                   (elements a)))))
               (write-table-32 0)             ;; todo: annotations
               (write-table-32 *data-offset*) ;; offset of class_data_item
               (with-data ()
                 (write-uleb128 (length (static-fields c)) *stream*)
                 (write-uleb128 (length (instance-fields c)) *stream*)
                 (write-uleb128 (length (direct-methods c)) *stream*)
                 (write-uleb128 (length (virtual-methods c)) *stream*)
                 (flet ((f (ff)
                          (when ff
                            (loop for f across ff
                                  for fn = (list c (name f) (field-type f) f)
                                  for i = (gethash fn fields)
                                    then (- (gethash fn fields) i)
                                  do (write-uleb128 i *stream*)
                                     (write-uleb128
                                      (encode-flags (flags f) *field-flags*)
                                      *stream*))))
                        (m (mm)
                          (loop for m across mm
                                for i = (method-index m)
                                  then (- (method-index m) i)
                                do (write-uleb128 i *stream*)
                                   (write-uleb128
                                    (encode-flags (flags m) *method-flags*)
                                    *stream*)
                                   (write-uleb128 (code-off m) *stream*))))

                   (f (static-fields c))
                   (f (instance-fields c))
                   (m (direct-methods c))
                   (m (virtual-methods c))))
               (write-table-32 (gethash c encoded-array-items 0))))))


(defun write-dex-file (dex stream)
  (assert (member (version dex) *supported-formats*))
  (let ((header (list :link-size 0
                      :link-off 0
                      :endian +dex-endian-constant+))
        (*data-offset* (header-size (version dex)))
        (*table-offset*)
        (*map-offset*)
        (*stream* stream)
        (map-count 0)
        (type-list (make-hash-table :test 'equal)))
    (destructuring-bind (strings types methods prototypes fields)
        (extract-dex-tables dex)
      (loop for (nil nil l) in (alexandria:hash-table-keys prototypes)
            when (and l (not (gethash l type-list)))
              do (setf (gethash l type-list) l))
      (loop for c across (classes dex)
            when (and (plusp (length (interfaces c)))
                      (not (gethash (interfaces c) type-list)))
              do (setf (gethash (interfaces c) type-list) (interfaces c)))

      (flet ((h (sk ok h)
               (let ((c (if (hash-table-p h)
                            (hash-table-count h)
                            h))
                     (size (second (getf *id-sizes* sk)))
                     (align (first (getf *id-sizes* sk))))
                 (setf (getf header sk) c)
                 (setf (getf header ok) *data-offset*)
                 (incf *data-offset* (* c size))
                 (incf map-count)
                 (align-data align))))
        ;; type-list section: N * (uint length of entry, + uint per
        ;;  type in entry)
        (h :type-list :type-list-off
           (+ (hash-table-count type-list)
              (reduce '+ (alexandria:hash-table-keys type-list)
                      :key 'length)))
        (h :strings-size :strings-off strings)
        (h :types-size :types-off types)
        (h :prototypes-size :prototypes-off prototypes)
        (h :fields-size :fields-off fields)
        (h :methods-size :methods-off methods)
        (h :classes-size :classes-off (length (classes dex)))
        (setf (getf header :data-off) *data-offset*))
      (incf map-count) ;; header
      ;; (incf map-count 3) ;; annotation set, directory, data
      (incf map-count) ;; code
      (incf map-count) ;; string data
      ;;(incf map-count) ;; debug info
      (incf map-count) ;; encoded arrays
      (incf map-count) ;; class data
      (incf map-count) ;; map-list
      (format t ":header = ~s~%" header)
      (write-header (version dex)
                    (list*
                     :map-off *data-offset*
                     header)
                    stream)
      (format t "file position = ~x~%" (file-position stream))
      (align-data 4)
      (format t "file position => ~x~%" (file-position stream))
      (setf *map-offset* *data-offset*)
      (incf *data-offset* (+ 4
                             (* map-count
                                (second (getf *id-sizes* :map-off)))))
      (file-position *stream* *map-offset*)
      (format t "map count ~s @ ~x~%" map-count (file-position stream))
      (write-u32 map-count *stream*)
      (let ((map *map-offset*))
        (incf *map-offset* 4)
        (write-map :header-item 1 0)
        (write-map :string-id-item (hash-table-count strings)
                   (getf header :strings-off))
        (write-map :type-id-item (hash-table-count types)
                   (getf header :types-off))
        (write-map :proto-id-item (hash-table-count prototypes)
                   (getf header :prototypes-off))
        (write-map :field-id-item (hash-table-count fields)
                   (getf header :fields-off))
        (write-map :method-id-item (hash-table-count methods)
                   (getf header :methods-off))
        (write-map :class-def-item (length (classes dex))
                   (getf header :classes-off))
        (write-map :map-list 1 map))
      (sort-types-and-strings types strings)

      (write-type-list type-list types)

      (let ((*table-offset* (getf header :strings-off)))
        (write-strings strings)
        (assert (= *table-offset* (getf header :types-off))))

      (let ((*table-offset* (getf header :types-off)))
        (write-types types strings)
        (assert (= *table-offset* (getf header :prototypes-off))))

      (let ((*table-offset* (getf header :prototypes-off)))
        (write-prototypes prototypes type-list strings types)
        (assert (= *table-offset* (getf header :fields-off))))

      (let ((*table-offset* (getf header :fields-off)))
        (write-fields fields strings types)
        (assert (= *table-offset* (getf header :methods-off))))

      (let ((*table-offset* (getf header :methods-off)))
        (write-methods methods strings types prototypes fields)
        (assert (= *table-offset* (getf header :classes-off))))

      (let ((*table-offset* (getf header :classes-off)))
        (write-classes (classes dex) type-list strings types fields)
        (assert (= *table-offset* (getf header :data-off))))

      ;; write call-site IDs
      ;; write method handles

      (format t "p = ~s / ~s~%" (file-position *stream*)
              *data-offset*)
      ;; fill in remainder of header
      (file-position *stream* 32) ;; file size
      (write-u32 *data-offset* *stream*)
      (file-position *stream* 104) ;; data size
      (write-u32 (- *data-offset* (getf header :data-off)) *stream*)
      (file-position *stream* 12)
      (let ((c (make-array (- *data-offset* 12)
                           :element-type '(unsigned-byte 8))))
        (read-sequence c *stream*)
        (file-position *stream* 8) ;; checksum
        (format t "checksum = ~8,'0x~%"
                (ironclad:digest-sequence 'ironclad:adler32 c))
        (write-sequence (reverse (ironclad:digest-sequence 'ironclad:adler32 c))
                        *stream*))
      (file-position *stream* *data-offset*))))

