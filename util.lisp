(in-package #:3b-dex)


(defparameter *read-endian* :le)

;; used to track state of .dex file being read/written, so we don't need
;; to pass the parts to every function that wants to look something up
;; (here instead of with the .dex file parser, since asm/disasm needs
;;  to look things up too)
(defvar *strings*)
(defvar *types*)
(defvar *prototypes*)
(defvar *fields*)
(defvar *methods*)



(defun ub8-vector (&key length contents (initial-element 0))
  (cond
    ((and length contents)
     (make-array length :element-type '(unsigned-byte 8)
                        :initial-contents contents))
    (length (make-array length :element-type '(unsigned-byte 8)
                               :initial-element initial-element))
    (contents (make-array (length contents) :element-type '(unsigned-byte 8)
                          :initial-contents contents))
    (t (error "must specify length or contents to UB8-VECTOR"))))

(defun ub16-vector (&key length contents (initial-element 0))
  (cond
    ((and length contents)
     (make-array length :element-type '(unsigned-byte 16)
                        :initial-contents contents))
    (length (make-array length :element-type '(unsigned-byte 16)
                               :initial-element initial-element))
    (contents (make-array (length contents) :element-type '(unsigned-byte 16)
                          :initial-contents contents))
    (t (error "must specify length or contents to UB16-VECTOR"))))

(defun ub32-vector (&key length contents (initial-element 0))
  (cond
    ((and length contents)
     (make-array length :element-type '(unsigned-byte 32)
                        :initial-contents contents))
    (length (make-array length :element-type '(unsigned-byte 32)
                               :initial-element initial-element))
    (contents (make-array (length contents) :element-type '(unsigned-byte 32)
                          :initial-contents contents))
    (t (error "must specify length or contents to UB32-VECTOR"))))
;;; readers assume (unsigned-byte 8) stream
;;; TODO: verify type of stream

(defun read-u8 (stream)
  (read-byte stream))

(defun read-s8 (stream)
  (let ((b (read-byte stream)))
    (if (< b 128)
        b
        (dpb b (byte 7 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 127 128 255))
  (loop for a = (ignore-errors (read-s8 s)) while a collect a))

(defun read-u16 (stream)
  (if (eq *read-endian* :le)
      (dpb (read-byte stream) (byte 8 0) (ash (read-byte stream) 8))
      (dpb (read-byte stream) (byte 8 8) (read-byte stream))))

(defun read-s16 (stream)
  (let ((b (read-u16 stream)))
    (if (< b 32768)
        b
        (dpb b (byte 15 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 127 128 255 254))
  (loop for a = (ignore-errors (read-s16 s)) while a collect a))


(defun read-u32 (stream)
  (if (eq *read-endian* :le)
      (logior (read-byte stream) (ash (read-byte stream) 8)
              (ash (read-byte stream) 16) (ash (read-byte stream) 24))
      (logior (ash (read-byte stream) 24) (ash (read-byte stream) 16)
              (ash (read-byte stream) 8) (read-byte stream))))

(defun read-s32 (stream)
  (let ((b (read-u32 stream)))
    (if (< b #.(expt 2 31))
        b
        (dpb b (byte 31 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 127 127 254 255 255 255))
  (loop for a = (ignore-errors (read-s32 s)) while a collect a))

(defun read-u64 (stream)
  (if (eq *read-endian* :le)
      (logior (read-byte stream) (ash (read-byte stream) 8)
              (ash (read-byte stream) 16) (ash (read-byte stream) 24)
              (ash (read-byte stream) 32) (ash (read-byte stream) 40)
              (ash (read-byte stream) 48) (ash (read-byte stream) 56))
      (logior (ash (read-byte stream) 56) (ash (read-byte stream) 48)
              (ash (read-byte stream) 40) (ash (read-byte stream) 32)
              (ash (read-byte stream) 24) (ash (read-byte stream) 16)
              (ash (read-byte stream) 8) (read-byte stream))))

(defun read-s64 (stream)
  (let ((b (read-u64 stream)))
    (if (< b #.(expt 2 63))
        b
        (dpb b (byte 63 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 127 127 254 255 255 255))
  (loop for a = (ignore-errors (read-s64 s)) while a collect a))


(defun read-ub8-vector (length stream)
  (let ((v (ub8-vector :length length)))
    (read-sequence v stream)
    v))

(defun read-ub16-vector (length stream)
  ;; not sure if it would be better to read to a temp ub8 vector then swap
  ;; or read by individual u16s
  (let ((v8 (read-ub8-vector (* 2 length) stream))
        (v (ub16-vector :length length)))
    (if (eq *read-endian* :le)
        (loop for i below length
              do (setf (aref v i) (dpb (aref v8 (1+ (* i 2))) (byte 8 8)
                                       (aref v8 (* i 2)))))
        (loop for i below length
              do (setf (aref v i) (dpb (aref v8 (* i 2)) (byte 8 8)
                                       (aref v8 (1+ (* i 2)))))))
    v))

(defun read-ub32-vector (length stream)
  ;; not sure if it would be better to read to a temp ub8 vector then swap
  ;; or read by individual u16s
  (let ((v8 (read-ub8-vector (* 4 length) stream))
        (v (ub32-vector :length length)))
    (if (eq *read-endian* :le)
        (loop for i below length
              do (setf (aref v i)
                       (logior (ash (aref v8 (+ 3 (* i 4))) 24)
                               (ash (aref v8 (+ 2 (* i 4))) 16)
                               (ash (aref v8 (+ 1 (* i 4))) 8)
                               (aref v8 (+ 0 (* i 4))))))
        (loop for i below length
              do (setf (aref v i)
                       (logior (ash (aref v8 (+ 0 (* i 4))) 24)
                               (ash (aref v8 (+ 1 (* i 4))) 16)
                               (ash (aref v8 (+ 2 (* i 4))) 8)
                               (aref v8 (+ 1 (* i 4)))))))
    v))

#++
(let ((*read-endian* :le))
  (flex:with-input-from-sequence (s #(#x1 #x0 #xff #xff))
    (read-ub16-vector 2 s)))

#++
(let ((*read-endian* :le))
  (flex:with-input-from-sequence (s #(#x1 #x0 #xff #xff))
    (read-ub32-vector 1 s)))

(defun read-zero-terminated (stream min-size)
  (let ((buf (make-array (max min-size 1) :element-type '(unsigned-byte 8)
                                  :fill-pointer min-size
                                  :adjustable t)))
    (read-sequence buf stream)
    (when (find 0 buf)
      (error "got unexpected 0 in mutf8 encoded string?"))
    (loop for b = (read-byte stream)
          while (plusp b)
          do (vector-push-extend b buf))
    buf))
