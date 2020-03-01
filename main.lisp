;(ql:quickload 'ieee-floats)
#| Superlisp compiler services

A compiler infrastructure for compiling and executing lisp code on all platforms.
lisp interpreted + later type annotations

can be executed on top of a virtual machine or on bare metal.

There is a lisp (subset of scheme or something like that).
there is a compiler for this which emits webassembly code, the compiler itself can run on webassembly, because it is written in the same langue.

it is all based on a lisp port of wasmrun, because it would be too complicated to make c compile itself.

step 1: To be able to execute wasm code on lisp.
step 2: compiling lisp to wasm.
step 3: bootstrap
|#

(defpackage :awsm 
  (:use "COMMON-LISP" "SB-ALIEN"))

(in-package :awsm)

(defstruct byte-stream
  (bytes)
  (offset 0))

(defun byte-stream-read-byte (bs)
  (let* ((offset (byte-stream-offset bs))
	 (bytes (byte-stream-bytes bs))
	 (len (array-total-size bytes)))
    (if (< offset len)
	(let ((b (aref bytes offset)))
	  (incf (byte-stream-offset bs))
	  b)
      0)))

(defun read-byte2 (str &optional eof-error-p eof-value)
  (if (byte-stream-p str)
      (byte-stream-read-byte str)
    (cl:read-byte str eof-error-p eof-value)))


(defun load-wasm-reader(file)
  (let ((f (open file :direction :input :element-type 'unsigned-byte)))
    f))

(defun int-from-bytes (a b c d)
  (logior a (ash b 8) (ash c 16) (ash d 24)))

(defun read-uint(reader)
  (int-from-bytes (read-byte2 reader) (read-byte2 reader)(read-byte2 reader)(read-byte2 reader)))

(defun read-uint64(reader)
  (int-from-bytes (read-byte2 reader) (read-byte2 reader)(read-byte2 reader)(read-byte2 reader)
		  (read-byte2 reader) (read-byte2 reader)(read-byte2 reader)(read-byte2 reader)))


(defun read-uint-leb(reader)
  (let ((v 0)
	(shift 0))
    (loop while t do
	 (let* ((byte (read-byte2 reader))
		(value (logand #b01111111 byte)))
	   (setf v (logior (ash value shift) v))
	   (when (eq value byte)
	     (return v))
	   (incf shift 7)
	   ))))

(defun read-int-leb-part1(reader)
  (let* ((chunk (read-byte2 reader))
	 (value (logand #x7f chunk)))
    (if (< chunk 128)
	(values value 7 chunk)
	(multiple-value-bind (v s c)
	    (read-int-leb-part1 reader)
	  (values (logior (ash v 7) value) (+ s 7) chunk)))))

(defun read-int-leb (reader)
  (multiple-value-bind (v s c)
      (read-int-leb-part1 reader)
    (if (eq (logand c #x40) 0)
	v
	(logior v (ash -1 s)))))

(defun encode-uint-leb (value)
  (declare ((unsigned-byte 128) value))
  (let ((byte (logand #b01111111 value)))
    (if (eq byte value)
	(cons byte nil)
	(cons (logior #b10000000 byte) (encode-uint-leb-r (ash value -7))))))

(defun encode-int-leb(value)
  (declare (integer value))
  (let ((bits (logand #b01111111 value))
	(sign (logand #b01000000 value))
	(next (ash value -7)))
    (if (or (and (eq next 0) (eq sign 0)) (and (> sign 0) (eq next -1)))
	(cons bits nil)
	(cons (logior #b10000000 bits)
	      (encode-int-leb next))
	)))

(defun test-ileb-rt(value)
  (let ((bytes (encode-int-leb value)))
    (let ((rd (make-byte-stream :bytes (make-array (length bytes) :element-type '(unsigned-byte 8) :initial-contents bytes))))
      (read-int-leb rd))))

(defun test-uleb-rt(value)
  (let* ((bytes (encode-uint-leb value))
	 (rd (make-byte-stream :bytes (make-array (length bytes) :element-type '(unsigned-byte 8) :initial-contents bytes))))
    (read-uint-leb rd)))

;(defun read-f64(reader)
;  (let ((integer (read-uint64 reader)))
;    (ieee-floats:decode-float64 integer)))

;(defun read-f32(reader)
;  (let ((integer (read-uint reader)))
;    (ieee-floats:decode-float32 integer)))


(defun char-byte(char)
  (coerce (char-int char) 'unsigned-byte))

(defparameter *wasm-magic* (int-from-bytes 0 (char-int #\a) (char-int #\s) (char-int #\m)))
(defparameter *wasm-version* (int-from-bytes 1 0 0 0))


(defun awsm-read-header (reader)
  (let ((header (read-uint reader)))
    (assert (eq header *wasm-magic*) (reader) "stream does not contain the right header"))
  (let ((version (read-uint reader)))
    (unless (eq version *wasm-version*)
      (print "warning: unexpected wasm version")))
  (print "wasm OK! awsm!"))

(defvar *wasm-sections* #(custom type import function table memory global export start element code data))

(defun awsm-read-section(reader)
  (let ((c (read-byte2 reader)))
    (aref *wasm-sections* c)))

(defun awsm-register-type(id param-count return-count)
  (format t "type ~a ~a ~a~%" id param-count return-count))

(defun read-type-header (reader)
  (read-byte2 reader))

(defun read-name (reader)
  (let* ((l (read-uint-leb reader))
	 (buffer (make-array l :element-type '(unsigned-byte 8))))
    (loop for i from 0 below l do
	 (setf (aref buffer i) (read-byte2 reader)))
    (sb-ext:octets-to-string buffer :external-format :utf-8)))

(defvar *wasm-import-types* #(FUNC TABLE MEM GLOBAL))

(defun read-import-type (reader)
  (let ((code (read-byte2 reader)))
    (aref *wasm-import-types* code)))

(defun read-type (reader)
  (let ((byte (read-byte2 reader)))
    (case byte
      (#x40 'BLOCK-EMPTY)
      (#x7C 'F64)
      (#x7D 'F32)
      (#x7E 'I64)
      (#x7F 'I32)
      (otherwise (error "Invalid type"))
      )))
(defun read-bool (reader)
  (not (eq (read-byte2 reader) 0)))
      

(defun awsm-read-type-section(reader)
  (let ((l (read-uint-leb reader))
	(type-count (read-uint-leb reader)))
    (format t "type section length: ~a~%" l)
    (loop for x from 0 below type-count do
	 (let ((header (read-type-header reader)))
	   (assert (eq header #x60))
	   (let ((param-count (read-uint-leb reader)))
	     (format t "parms ~a~%" param-count)
	     (loop repeat param-count do
		  (read-byte2 reader))
	     (let ((return-count (read-uint-leb reader)))
	       (assert (< return-count 2))
	       (loop repeat return-count do
		    (read-byte2 reader))
	       (awsm-register-type x param-count return-count)))))))

(defvar *awsm-import-table* (make-hash-table :test 'equal))
(defvar *awsm-import-function* (list 'func))
(defvar *awsm-symbols* (make-hash-table :test 'equal))
(defvar *awsm-code* (make-hash-table))
(defvar *awsm-func-symbol* (list 'func))

(defun register-import-function(name)
  (setf (gethash name *awsm-import-table*) (cons name *awsm-import-function*)))

(defun awsm-read-import-section (reader)
  (let ((l (read-uint-leb reader))
	(import-count (read-uint-leb reader)))
    (loop for i from 0 below import-count do
	 (let ((module-name (read-name reader))
	       (name (read-name reader))
	       (type (read-import-type reader)))
	   (case type
	     (FUNC
	      (let ((type-index (read-uint-leb reader)))
		(register-import-function name)
		(print (list 'func name type-index))))
	     (TABLE
	      (let* ((elem-type (read-byte2 reader))
		     (has-max (read-bool reader))
		     (min (read-uint-leb reader))
		     (max (when has-max (read-uint-leb reader))))
		(print (list 'table name elem-type has-max min max))))
	     (MEM
	      (let* ((has-max (not (eq (read-byte2 reader) 0)))
		    (min (read-uint-leb reader))
		    (max (when has-max (read-uint-leb reader))))
		(print (list 'mem name has-max min max))))
	     (GLOBAL
	      (let ((type (read-type reader))
		    (mutable (read-bool reader)))
		(print (list 'global name type mutable)))))))))

(defun awsm-read-function-section (reader)
  (let ((length (read-uint-leb reader))
	(func-count (read-uint-leb reader)))
    (loop for i from 0 below func-count do
	 (let ((f (read-uint-leb reader)))
	   (print (list 'function-index f))))))

(defun awsm-read-memory-section (reader)
  (let ((length (read-uint-leb reader))
	(mem-count (read-uint-leb reader)))
    (loop for i from 0 below mem-count do
	 (let* ((has-max (read-bool reader))
		(min (read-uint-leb reader))
	       (max (when has-max (read-uint-leb reader))))
	   (print (list 'MEMORY min max))))))

(defun load-instr-file(instr-list)
  (with-open-file (f instr-list )
    (loop
       until (not (peek-char nil f nil))
       for line = (read-line f)
       collect
	 (let* ((offset (search "#" line))
		(line
		 (if offset (subseq line 0 offset) line))
		(space (search " 0x" line)))
	   (when space
	     (let ((name (subseq line 0 space))
		   (value (parse-integer (subseq line (+ space 3) ) :radix 16)))
	       (list (intern name) value )
	     ))))))

(let ((instrs (load-instr-file "instruction.list"))
      (_max -1))
  (loop for x in instrs
     when x
       do
       (setf _max (max _max (cadr x))))
  (defparameter *wasm-instr* (make-array (+ 1 _max) :initial-element nil))
  (defparameter *wasm-instr2* (make-hash-table))
  (loop for x in instrs
     when x
     do
       (setf (aref *wasm-instr* (cadr x)) (car x))
       (setf (gethash (car x) *wasm-instr2*) (cadr x))
       (let ((name (intern (concatenate 'string "INSTR_" (symbol-name (car x))))))
	 (eval `(defparameter ,name ,(cadr x))))
       ;(print x)
       )
       
  )

(defun instr-to-int (instr)
  (gethash instr *wasm-instr2*))

(defun integer-to-instr (integer)
  (aref *wasm-instr* integer))

(defun read-instr (reader)
  (integer-to-instr (read-byte2 reader)))

(defun awsm-read-global-section (reader)
  
  (let ((length (read-uint-leb reader))
	(global-count (read-uint-leb reader)))
    (loop for i from 0 below global-count do
	 (let ((val-type (read-byte2 reader))
	       (mut (read-byte2 reader))
	       (instr (read-instr reader)))
	   (case instr
	     (I32_CONST (format t "i32 const: ~a~%" (read-int-leb reader)))
	     (I64_CONST (format t "i64 const: ~a~%" (read-int-leb reader)))
	     (F32_CONST (format t "f32 const: ~a~%" (read-f32 reader)))
	     (F64_CONST (format t "f64 const: ~a~%" (read-f64 reader)))
	     (otherwise (error "Unsupported instr" instr)))
	   (assert (eq 'END (print (read-instr reader))))))))

(defun awsm-symbol-by-name(name)
  (gethash name *awsm-symbols*))


(defun awsm-register-function(name index etype)
  (setf (gethash name *awsm-symbols*) (cons index *awsm-func-symbol*)))

(defun awsm-read-export-section (reader)
  (let ((length (read-uint-leb reader))
	(export-count (read-uint-leb reader)))
    (loop for i from 0 below export-count do
	 (let ((name (read-name reader))
	       (etype (read-import-type reader)))
	   (case etype
	     (FUNC (let ((index (read-uint-leb reader)))
		     (awsm-register-function name index etype)
		     (format t "EXPORT FUNC ~a ~a~%" name index)))
	     (TABLE (error "not supported"))
	     (MEM (let ((index (read-uint-leb reader)))
		    ;;; only one in the current wasm.
		    (format t "EXPORT MEMORY ~a~%" name)))
	     (GLOBAL (let ((index (read-uint-leb reader)))
		       (format t "EXPORT GLOBAL ~a~%" name))))))))

(defun awsm-read-code-section (reader)
  (let ((length (read-uint-leb reader))
	(func-count (read-uint-leb reader)))
    (loop for i from 0 below func-count do
	 (let* ((code-size (read-uint-leb reader))
		(seq (make-array code-size :element-type 'unsigned-byte)))
	   (format t "skipping ~a Func Index: ~a ~a ~%" code-size i func-count)
	   (let ((code (read-sequence seq reader)))
	     (setf (gethash i *awsm-code*) seq))
	   ))))
(defun awsm-read-custom-section (reader)
  (let ((length (read-uint-leb reader)))
    (loop for j from 0 below length do
	 (read-byte2 reader))))

(defstruct awsm-func
  (type 0)
  (argcount 0)
  (retcount 0)
  (import nil))

(defstruct stack-frame
  (block 0)
  (label-offset 0)
  (stack-pos 0)
  (local-count 0)
  (return-count 0)
  (fn)
  (reader nil)
  )

(defstruct awsm-context
  (stack nil)
  (frames nil)
  (labels nil))

(defvar *awsm-stack* '())
(defvar *awsm-frame-stack* '())

(defun awsm-push(value)
  (setf *awsm-stack* (cons value *awsm-stack*)))
;(defun awsm-push-frame()
  
  
  

(defun awsm-execute-symbol (sym args)
  (destructuring-bind (index . export-type) sym
    (assert (eq export-type *awsm-func-symbol*))
    (let* ((actual-symbol-place (- index (hash-table-count *awsm-import-table*)))
	   (code (gethash actual-symbol-place *awsm-code*))
	   (s (make-byte-stream :bytes code)))
      (let ((f (read-uint-leb s)))
	
	(loop for i from 0 below f do
	      (let ((elem-cnt (read-uint-leb s))
		    (type (read-type s)))
		(loop for j from 0 below elem-cnt do
		     (awsm-push 0))))
	(print (list f code))))))

(defun awsm-exec-code(awsm -context steps)
  (let* ( ;(startcount steps)
	 (frame (car (awsm-context-frames awsm-context)))
	 (reader (stack-frame-reader frame)))
    (loop for step from 0 below steps
	 (let ((instr (read-instr reader)))
	   (case instr
	     ('NOP (error "NOT SUPPORTED"))
	     (otherwise (error "Unsupported opcode")))))))

	  
			       

	       
#| test |#

(defvar reader nil)
(when reader
  (close reader)
  (setf reader nil))

(defun go-test ()
  (setf reader (load-wasm-reader "./testlib.wasm"))
  (awsm-read-header reader)
  (let ((sec (awsm-read-section reader)))
    (assert (eq sec 'type)))
  
  (awsm-read-type-section reader)
  (let ((sec (awsm-read-section reader)))
    (assert (eq sec 'import)))
  (awsm-read-import-section reader)
  (let ((sec (awsm-read-section reader)))
    (assert (eq sec 'function)))
  (awsm-read-function-section reader)
  (let ((sec (awsm-read-section reader)))
    (assert (eq sec 'memory)))
  (awsm-read-memory-section reader)
  (let ((sec (awsm-read-section reader)))
    (assert (eq sec 'global)))
  (awsm-read-global-section reader)
  (let ((sec (awsm-read-section reader)))
    (assert (eq sec 'export)))
  (awsm-read-export-section reader)
  (let ((sec (awsm-read-section reader)))
    (assert (eq sec 'code)))
  (awsm-read-code-section reader)
  (let ((sec (awsm-read-section reader)))
    (assert (eq sec 'custom)))
  (awsm-read-custom-section reader)

  (make-byte-stream :bytes (vector (instr-to-int 'I32_CONST) '4))
  
;  (let ((sec (awsm-read-section reader)))
;    (assert (eq sec 'custom)))
  )

(defun encode-integer(value)
  (logior (ash value 2) 1))

(defvar emitf (lambda (x) ))
(defun emit(x)
  (funcall emitf x)
  )

(defun emit-instr(x)
 (format t "instr: ~a~%" x))

(defvar awsm-module nil)

(defvar fun-ids (make-hash-table))

(defun register-function (name-symbol id)
  (setf (gethash name-symbol fun-ids) id))  

(defun import-function (import-name symbol)
  (let ((id (awsm-get-function awsm-module import-name)))
    (register-function symbol id)))

(defun lookup-symbol (sym)
  (multiple-value-bind (v exists) (gethash sym fun-ids)
    (assert exists)
    v))

(defun compute-locals(args)
  (let ((table (make-hash-table)))
    (loop for x in args
	  for i from 0 do
	  (setf (gethash x table) i))
    table
    ))

;; thread static global for storing locals
(defvar *locals* nil)

(defun compile-lisp-inner(code)
  (cond
    ((null code) (error "cannot compile nil"))
    ((integerp code)
     (emit `(INSTR_I64_CONST (I64 ,code))))
    ((and (consp code) (eq 'if (car code)))
     (let ((test (cadr code))
	   (a (caddr code))
	   (b (cadddr code)))
       (compile-lisp-inner test)
       (emit `(INSTR_I64_CONST 3))
       (emit `(INSTR_I64_SHR_S))
       (emit '(INSTR_IF (valtype i64)))
       (compile-lisp-inner a)
       (emit '(INSTR_ELSE))
       (compile-lisp-inner b)
       (emit '(INSTR_END))
       ))
    ((and (consp code) (eq 'defun (car code)))
     (let* (( name-dr (cdr code))
	    ( args-dr (cdr name-dr))
	    ( body (cdr args-dr))
	    (name (car name-dr))
	    (name-str (symbol-name name))
	    (body-cnt (length body))
	    (args (car args-dr))
	    (locals-table (compute-locals args))
	    (_ (awsm-define-function awsm-module name-str (sb-sys:int-sap 0) 0 1 (length args)))
	    (__ (register-function name _))
	    (code (compile-lisp
		   (if (eq body-cnt 1) (car body) `(progn @,body) )
		   locals-table
		   ))
	    (byte-code (print(cons 0 (gen-byte-code code))))
	    (byte-code-buffer (make-array (length byte-code) :element-type '(unsigned-byte 8) :initial-contents byte-code))
	 
	    (f (awsm-define-function awsm-module name-str (sb-sys:vector-sap byte-code-buffer) (array-total-size byte-code-buffer) 1 (length args)))
	    )
       ;(print (list name code))
       ;(print byte-code)
       (register-function name f)
       (compile-lisp-inner `(quote ,name))))
    ((and (consp code) (eq (car code) 'quote))
     (let ((rest (cadr code)))
       (if (symbolp rest)
	   (emit `(INSTR_i64_CONST (symbol ,code)))
	 (error "Quotation not supported")))
     )
     
    ((consp code)
     (loop for l in (cdr code) do
	  (compile-lisp-inner l))
     (let ((symname (car code)))
       (emit `(INSTR_CALL (func ,symname)))
       ;(compile-lisp-inner (car code))
       )
     )
    ((and (symbolp code) (integerp (gethash code *locals*)))
     (emit `(INSTR_LOCAL_GET ,(gethash code *locals*)))
     )
    (t (error "Unsupported code"))

    )
  )

(defun compile-lisp(code &optional (locals (make-hash-table)))
  (let ((buffer ())
	(*locals* locals))
    (let ((emitf (lambda (x) (setf buffer (cons x buffer)))))
      (compile-lisp-inner code)
      (emit '(INSTR_END))
      )
    buffer))

(defvar symbol-map (make-hash-table))

(defun get-symbol(sym)
  (multiple-value-bind(symid exists) (gethash sym symbol-map)
    (if exists symid
	(let ((newsym (run-lisp '(new-symbol ))))
	  (setf (gethash sym symbol-map) (logior (ash (car newsym) 3) 4))
	  ))))

(defun gen-i64 (x)
  (assert (integerp x))
  (logior (ash x 3) 1))

(defun gen-byte-code (code)
  (let ((buffer '()))
    (loop for item in (reverse code) do
	 ;(print item)
	 (loop for part in item do
	      (cond ((symbolp part)
		     (setf buffer (cons (symbol-value part) buffer)))
		    ((integerp part)
		     (setf buffer (append (encode-int-leb part) buffer)))
		    ((and (consp part) (eq (car part) 'func))
		     (push (lookup-symbol (cadr part)) buffer))
		    ((and (consp part) (eq (car part) 'symbol))
		     (setf buffer (append (reverse (encode-int-leb (print (get-symbol (cadr part))))) buffer)))
		    ((and (consp part) (eq (car part) 'I64))
		     (setf buffer (append (reverse (encode-int-leb (gen-i64 (cadr part)))) buffer)))
		    ((and (consp part) (eq (car part) 'valtype) (eq (cadr part) 'i64))

		     (setf buffer (cons #x73 buffer)))
		    )))
	   
       (reverse buffer)))

(defun byte-vector (&rest args)
  (make-array (length args) :element-type '(unsigned-byte 8) :initial-contents args)) ;(list 0 INSTR_I64_CONST 15 INSTR_END))

;(defun test2()
(load-shared-object "../wasmrun/libawsm.so")
(define-alien-type awsm-module
    (struct _awsm-module))

(define-alien-type awsm-thread
    (struct _awsm-thread))

(define-alien-routine "awsm_load_module_from_file" (* awsm-module) (file c-string))
(define-alien-routine "awsm_define_function" int (mod (* awsm-module))
		      (name c-string) (data (* unsigned-char)) (len int) (retcnt int) (argcnt int))
(define-alien-routine "awsm_process" int (mod (* awsm-module)) (cnt int))
(define-alien-routine "awsm_get_function" int (module (* awsm-module)) (name c-string))
(define-alien-routine "awsm_load_thread" (* awsm-thread) (module (* awsm-module)) (symbol c-string))
(define-alien-routine "awsm_diagnostic" void (enabled boolean))
(define-alien-routine "awsm_thread_keep_alive" void (thread (* awsm-thread)) (keep-alive int))
(define-alien-routine "awsm_pop_i64" int (thread (* awsm-thread)))

(awsm-diagnostic t)

(setf awsm-module (awsm-load-module-from-file "awsmlib.wasm"))
(defvar addfun (byte-vector 0 INSTR_I64_ADD INSTR_END))
(defvar plus-add1 (awsm-get-function awsm-module "add1"))
(import-function "add1" '+)
(import-function "mkcons" 'cons-mk)
(import-function "init_cons" 'cons-init)
(import-function "car" 'car)
(import-function "cdr" 'cdr)
(import-function "new_symbol" 'new-symbol)

(defun run-lisp (lisp-code &optional (name "anon"))
  (let* (
	 (code (compile-lisp lisp-code))
	 (proto (cons 0 (gen-byte-code code)))
	 (buf (make-array (length proto) :element-type '(unsigned-byte 8) :initial-contents proto))
	 (f (awsm-define-function awsm-module name (sb-sys:vector-sap buf) (array-total-size buf) 1 0)))
    (let ((trd (awsm-load-thread awsm-module name)))

      (awsm-thread-keep-alive trd 1)
      (print code)
      (finish-output)
      (awsm-process awsm-module 10000)
      (let ((v (awsm-pop-i64 trd)))
	(awsm-thread-keep-alive trd 0)
	(let ((type-code (logand v #b00000111))
	      (value (ash v -3)))
	  (print (list type-code v))
	  (case type-code
	    (0 'nil)
	    (1 value)
	    (2 (list value 'f64))
	    (3 (list value 'cons))
	    (4 (list value 'symbol))
	    (otherwise (error "Unknown ~a ~a" type-code v))))))))


(defun test-leb()
  (loop for scale in '(1 10 100 1000 10000) do
       (loop for i upfrom (* scale -10) upto (* scale 10) by scale do
	    (assert (eq (run-lisp i) i))
	    )))

(print (run-lisp '(cons-init)))
;(print (run-lisp '(if 0 2 3)))
;(print (run-lisp '(defun xfunc () 5)))
;(print (run-lisp '(xfunc)))
;(print (run-lisp '(if 1 2 (xfunc))))
;(run-lisp '(defun rec-func (x) (if x 0 (rec-func (+ x 1)))))
(run-lisp '(defun xfunc2 (x) (+ 5 x)))
(print (run-lisp '(xfunc2 35)))

					;(run-lisp '(rec-func -5))


					;(print (run-lisp '(if 1 2 3)))
;(print cons-init)
;(print (ash (run-lisp '5) -2))
;(print (ash (run-lisp '(+ 1 (+ 3 (+ 4 5)))) -2))
;(print (ash (run-lisp '(cdr (car (cons (cons 3 5) 4)))) -2))
;(run-lisp '(new-symbol 10))
;(print (run-lisp '(+ 1 2)))
;(print (run-lisp '(+ (+ 2 3) (+ 1 0))))
;(print (run-lisp '1))
;(print (ash (run-lisp '(+ 1 3)) -2))
;(print (ash (run-lisp '(cons 1 3)) -2))
;(print (ash (run-lisp '(cons 1 3)) -2))
;)
