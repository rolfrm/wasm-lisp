(asdf:defsystem :awsm
  :description "Lisp on WebAssembly."
  :author "Rolf Madsen <rolfrm@gmail.com>"
  :license  "MIT"
  :version "0.0.1"
  :serial t
  :components ((:file "package")
	       (:file "main" :depends-on ("package"))
	       ))
