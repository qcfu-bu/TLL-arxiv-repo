;;; tll-mode.el --- major mode for tll -*- lexical-binding: t; -*-
(setq tll-types '("let" "in" "rew" "match" "as" "with" "end"
                  "if" "then" "else" "fork" "return"))
(setq tll-keywords '("of" "size"))
(setq tll-lambda '("fn" "ln" "fun" "val" "main"))
(setq tll-session '("open" "send" "recv" "close"))

(setq tll-pragma-start-regexp "\\(?:#\\)")
(setq tll-sorts-regexp "\\(?:\\_<U\\_>\\|\\_<L\\_>\\)")
(setq tll-types-regexp (regexp-opt tll-types 'symbols))
(setq tll-keywords-regexp (regexp-opt tll-keywords 'symbols))
(setq tll-lambda-regexp (regexp-opt tll-lambda 'symbols))
(setq tll-session-regexp (regexp-opt tll-session 'symbols))
(setq tll-quantifier-regexp "\\(?:∀\\|∃\\|⇑\\|⇓\\|•\\)")
(setq tll-magic-regexp "\\(?:bad_magic\\)")
(setq tll-infer-regexp "\\(?:infer_tm\\)")
(setq tll-check-regexp "\\(?:check_tm\\)")
(setq tll-assert-regexp "\\(?:assert_equal\\)")

(setq tll-font-lock-keywords
      `(("\\(\\<inductive\\>\\|\\<program\\>\\|\\<logical\\>\\|\\<data\\>\\|\\<def\\>\\)\s*\\([[:graph:]]*\\)"
         (1 font-lock-keyword-face)
         (2 font-lock-variable-name-face))
        (,tll-pragma-start-regexp . font-lock-keyword-face)
        (,tll-sorts-regexp . font-lock-constant-face)
        (,tll-types-regexp . font-lock-type-face)
        (,tll-keywords-regexp . font-lock-keyword-face)
        (,tll-lambda-regexp . font-lock-keyword-face)
        (,tll-session-regexp . font-lock-builtin-face)
        (,tll-quantifier-regexp . font-lock-constant-face)
        (,tll-magic-regexp . tuareg-font-lock-error-face)
        (,tll-infer-regexp . font-lock-string-face)
        (,tll-check-regexp . font-lock-warning-face)
        (,tll-assert-regexp . font-lock-doc-face)
        ))

(defvar tll-mode-syntax-table nil "syntax table for tll-mode")
(setq tll-mode-syntax-table
      (let ((st (make-syntax-table)))
        ;; comments
        (modify-syntax-entry ?/ ". 14nb" st)
        (modify-syntax-entry ?- ". 123" st)
        (modify-syntax-entry ?\n ">" st)

        ;; strings
        (modify-syntax-entry ?\" "\"" st)
        (modify-syntax-entry ?\' "\"" st)
        st))

;;;###autoload
(define-derived-mode tll-mode prog-mode
  "TLL"
  "Major mode for editing TLL"
  (setq font-lock-defaults '((tll-font-lock-keywords)))
  (set-syntax-table tll-mode-syntax-table)
  (setq-local comment-start "--")
  (setq-local comment-start-skip "--+[\t ]*")
  (setq-local comment-end "")
  (company-mode 1)
  (add-to-list 'company-backends 'company-math-symbols-unicode))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tll" . tll-mode))
(provide 'tll-mode)
