" Vim syntax file for CHL, the Cambra High-level Language.
"
" The keyword lists mirror `KEYWORDS` in chl-parser/src/lexer.rs and the
" builtin list mirrors `SURFACE_BUILTINS` in chl-parser/src/builtins.rs;
" tests/editor_grammars.rs fails when they differ. Each keyword class is one
" `syn keyword` line and the builtins are one `syn match` line, so that test can
" read them back.

if exists('b:current_syntax')
  finish
endif

syn case match

syn keyword cambraBoolean True False
syn keyword cambraKeywordControl if elif else for in return yield match case pass with
syn keyword cambraKeywordOther def where and or not

" Ordinary operators. Among matches starting at one column, Vim prefers the one
" defined last, so the mutation, feed and define operators below win over the
" `:`, `<` and `<=` prefixes matched here.
syn match cambraOperator "[-+*&|^=<>?]"
syn match cambraOperator "\*\*\|//=\=\|++\|\^[+=]\|[-+*]=\|[=!<>]=\|<:\|->\|=>"
syn match cambraPunctuation "[,;:.]"
syn match cambraMutation ":="
syn match cambraFeed "<<=\="

" A match rather than a keyword: a keyword outranks every match, and
" `cambraFunction` below has to win over a builtin name after `def`.
syn match cambraBuiltin "\<\%(sum\|max\|groupby\|set\|map\|box\|empty_map\|await_final\|defer\|begin\|http_serve\|test_sink\|stdin\)\>"

syn match cambraLambda "\\"
syn match cambraNumber "\<\d\+\>"
syn match cambraType "\<\u\w*\>"
" The type hole `_` directly after an annotation's `:`, `<:` or `=>`, or after
" the `{` that opens a type literal. A `=>` whose `=` ends an operator before
" it, as in `==>` or `<=>`, is not the arrow.
syn match cambraType "\%(\%([:{]\|\%(^\|[^=<>!:+*/^-]\)=>\)\s*\)\@<=\<_\>"
syn match cambraVariant "`\h\w*"
syn match cambraDecorator "@\s*\h\w*"
syn match cambraFunction "\%(\<def\s\+\)\@<=\h\w*"

syn match cambraEscape +\\[ntr0\\"']+ contained
" A string literal ends on its line, so an unterminated one stops at the line end.
syn region cambraString start=+"+ skip=+\\.+ end=+"+ end=+$+ contains=cambraEscape
syn region cambraString start=+'+ skip=+\\.+ end=+'+ end=+$+ contains=cambraEscape
syn keyword cambraTodo TODO FIXME XXX contained
syn match cambraComment "#.*$" contains=cambraTodo

hi def link cambraBoolean Boolean
hi def link cambraKeywordControl Statement
hi def link cambraKeywordOther Keyword
hi def link cambraOperator Operator
hi def link cambraPunctuation Delimiter
hi def link cambraMutation Special
hi def link cambraFeed Special
hi def link cambraLambda Special
hi def link cambraNumber Number
hi def link cambraType Type
hi def link cambraVariant Constant
hi def link cambraDecorator PreProc
hi def link cambraFunction Function
hi def link cambraBuiltin Function
hi def link cambraEscape SpecialChar
hi def link cambraString String
hi def link cambraComment Comment
hi def link cambraTodo Todo

let b:current_syntax = 'cambra'
