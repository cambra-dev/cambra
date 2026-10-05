if vim.b.did_indent then
  return
end
vim.b.did_indent = 1

-- `line` with each string literal's contents and a trailing comment removed, so
-- that the brackets, `:` and `=` left are the code's own. One left-to-right
-- scan decides what is quoted: a quote opens a literal only outside one, the
-- literal closes at the next unescaped quote of the same kind, and a `#` starts
-- a comment only outside one. A literal closes on its own line
-- (`docs/chl-spec.md`, "1.7 Literals"), so one line is enough; an unterminated
-- one runs to the end of the line.
local function code_of(line)
  local out = {}
  local quote = nil
  local i = 1
  while i <= #line do
    local c = line:sub(i, i)
    if quote then
      if c == "\\" then
        i = i + 1
      elseif c == quote then
        table.insert(out, c)
        quote = nil
      end
    elseif c == "#" then
      break
    else
      table.insert(out, c)
      if c == '"' or c == "'" then
        quote = c
      end
    end
    i = i + 1
  end
  return table.concat(out)
end

-- Open brackets minus close brackets on `line`.
local function bracket_balance(line)
  local code = code_of(line)
  local _, opens = code:gsub("[%(%[{]", "")
  local _, closes = code:gsub("[%)%]}]", "")
  return opens - closes
end

-- The first line of the logical line that ends on line `lnum`: a line that
-- closes more brackets than it opens continues one that opened them.
local function logical_start(lnum)
  local start = lnum
  local depth = bracket_balance(vim.fn.getline(lnum))
  while depth < 0 do
    local prev = vim.fn.prevnonblank(start - 1)
    if prev == 0 then
      break
    end
    start = prev
    depth = depth + bracket_balance(vim.fn.getline(start))
  end
  return start
end

-- The indent for line `lnum` (default `v:lnum`), from the logical line before
-- it:
--
-- - inside an unclosed bracket, the previous line's indent;
-- - after a header ending in `:`, one level past the header's first line; two
--   levels when the header is an `if` on the right of an assignment, whose
--   `elif`/`else` chain sits one level in and whose bodies sit one further
--   (`docs/chl-spec.md`, "4.3 Assignment forms");
-- - after a `return` or `pass`, one level less;
-- - otherwise, the logical line's indent.
function _G.cambra_indent(lnum)
  local prev = vim.fn.prevnonblank((lnum or vim.v.lnum) - 1)
  if prev == 0 then
    return 0
  end
  local start = logical_start(prev)
  local open = 0
  for l = start, prev do
    open = open + bracket_balance(vim.fn.getline(l))
  end
  if open > 0 then
    return vim.fn.indent(prev)
  end
  local base = vim.fn.indent(start)
  local sw = vim.fn.shiftwidth()
  local first = code_of(vim.fn.getline(start))
  if code_of(vim.fn.getline(prev)):match(":%s*$") then
    if first:match("=%s*if%f[^%w_]") then
      return base + 2 * sw
    end
    return base + sw
  end
  if first:match("^%s*return%f[^%w_]") or first:match("^%s*pass%s*$") then
    return math.max(base - sw, 0)
  end
  return base
end

vim.bo.indentexpr = "v:lua.cambra_indent()"
-- Reindent only on a new line or an explicit request. The default set also
-- reindents on typing `:`, which would undo a manual dedent of `else:`.
vim.bo.indentkeys = "!^F,o,O"

vim.b.undo_indent = "setlocal indentexpr< indentkeys<"
