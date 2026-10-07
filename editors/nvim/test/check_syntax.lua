-- Checks the Vim syntax file against the lexer's highlight spans.
--
--   nvim --headless -u NONE -i NONE -n --cmd 'set rtp^=editors/nvim' \
--     -l editors/nvim/test/check_syntax.lua DUMP TABLE
--
-- DUMP is the JSON-lines output of `chl-parser`'s `dump_tokens` example and
-- TABLE is `editors/highlight-classes.json`. Paths inside DUMP resolve against
-- the working directory. Every byte of every span must resolve to the class's
-- expected group; see editors/README.md, "Editor highlight check". A span
-- that contains a newline byte fails the check.

local dump_path, table_path = arg[1], arg[2]
if not dump_path or not table_path then
  io.stderr:write("usage: check_syntax.lua DUMP TABLE\n")
  os.exit(2)
end

local function read(path)
  local f = assert(io.open(path, "rb"))
  local text = f:read("*a")
  f:close()
  return text
end

local expectations = vim.json.decode(read(table_path), { luanil = { object = true } })

local files, spans_by_file = {}, {}
for line in read(dump_path):gmatch("[^\n]+") do
  local span = vim.json.decode(line)
  if not spans_by_file[span.file] then
    spans_by_file[span.file] = {}
    table.insert(files, span.file)
  end
  table.insert(spans_by_file[span.file], span)
end

vim.cmd("filetype on")
vim.cmd("syntax on")

-- The group a colorscheme styles at a position: follow `hi link` from the
-- syntax item's own group until the name leaves the `cambra` namespace.
-- `synIDtrans` would follow the links further, into the default links among
-- the standard groups (`Boolean` and `Number` both end at `Constant`), which
-- loses the distinctions the table records. A `cambra` group with no link
-- stays as itself and fails the comparison.
local function group_at(line, col)
  local id = vim.fn.synID(line, col, 1)
  if id == 0 then
    return nil
  end
  local name = vim.fn.synIDattr(id, "name")
  while name:match("^cambra") do
    local link = vim.api.nvim_get_hl(0, { name = name, link = true }).link
    if not link then
      break
    end
    name = link
  end
  return name
end

local mismatches, checked = {}, 0
for _, file in ipairs(files) do
  vim.cmd("edit " .. vim.fn.fnameescape(file))
  assert(vim.bo.filetype == "cambra", file .. " did not get filetype cambra")
  -- Every position is computed from the top of the file, so no result
  -- depends on where Vim's default sync point falls.
  vim.cmd("syntax sync fromstart")
  local bytes = read(file)
  for _, span in ipairs(spans_by_file[file]) do
    local expectation = expectations[span.class]
    if not expectation then
      table.insert(
        mismatches,
        string.format("%s:%d:%d: class `%s` is not in %s", file, span.line, span.col, span.class, table_path)
      )
    else
      local expected = expectation.vim
      local got, seen = {}, {}
      for b = span.start, span["end"] - 1 do
        local line = vim.fn.byte2line(b + 1)
        local col = b + 1 - vim.fn.line2byte(line) + 1
        local newline = bytes:byte(b + 1) == 10
        local group = not newline and group_at(line, col) or nil
        if newline or group ~= expected then
          local shown = newline and "a newline" or group or "no group"
          if not seen[shown] then
            seen[shown] = true
            table.insert(got, shown)
          end
        end
      end
      checked = checked + 1
      if #got > 0 then
        table.insert(
          mismatches,
          string.format(
            "%s:%d:%d: %s is %s; Vim gave %s, expected %s",
            file,
            span.line,
            span.col,
            vim.json.encode(bytes:sub(span.start + 1, span["end"])),
            span.class,
            table.concat(got, ", "),
            expected or "no group"
          )
        )
      end
    end
  end
  vim.cmd("bwipeout")
end

for _, m in ipairs(mismatches) do
  io.stderr:write(m, "\n")
end
local summary = string.format("%d spans in %d files", checked, #files)
if checked == 0 then
  io.stderr:write(string.format("check_syntax: checked %s; %s holds no spans\n", summary, dump_path))
  os.exit(1)
end
if #mismatches > 0 then
  io.stderr:write(string.format("check_syntax: %d mismatches over %s\n", #mismatches, summary))
  os.exit(1)
end
io.stdout:write("check_syntax: Vim syntax agrees with the lexer over " .. summary .. "\n")
