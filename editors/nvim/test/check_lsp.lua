-- Checks the language server through Neovim's client and `lsp/cambra.lua`.
--
--   nvim --headless -u NONE -i NONE -n --cmd 'set rtp^=editors/nvim' \
--     -l editors/nvim/test/check_lsp.lua CAMBRA
--
-- CAMBRA is the `cambra` binary to run as `CAMBRA --lsp`. The check opens a
-- `.cambra` file with two lex errors, the second after a `😀` on its line,
-- and requires: the client attaches with UTF-8 columns; both diagnostics
-- arrive at their byte columns; the outline lists the file's bindings and
-- function; the server's folds close the function body; and two edits clear
-- the diagnostics one at a time. `editors/vscode/test/lsp/suite.js` checks the
-- same file through VS Code, in UTF-16 columns (editors/README.md, "Language
-- server checks").

local cambra = arg[1]
if not cambra then
  io.stderr:write("usage: check_lsp.lua CAMBRA\n")
  os.exit(2)
end

local TIMEOUT = 10000
local failures, checked = {}, 0

local function check(ok, what)
  checked = checked + 1
  if not ok then
    table.insert(failures, what)
  end
  return ok
end

local function finish()
  for _, failure in ipairs(failures) do
    io.stderr:write(failure, "\n")
  end
  if #failures > 0 then
    io.stderr:write(string.format("check_lsp: %d of %d checks fail\n", #failures, checked))
    os.exit(1)
  end
  io.stdout:write(string.format("check_lsp: all %d checks pass\n", checked))
  os.exit(0)
end

local dir = vim.fn.tempname()
vim.fn.mkdir(dir, "p")
local path = dir .. "/check.cambra"
vim.fn.writefile({
  "x = f(1]",
  'y = "😀" $',
  "def g(a):",
  "    a",
}, path)

vim.cmd("filetype plugin indent on")
vim.lsp.config("cambra", { cmd = { cambra, "--lsp" } })
vim.lsp.enable("cambra")
vim.cmd.edit(path)
local buf = vim.api.nvim_get_current_buf()
vim.wo.foldmethod = "expr"
vim.wo.foldexpr = "v:lua.vim.lsp.foldexpr()"

local client
vim.wait(TIMEOUT, function()
  client = vim.lsp.get_clients({ bufnr = buf, name = "cambra" })[1]
  return client ~= nil and client.initialized
end, 20)
if not check(client ~= nil, "the cambra client did not attach to a `cambra` buffer") then
  finish()
end
check(client.offset_encoding == "utf-8", "the client uses " .. client.offset_encoding .. " columns, not utf-8")

-- Diagnostics as `{ line, col, message }`, sorted, with 0-based byte columns.
local function diagnostics()
  local out = {}
  for _, d in ipairs(vim.diagnostic.get(buf)) do
    table.insert(out, { d.lnum, d.col, d.message })
  end
  table.sort(out, function(a, b)
    return a[1] < b[1] or (a[1] == b[1] and a[2] < b[2])
  end)
  return out
end

local function wait_diagnostics(count, what)
  vim.wait(TIMEOUT, function()
    return #vim.diagnostic.get(buf) == count
  end, 20)
  return check(#vim.diagnostic.get(buf) == count, string.format("%s: %s", what, vim.inspect(diagnostics())))
end

if wait_diagnostics(2, "expected two diagnostics on opening") then
  local got = diagnostics()
  check(
    vim.deep_equal(got[1], { 0, 7, "`]` does not match `(`" }),
    "the mismatched `]` is not reported at 1:8: " .. vim.inspect(got[1])
  )
  -- `😀` is 4 bytes, so the `$` after it is at byte column 11.
  check(got[2][1] == 1 and got[2][2] == 11, "the `$` after `😀` is not reported at 2:12: " .. vim.inspect(got[2]))
end

local response = vim.lsp.buf_request_sync(
  buf,
  "textDocument/documentSymbol",
  { textDocument = vim.lsp.util.make_text_document_params(buf) },
  TIMEOUT
)
local names = {}
for _, symbol in ipairs((response and response[client.id] and response[client.id].result) or {}) do
  table.insert(names, symbol.name)
end
check(vim.deep_equal(names, { "x", "g" }), "the outline is not { x, g }: " .. vim.inspect(names))

-- The folds arrive after the first request for them; `foldclosed` reports
-- the fold's first line once `zc` can close it.
vim.wait(TIMEOUT, function()
  vim.cmd("silent! 4foldclose")
  return vim.fn.foldclosed(4) ~= -1
end, 50)
check(vim.fn.foldclosed(4) == 3, "the function body does not fold from line 3: foldclosed(4) = " .. vim.fn.foldclosed(4))
vim.cmd("silent! %foldopen!")

-- Replace `]` with `)`, then delete ` $` after the `😀`.
vim.api.nvim_buf_set_text(buf, 0, 7, 0, 8, { ")" })
wait_diagnostics(1, "fixing the bracket should leave one diagnostic")
vim.api.nvim_buf_set_text(buf, 1, 10, 1, 12, { "" })
wait_diagnostics(0, "deleting the `$` should leave no diagnostic")

vim.lsp.stop_client(client.id)
finish()
