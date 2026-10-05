-- Checks the Neovim indent plugin against the shared indentation cases.
--
--   nvim --headless -u NONE -i NONE -n --cmd 'set rtp^=editors/nvim' \
--     -l editors/nvim/test/check_indent.lua CASES
--
-- CASES is `editors/indent-cases.json`. For each case the buffer holds the
-- case's lines and one empty line after them, and `cambra_indent` computes the
-- empty line's indent, as it does when Enter or `o` opens that line. A case
-- whose `expected_failures` names `nvim` must get a different indent; see
-- editors/README.md, "Indentation tests".

local cases_path = arg[1]
if not cases_path then
  io.stderr:write("usage: check_indent.lua CASES\n")
  os.exit(2)
end

local f = assert(io.open(cases_path, "rb"))
local cases = vim.json.decode(f:read("*a")).cases
f:close()

vim.cmd("filetype plugin indent on")
vim.cmd("enew")
vim.bo.filetype = "cambra"
assert(vim.bo.indentexpr == "v:lua.cambra_indent()", "the cambra indent plugin did not load")

local failures, checked = {}, 0
for _, case in ipairs(cases) do
  local lines = vim.list_extend(vim.deepcopy(case.lines), { "" })
  vim.api.nvim_buf_set_lines(0, 0, -1, false, lines)
  local got = _G.cambra_indent(#lines)
  local known = case.expected_failures and case.expected_failures.nvim
  if known and got == case.indent then
    table.insert(failures, string.format("%s: now indents %d as expected; remove its `nvim` expected failure", case.name, got))
  elseif not known and got ~= case.indent then
    table.insert(failures, string.format("%s: indents %d, expected %d", case.name, got, case.indent))
  end
  checked = checked + 1
end

for _, failure in ipairs(failures) do
  io.stderr:write(failure, "\n")
end
if checked == 0 then
  io.stderr:write("check_indent: " .. cases_path .. " holds no case\n")
  os.exit(1)
end
if #failures > 0 then
  io.stderr:write(string.format("check_indent: %d of %d cases fail\n", #failures, checked))
  os.exit(1)
end
io.stdout:write(string.format("check_indent: Neovim indents all %d cases as expected\n", checked))
