-- The language server `cambra --lsp` (`cambra-lsp/design-cambra-lsp.md`), for
-- Neovim 0.11's `vim.lsp.config`. `vim.lsp.enable('cambra')` starts it in
-- `cambra` buffers; `cambra` must be on PATH.
---@type vim.lsp.Config
return {
  cmd = { 'cambra', '--lsp' },
  filetypes = { 'cambra' },
}
