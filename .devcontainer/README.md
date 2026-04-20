# Dev Container

A sandboxed development environment with Rust toolchain, Claude Code CLI, and a network firewall that restricts outbound traffic to approved sources.

## Prerequisites

- Docker
- VS Code with the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) extension

## Usage

Open this repo in VS Code and select **Dev Containers: Reopen in Container** from the command palette.

## Platform Notes

### macOS

Credentials are stored in the macOS Keychain by Claude Code. The `extract-token.sh` script reads the token from Keychain automatically when the container starts — you may be prompted to allow Keychain access on the first rebuild.

**Prerequisite:** Run `claude auth login` on the host at least once before building the container. To switch accounts, log in with a different account on the host and rebuild.

### Linux / WSL

Claude Code stores credentials in `~/.claude/.credentials.json`, which is bind-mounted directly into the container. No extra setup is needed — authenticate inside the container with `claude auth login` after it starts.

## Network Firewall

The container runs an `iptables`-based firewall that restricts outbound traffic to:

- GitHub (source IP ranges via the GitHub meta API)
- `api.anthropic.com`, `claude.ai`, `claude.com`
- `registry.npmjs.org`
- `static.crates.io`, `index.crates.io`, `static.rust-lang.org`
- VS Code marketplace and update servers
- Statsig and Sentry (Claude Code telemetry)

All other outbound traffic is blocked. If a build or tool fails with a network error, the domain it needs may not be in the allowlist — add it to the `init-firewall.sh` domain list.
