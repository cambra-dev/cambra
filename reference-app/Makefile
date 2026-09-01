COMPOSE ?= docker compose

.DEFAULT_GOAL := help

.PHONY: help up down logs ps test test-unit test-integration lint seed count clean

help: ## List targets
	@grep -hE '^[a-z-]+:.*##' $(MAKEFILE_LIST) | sed 's/:.*##/\t/' | expand -t24

up: ## Build and start the whole stack, then wait for it to be ready
	$(COMPOSE) up -d --build
	$(COMPOSE) run --rm --no-deps -T api python -m storefront.tools.wait_for_ready

down: ## Stop the stack and delete its volumes
	$(COMPOSE) down -v

ps: ## Show service status
	$(COMPOSE) ps

logs: ## Follow logs for every service
	$(COMPOSE) logs -f

seed: ## Re-run migrations, including the catalog seed
	$(COMPOSE) run --rm -T api alembic upgrade head

test: test-unit test-integration ## Run every test

test-unit: ## Run the unit tests (no services needed)
	$(COMPOSE) run --rm --no-deps -T api pytest tests/unit -q

test-integration: ## Run the end-to-end tests against the running stack
	$(COMPOSE) run --rm -T api pytest tests/integration -q

lint: ## Lint and format-check
	$(COMPOSE) run --rm --no-deps -T api ruff check .

count: ## Print the line-count table used in docs/REPORT.md
	python3 tools/count_loc.py

clean: down ## Stop everything and remove build artifacts
	rm -rf .pytest_cache **/__pycache__
