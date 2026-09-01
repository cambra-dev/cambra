"""Runs the SQL models against the warehouse, in filename order.

A model is a file that rebuilds one table. Ordering by name is the whole
dependency mechanism, which is the point at which a real project reaches for dbt
— `docs/REPORT.md` estimates what that would cost.
"""

from pathlib import Path

import duckdb

from storefront.platform.observability import logger

log = logger(__name__)
MODELS = Path(__file__).parent / "sql"


def run(conn: duckdb.DuckDBPyConnection) -> list[str]:
    applied = []
    for model in sorted(MODELS.glob("*.sql")):
        conn.execute(model.read_text())
        applied.append(model.stem)
    log.info("etl.transform", models=applied)
    return applied
