"""The warehouse-backed endpoint.

DuckDB is opened read-only per request. The ETL process is the only writer, and
a single-writer embedded warehouse is exactly what a Snowflake or BigQuery
connection would replace.
"""

import duckdb
from fastapi import APIRouter

from storefront.config import settings
from storefront.schemas import DailyRevenueResponse, DailyRevenueRow

router = APIRouter()

QUERY = """
    SELECT day, sku, revenue, units
    FROM daily_sku_revenue
    ORDER BY day, sku
"""


@router.get("/analytics/daily-revenue", response_model=DailyRevenueResponse)
async def daily_revenue() -> DailyRevenueResponse:
    try:
        conn = duckdb.connect(settings().warehouse_path, read_only=True)
    except duckdb.Error:
        # The warehouse has not been created yet, which is a state the endpoint
        # answers rather than an error: no loads have run.
        return DailyRevenueResponse(rows=[])
    try:
        rows = conn.execute(QUERY).fetchall()
    except duckdb.CatalogException:
        return DailyRevenueResponse(rows=[])
    finally:
        conn.close()
    return DailyRevenueResponse(
        rows=[
            DailyRevenueRow(day=str(d), sku=s, revenue=int(r), units=int(u))
            for d, s, r, u in rows
        ]
    )
